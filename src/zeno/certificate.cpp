#include <zeno/certificate.hpp>

#include <zeno/forest.hpp>
#include <zeno/ns.hpp>
#include <zeno/ns_search.hpp>
#include <zeno/roles.hpp>
#include <zeno/one_plane.hpp>
#include <zeno/reduce.hpp>

#include <algorithm>
#include <istream>
#include <optional>
#include <ostream>
#include <sstream>
#include <stdexcept>

namespace zeno
{
namespace
{
std::size_t at(int v) { return static_cast<std::size_t>(v); }

/// Lower bounds at the levels of an instance, sharing tables that cover every
/// level below a point of makespan <= maxMakespan. A plan of makespan M <
/// nextMakespan has every load within level(nextMakespan) (in level units).
class LevelBounds
{
public:
    LevelBounds(const Instance& instance, Time maxMakespan)
        : instance_(instance)
        , r(reduce(instance))
        , maxLevel_(std::max<Time>(level(maxMakespan), 0))
        , low_(r.low, r.c, r.maxGroup(), maxLevel_)
        , fill_(r.fill, r.c, r.maxGroup(), maxLevel_)
        , roles_(r, maxLevel_) {}
    LevelBounds(const LevelBounds&) = delete;
    LevelBounds& operator=(const LevelBounds&) = delete;

    [[nodiscard]] Time level(Time nextMakespan) const { return (nextMakespan - 1) / r.makespanPerLevel; }

    Cost relaxed(Time T) const { return T < 0 ? kInfCost : relaxedCost(r, low_, checked(T)); }
    Cost forest(Time T) const { return T < 0 ? kInfCost : forestCost(r, fill_, checked(T), r.maxTree()); }
    Cost roles(Time T) const { return T < 0 ? kInfCost : roles_.bound(checked(T)); }
    /// Multipliers per original city.
    Cost lagrangian(Time T, const std::vector<Cost>& original) const
    {
        if(T < 0)
            return kInfCost;
        std::vector<Cost> mu;
        for(int i : r.original)
            mu.push_back(original[at(i)]);
        return lagrangianValue(r, checked(T), mu);
    }
    /// The exact balanced bound, or nothing when the program gives up.
    std::optional<Cost> balanced(Time T, Cost target) const
    {
        if(T < 0)
            return kInfCost;
        const auto remaining = remainingPlanesBound(r, roles_, checked(T));
        const BalancedRoles program(r, fill_, T, 2'000'000, 50'000'000, target, &remaining);
        if(!program.complete())
            return std::nullopt;
        return program.value();
    }

    /// The exhaustive search closes the region: no configuration of cost <
    /// costBelow finishes before makespanBelow. Nothing when it gives up.
    std::optional<bool> search(Time T, Cost costBelow, Time makespanBelow) const
    {
        if(T < 0)
            return true;
        const GapSearch g = searchGap(instance_, r, fill_, roles_, checked(T), costBelow, makespanBelow);
        if(g.outcome == GapSearch::Outcome::Incomplete)
            return std::nullopt;
        return g.outcome == GapSearch::Outcome::Closed;
    }

    const Instance& instance_;
    const ReducedInstance r;

private:
    Time checked(Time T) const
    {
        if(T > maxLevel_)
            throw std::logic_error("LevelBounds: level outside the table");
        return T;
    }
    Time maxLevel_;
    OnePlaneTable low_, fill_;
    RoleRelaxation roles_;
};

const char* kindName(GapBound kind)
{
    switch(kind)
    {
        case GapBound::Relaxed: return "relaxed";
        case GapBound::Forest: return "forest";
        case GapBound::Roles: return "roles";
        case GapBound::Lagrangian: return "lagrangian";
        case GapBound::Balanced: return "balanced";
        case GapBound::Search: return "search";
        case GapBound::Closed: return "closed";
    }
    return "?";
}

std::optional<GapBound> kindFromName(const std::string& name)
{
    for(GapBound k : {GapBound::Relaxed, GapBound::Forest, GapBound::Roles, GapBound::Lagrangian, GapBound::Balanced, GapBound::Search, GapBound::Closed})
        if(name == kindName(k))
            return k;
    return std::nullopt;
}

/// Tokenised lines without comments or blank lines, with their numbers.
class Lines
{
public:
    explicit Lines(std::istream& in)
    {
        int number = 0;
        for(std::string line; std::getline(in, line);)
        {
            ++number;
            std::istringstream words(line);
            std::vector<std::string> tokens;
            for(std::string w; words >> w;)
                tokens.push_back(w);
            if(tokens.empty() || tokens.front().starts_with('#'))
                continue;
            lines_.push_back({number, std::move(tokens)});
        }
    }

    const std::vector<std::string>& next(const std::string& keyword, std::size_t arity)
    {
        if(pos_ >= lines_.size())
            throw std::runtime_error("certificate: unexpected end of file, expected '" + keyword + "'");
        const auto& [number, tokens] = lines_[pos_++];
        line_ = number;
        if(!keyword.empty() && tokens.front() != keyword)
            fail("expected '" + keyword + "', found '" + tokens.front() + "'");
        if(arity != kAny && tokens.size() != arity)
            fail("expected " + std::to_string(arity) + " tokens");
        return tokens;
    }

    [[noreturn]] void fail(const std::string& why) const
    {
        throw std::runtime_error("certificate, line " + std::to_string(line_) + ": " + why);
    }

    std::int64_t number(const std::string& token) const
    {
        std::size_t used = 0;
        long long v = -1;
        try
        {
            v = std::stoll(token, &used);
        }
        catch(const std::exception&)
        {
            used = 0;
        }
        if(used != token.size() || v < 0)
            fail("expected a non-negative integer, found '" + token + "'");
        if(v > kMaxValue)
            fail("value " + token + " exceeds the limit 2^36 of this reader");
        return v;
    }

    std::int64_t signedNumber(const std::string& token) const
    {
        if(!token.empty() && token.front() == '-')
            return -number(token.substr(1));
        return number(token);
    }

    bool done() const { return pos_ >= lines_.size(); }

    static constexpr std::size_t kAny = static_cast<std::size_t>(-1);
    /// Limits of this reader: they keep every sum of the checker far from
    /// overflow (at most 10^7 legs of values below 2^36).
    static constexpr std::int64_t kMaxValue = std::int64_t{1} << 36;
    static constexpr std::int64_t kMaxCount = 100'000;
    static constexpr std::int64_t kMaxLegs = 10'000'000;

private:
    std::vector<std::pair<int, std::vector<std::string>>> lines_;
    std::size_t pos_ = 0;
    int line_ = 0;
};
} // namespace

Certificate makeCertificate(const Instance& instance, const SolveResult& result)
{
    if(result.plans.size() != result.front.size())
        throw std::invalid_argument("makeCertificate: the result has no plans (SolveOptions::plans)");
    Certificate cert;
    cert.instance = instance;
    cert.front = result.front;
    cert.plans = result.plans;
    const LevelBounds bounds(instance, result.front.empty() ? 0 : result.front.back().makespan);
    bool needsA1 = false;
    for(std::size_t i = 0; i + 1 < cert.front.size(); ++i)
    {
        const Time T = bounds.level(cert.front[i + 1].makespan);
        const bool relaxedEnough = bounds.relaxed(T) >= cert.front[i].cost;
        cert.gaps.push_back(relaxedEnough ? GapBound::Relaxed : GapBound::Forest);
        needsA1 = needsA1 || !relaxedEnough;
    }
    cert.assumptions = {"S"};
    if(needsA1)
        cert.assumptions.push_back("A1");
    return cert;
}

Certificate makeBracketCertificate(const Instance& instance, const BracketResult& result)
{
    if(!result.exact())
        throw std::invalid_argument("the front is not exact: some gaps are open, so there is no certificate");
    if(result.plans.size() != result.upper.size())
        throw std::invalid_argument("makeBracketCertificate: the result has no plans (SolveOptions::plans)");
    Certificate cert;
    cert.version = 2;
    cert.instance = instance;
    cert.front = result.upper;
    cert.plans = result.plans;
    const ReducedInstance r = reduce(instance);
    bool needsA1 = false;
    const auto kind = [&](GapProof proof) {
        switch(proof)
        {
            case GapProof::Relaxed: return GapBound::Relaxed;
            case GapProof::Roles: needsA1 = true; return GapBound::Roles;
            case GapProof::Lagrangian: needsA1 = true; return GapBound::Lagrangian;
            case GapProof::Balanced: needsA1 = true; return GapBound::Balanced;
            case GapProof::Search: needsA1 = true; return GapBound::Search;
            case GapProof::Open: break;
        }
        throw std::logic_error("makeBracketCertificate: open gap in an exact bracket");
    };
    for(std::size_t i = 0; i < result.gapProof.size(); ++i)
    {
        cert.gaps.push_back(kind(result.gapProof[i]));
        std::vector<Cost> mu;
        if(cert.gaps.back() == GapBound::Lagrangian)
        {
            mu.assign(at(instance.n()), 0);
            for(std::size_t k = 0; k < r.original.size(); ++k)
                mu[at(r.original[k])] = result.gapMultipliers[i][k];
        }
        cert.multipliers.push_back(std::move(mu));
    }
    cert.fastest = kind(result.fastestProof);
    if(instance.symmetric())
        cert.assumptions.push_back("S");
    if(needsA1)
        cert.assumptions.push_back("A1-NS");
    for(const auto& a : result.assumptions())
        if(a == "EO")
            cert.assumptions.push_back("EO");
    return cert;
}

void writeCertificate(std::ostream& out, const Certificate& cert)
{
    const Instance& in = cert.instance;
    const auto row = [&](const char* name, const auto& values) {
        out << name;
        for(auto v : values)
            out << " " << v;
        out << "\n";
    };
    out << "zeno-certificate " << cert.version << "\n";
    out << "instance " << in.n() << " " << in.t << " " << in.p << "\n";
    row("d", in.d);
    row("dbar", in.dbar);
    row("c", in.c);
    row("assume", cert.assumptions);
    out << "front " << cert.front.size() << "\n";
    for(const auto& point : cert.front)
        out << point.cost << " " << point.makespan << "\n";
    if(cert.version >= 2)
        out << "fastest " << kindName(cert.fastest) << "\n";
    for(std::size_t i = 0; i < cert.plans.size(); ++i)
    {
        out << "plan " << i + 1 << " " << cert.plans[i].planes.size() << "\n";
        for(std::size_t k = 0; k < cert.plans[i].planes.size(); ++k)
        {
            const auto& legs = cert.plans[i].planes[k];
            out << "plane " << k + 1 << " " << legs.size() << "\n";
            for(const Leg& leg : legs)
                out << leg.from << " " << leg.to << " " << leg.depart << " " << leg.arrive << " " << leg.passenger + 1 << "\n";
        }
    }
    out << "lower-bounds " << cert.gaps.size() << "\n";
    for(std::size_t i = 0; i < cert.gaps.size(); ++i)
    {
        out << i + 1 << " " << kindName(cert.gaps[i]);
        if(cert.gaps[i] == GapBound::Lagrangian)
            for(Cost mu : cert.multipliers[i])
                out << " " << mu;
        out << "\n";
    }
    out << "end\n";
}

Certificate readCertificate(std::istream& input)
{
    Lines lines(input);
    Certificate cert;
    const auto& header = lines.next("zeno-certificate", 2);
    if(header[1] != "1" && header[1] != "2")
        lines.fail("unsupported version " + header[1]);
    cert.version = header[1] == "1" ? 1 : 2;
    const auto& head = lines.next("instance", 4);
    const auto n = lines.number(head[1]);
    const auto t = lines.number(head[2]);
    const auto p = lines.number(head[3]);
    if(n > Lines::kMaxCount || t > Lines::kMaxCount || p > Lines::kMaxCount)
        lines.fail("n, t and p are limited to 100000 by this reader");
    cert.instance.t = static_cast<int>(t);
    cert.instance.p = static_cast<int>(p);
    const auto vector = [&](const char* name) {
        const auto& tokens = lines.next(name, at(static_cast<int>(n)) + 1);
        std::vector<std::int64_t> v;
        for(std::size_t i = 1; i < tokens.size(); ++i)
            v.push_back(lines.number(tokens[i]));
        return v;
    };
    cert.instance.d = vector("d");
    cert.instance.dbar = vector("dbar");
    cert.instance.c = vector("c");
    const auto& assume = lines.next("assume", Lines::kAny);
    cert.assumptions.assign(assume.begin() + 1, assume.end());
    const auto r = lines.number(lines.next("front", 2)[1]);
    if(r > Lines::kMaxLegs)
        lines.fail("too many points");
    std::int64_t totalLegs = 0;
    for(std::int64_t i = 0; i < r; ++i)
    {
        const auto& point = lines.next("", 2);
        cert.front.push_back({lines.number(point[0]), lines.number(point[1])});
    }
    if(cert.version >= 2)
    {
        const auto& fastest = lines.next("fastest", 2);
        const auto kind = kindFromName(fastest[1]);
        if(!kind || *kind == GapBound::Forest || *kind == GapBound::Lagrangian)
            lines.fail("unknown fastest bound '" + fastest[1] + "'");
        cert.fastest = *kind;
    }
    for(std::int64_t i = 0; i < r; ++i)
    {
        const auto& planHead = lines.next("plan", 3);
        if(lines.number(planHead[1]) != i + 1)
            lines.fail("plans must be listed in order");
        Plan plan;
        const auto planes = lines.number(planHead[2]);
        if(planes > Lines::kMaxCount)
            lines.fail("too many planes");
        for(std::int64_t k = 0; k < planes; ++k)
        {
            const auto& planeHead = lines.next("plane", 3);
            if(lines.number(planeHead[1]) != k + 1)
                lines.fail("planes must be listed in order");
            std::vector<Leg> legs;
            const auto count = lines.number(planeHead[2]);
            totalLegs += count;
            if(totalLegs > Lines::kMaxLegs)
                lines.fail("more than 10^7 legs");
            for(std::int64_t l = 0; l < count; ++l)
            {
                const auto& leg = lines.next("", 5);
                legs.push_back({static_cast<int>(lines.number(leg[0])), static_cast<int>(lines.number(leg[1])),
                                lines.number(leg[2]), lines.number(leg[3]), static_cast<int>(lines.number(leg[4])) - 1});
            }
            plan.planes.push_back(std::move(legs));
        }
        cert.plans.push_back(std::move(plan));
    }
    const auto gaps = lines.number(lines.next("lower-bounds", 2)[1]);
    for(std::int64_t i = 0; i < gaps; ++i)
    {
        const auto& gap = lines.next("", Lines::kAny);
        if(gap.size() < 2 || lines.number(gap[0]) != i + 1)
            lines.fail("lower bounds must be listed in order, as '<gap> <kind>'");
        const auto kind = kindFromName(gap[1]);
        const bool v1kind = kind == GapBound::Relaxed || kind == GapBound::Forest;
        if(!kind || *kind == GapBound::Closed || (cert.version == 1 && !v1kind))
            lines.fail("unknown lower bound '" + gap[1] + "'");
        cert.gaps.push_back(*kind);
        std::vector<Cost> mu;
        if(*kind == GapBound::Lagrangian)
        {
            if(gap.size() != at(static_cast<int>(n)) + 2)
                lines.fail("a lagrangian bound lists one multiplier per city");
            for(std::size_t k = 2; k < gap.size(); ++k)
                mu.push_back(lines.signedNumber(gap[k]));
        }
        else if(gap.size() != 2)
            lines.fail("unexpected values after '" + gap[1] + "'");
        cert.multipliers.push_back(std::move(mu));
    }
    lines.next("end", 1);
    if(!lines.done())
        throw std::runtime_error("certificate: content after 'end'");
    return cert;
}

CertificateCheck checkCertificate(const Certificate& cert)
{
    CertificateCheck report;
    const auto fail = [&](std::string why) { report.errors.push_back(std::move(why)); };
    const auto assumed = [&](const std::string& a) { return std::ranges::find(cert.assumptions, a) != cert.assumptions.end(); };
    const Instance& in = cert.instance;
    try
    {
        in.validate();
    }
    catch(const std::exception& e)
    {
        fail(std::string("invalid instance: ") + e.what());
        return report;
    }
    if(cert.version == 1 && (!in.symmetric() || !assumed("S")))
    {
        fail("version 1 certificates need symmetric durations, assumed as S");
        return report;
    }
    if(assumed("S") && !in.symmetric())
    {
        fail("assumption S listed for non-symmetric durations");
        return report;
    }
    const auto& f = cert.front;
    if(f.empty())
    {
        fail("the front is empty");
        return report;
    }
    for(std::size_t i = 0; i + 1 < f.size(); ++i)
        if(!(f[i].makespan < f[i + 1].makespan && f[i].cost > f[i + 1].cost))
        {
            // The gap obligations below assume a monotone list.
            fail("the points are not strictly increasing in makespan and decreasing in cost at point " + std::to_string(i + 1));
            return report;
        }
    if(cert.plans.size() != f.size() || cert.gaps.size() + 1 != f.size() || (cert.version >= 2 && cert.multipliers.size() != cert.gaps.size()))
    {
        fail("one plan per point and one lower bound per gap are required");
        return report;
    }

    // 1. Achieved.
    for(std::size_t i = 0; i < f.size(); ++i)
    {
        const PlanCheck check = checkPlan(in, cert.plans[i]);
        if(!check.ok)
            fail("plan " + std::to_string(i + 1) + " is infeasible: " + check.error);
        else if(check.cost != f[i].cost || check.makespan != f[i].makespan)
            fail("plan " + std::to_string(i + 1) + " has cost " + std::to_string(check.cost) + " and makespan " + std::to_string(check.makespan));
    }

    // 4. Nothing is cheaper than s * c_min.
    const Time s = in.landings();
    const Cost cmin = *std::ranges::min_element(in.c);
    if(f.back().cost != s * cmin)
        fail("the cheapest point's cost is not s * c_min = " + std::to_string(s * cmin));

    const LevelBounds bounds(in, f.back().makespan);
    bool usedA1 = false, usedA1NS = false;
    bool zeroDurationCity = false;
    for(int i = 0; i < in.n(); ++i)
        zeroDurationCity = zeroDurationCity || (in.d[at(i)] == 0 && in.dbar[at(i)] == 0);
    // The search proof (Corollary 6.10) needs A1-NS, and EO (event-ordered
    // plans) when some city has d = dbar = 0.
    const auto searchAllowed = [&](std::string& why) {
        if(!assumed("A1-NS") || (zeroDurationCity && !assumed("EO")))
        {
            why = zeroDurationCity ? "the search bound needs assumptions A1-NS and EO" : "the search bound needs assumption A1-NS";
            return false;
        }
        usedA1NS = true;
        return true;
    };
    // A lower bound of the given kind at level T, or a reason it cannot be used.
    const auto boundAt = [&](GapBound kind, Time T, Cost target, const std::vector<Cost>& mu, std::string& why) -> std::optional<Cost> {
        switch(kind)
        {
            case GapBound::Relaxed: return bounds.relaxed(T);
            case GapBound::Forest:
                if(!in.symmetric() || !assumed("A1"))
                {
                    why = "the forest bound needs symmetric durations and assumption A1";
                    return std::nullopt;
                }
                usedA1 = true;
                return bounds.forest(T);
            case GapBound::Search: break; // handled by the callers
            case GapBound::Roles:
            case GapBound::Lagrangian:
            case GapBound::Balanced:
                if(!assumed("A1-NS"))
                {
                    why = std::string("the ") + kindName(kind) + " bound needs assumption A1-NS";
                    return std::nullopt;
                }
                usedA1NS = true;
                if(kind == GapBound::Roles)
                    return bounds.roles(T);
                if(kind == GapBound::Lagrangian)
                    return bounds.lagrangian(T, mu);
                if(auto v = bounds.balanced(T, target))
                    return v;
                why = "the balanced program gave up";
                return std::nullopt;
            case GapBound::Closed: break;
        }
        why = "this bound does not apply here";
        return std::nullopt;
    };

    // 2. Nothing is faster than the first point.
    if(cert.version == 1 || cert.fastest == GapBound::Closed)
    {
        const Time segments = (s + in.p - 1) / in.p;
        const Time dmin = *std::ranges::min_element(in.d);
        if(!in.symmetric())
            fail("the closed-form fastest point needs symmetric durations");
        else if(f.front().makespan != 2 * dmin * segments)
            fail("the fastest point's makespan is not 2 * d_min * ceil(s / p) = " + std::to_string(2 * dmin * segments));
    }
    else if(cert.fastest == GapBound::Search)
    {
        std::string why;
        if(searchAllowed(why))
        {
            const auto closed = bounds.search(bounds.level(f.front().makespan), kInfCost, f.front().makespan);
            if(!closed)
                fail("fastest point: the search gave up");
            else if(!*closed)
                fail("fastest point: the search finds a faster plan");
        }
        else
            fail("fastest point: " + why);
    }
    else
    {
        std::string why;
        const auto bound = boundAt(cert.fastest, bounds.level(f.front().makespan), kInfCost, {}, why);
        if(!bound)
            fail("fastest point: " + why);
        else if(!isInf(*bound))
            fail(std::string("fastest point: the ") + kindName(cert.fastest) + " bound does not rule out faster plans");
    }

    // 3. Gaps.
    for(std::size_t i = 0; i + 1 < f.size(); ++i)
    {
        std::string why;
        static const std::vector<Cost> none;
        const auto& mu = cert.version >= 2 ? cert.multipliers[i] : none;
        if(cert.gaps[i] == GapBound::Lagrangian && mu.size() != static_cast<std::size_t>(in.n()))
        {
            fail("gap " + std::to_string(i + 1) + ": one multiplier per city is required");
            continue;
        }
        if(cert.gaps[i] == GapBound::Search)
        {
            if(!searchAllowed(why))
                fail("gap " + std::to_string(i + 1) + ": " + why);
            else if(const auto closed = bounds.search(bounds.level(f[i + 1].makespan), f[i].cost, f[i + 1].makespan); !closed)
                fail("gap " + std::to_string(i + 1) + ": the search gave up");
            else if(!*closed)
                fail("gap " + std::to_string(i + 1) + ": the search finds a cheaper plan inside the gap");
            continue;
        }
        const auto bound = boundAt(cert.gaps[i], bounds.level(f[i + 1].makespan), f[i].cost, mu, why);
        if(!bound)
            fail("gap " + std::to_string(i + 1) + ": " + why);
        else if(*bound < f[i].cost)
            fail("gap " + std::to_string(i + 1) + ": the " + kindName(cert.gaps[i]) + " bound " + std::to_string(*bound) +
                 " is below the cost " + std::to_string(f[i].cost));
    }
    if(in.symmetric())
        report.relied.push_back("S");
    if(usedA1)
        report.relied.push_back("A1");
    if(usedA1NS)
        report.relied.push_back("A1-NS");
    if(usedA1NS && zeroDurationCity && assumed("EO"))
        report.relied.push_back("EO");
    report.ok = report.errors.empty();
    return report;
}
} // namespace zeno
