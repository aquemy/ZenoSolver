#include <zeno/certificate.hpp>

#include <zeno/forest.hpp>
#include <zeno/one_plane.hpp>
#include <zeno/reduce.hpp>

#include <algorithm>
#include <istream>
#include <ostream>
#include <sstream>
#include <stdexcept>

namespace zeno
{
namespace
{
std::size_t at(int v) { return static_cast<std::size_t>(v); }

/// Scaled level of the gap below a point of makespan `nextMakespan`.
Time gapLevel(Time nextMakespan, Time scale)
{
    const Time half = (nextMakespan - 1) / 2;
    return half / scale;
}

/// Lower bounds at the gap levels of a symmetric instance, sharing one table
/// that covers every level below a point of makespan <= maxMakespan.
struct LevelBounds
{
    ReducedInstance r;
    OnePlaneTable G;

    LevelBounds(const Instance& instance, Time maxMakespan)
        : r(reduce(instance))
        , G(r.fill, r.c, r.maxGroup(), std::max<Time>(gapLevel(maxMakespan, r.scale), 0)) {}

    Cost relaxed(Time T) const { return T < 0 ? kInfCost : relaxedCost(r, G, checked(T)); }
    Cost forest(Time T) const { return T < 0 ? kInfCost : forestCost(r, G, checked(T), r.maxTree()); }

private:
    Time checked(Time T) const
    {
        if(T > G.maxLevel())
            throw std::logic_error("LevelBounds: level outside the table");
        return T;
    }
};

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
        const Time T = gapLevel(cert.front[i + 1].makespan, bounds.r.scale);
        const bool relaxedEnough = bounds.relaxed(T) >= cert.front[i].cost;
        cert.gaps.push_back(relaxedEnough ? GapBound::Relaxed : GapBound::Forest);
        needsA1 = needsA1 || !relaxedEnough;
    }
    cert.assumptions = {"S"};
    if(needsA1)
        cert.assumptions.push_back("A1");
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
    out << "zeno-certificate 1\n";
    out << "instance " << in.n() << " " << in.t << " " << in.p << "\n";
    row("d", in.d);
    row("dbar", in.dbar);
    row("c", in.c);
    row("assume", cert.assumptions);
    out << "front " << cert.front.size() << "\n";
    for(const auto& point : cert.front)
        out << point.cost << " " << point.makespan << "\n";
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
        out << i + 1 << " " << (cert.gaps[i] == GapBound::Relaxed ? "relaxed" : "forest") << "\n";
    out << "end\n";
}

Certificate readCertificate(std::istream& input)
{
    Lines lines(input);
    Certificate cert;
    const auto& header = lines.next("zeno-certificate", 2);
    if(header[1] != "1")
        lines.fail("unsupported version " + header[1]);
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
        const auto& gap = lines.next("", 2);
        if(lines.number(gap[0]) != i + 1)
            lines.fail("lower bounds must be listed in order");
        if(gap[1] == "relaxed")
            cert.gaps.push_back(GapBound::Relaxed);
        else if(gap[1] == "forest")
            cert.gaps.push_back(GapBound::Forest);
        else
            lines.fail("unknown lower bound '" + gap[1] + "'");
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
    if(!in.symmetric() || !assumed("S"))
    {
        fail("version 1 certificates need symmetric durations, assumed as S");
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
            fail("the points are not strictly increasing in makespan and decreasing in cost at point " + std::to_string(i + 1));
    if(cert.plans.size() != f.size() || cert.gaps.size() + 1 != f.size())
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

    // 2. and 4. Closed forms.
    const Time s = in.landings();
    const Time segments = (s + in.p - 1) / in.p;
    const Time dmin = *std::ranges::min_element(in.d);
    const Cost cmin = *std::ranges::min_element(in.c);
    if(f.front().makespan != 2 * dmin * segments)
        fail("the fastest point's makespan is not 2 * d_min * ceil(s / p) = " + std::to_string(2 * dmin * segments));
    if(f.back().cost != s * cmin)
        fail("the cheapest point's cost is not s * c_min = " + std::to_string(s * cmin));

    // 3. Gaps.
    const LevelBounds bounds(in, f.back().makespan);
    bool usedA1 = false;
    for(std::size_t i = 0; i + 1 < f.size(); ++i)
    {
        const Time T = gapLevel(f[i + 1].makespan, bounds.r.scale);
        const bool forest = cert.gaps[i] == GapBound::Forest;
        if(forest && !assumed("A1"))
        {
            fail("gap " + std::to_string(i + 1) + " uses the forest bound, which needs assumption A1");
            continue;
        }
        const Cost bound = forest ? bounds.forest(T) : bounds.relaxed(T);
        usedA1 = usedA1 || forest;
        if(bound < f[i].cost)
            fail("gap " + std::to_string(i + 1) + ": the " + (forest ? "forest" : "relaxed") + " bound " + std::to_string(bound) +
                 " is below the cost " + std::to_string(f[i].cost));
    }
    report.relied = {"S"};
    if(usedA1)
        report.relied.push_back("A1");
    report.ok = report.errors.empty();
    return report;
}
} // namespace zeno
