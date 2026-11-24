// zeno: exact Pareto fronts of MultiZenoTravel instances.
//
//   zeno [front] [instance options] [solver options]
//   zeno check CERTIFICATE
//   zeno pddl [instance options] [-O FILE] [--no-front]
//   zeno generate [instance options] [-O FILE]
//
// The instance options are those of the 2016 solvers and build the same
// instances, plus metric instances (--metric; zeno --help).
#include <zeno/certificate.hpp>
#include <zeno/flights.hpp>
#include <zeno/io.hpp>
#include <zeno/ns.hpp>
#include <zeno/solve.hpp>

#include <algorithm>
#include <fstream>
#include <iostream>
#include <optional>
#include <ranges>
#include <stdexcept>
#include <string>
#include <string_view>
#include <vector>

namespace
{
constexpr std::string_view kUsage = R"(usage: zeno [front] [instance options] [solver options]
       zeno check CERTIFICATE
       zeno pddl [instance options] [-O FILE] [--no-front]
       zeno generate [instance options] [-O FILE]

front     Pareto front (cost, makespan) as "cost makespan" lines by
          increasing cost (the default command). Exact for symmetric
          instances whose central flights satisfy (A1) or the triangle
          inequality (AΔ) (Theorem 4.10, Corollary 4.12; in Lean,
          solveFront_isParetoFront_ATri): the default table satisfies (A1),
          --metric tables (AΔ). With a central-flight table,
          stderr says which holds, or warns that the front may not be exact
          (Example 4.13). For non-symmetric instances: achieved points
          (simulated plans) and, on stderr, which gaps a lower bound
          certifies
check     verify a front certificate (doc/certificate-format.md) and print
          the assumptions it relied on (S; A1|AD: central flights satisfy
          (A1) or (AΔ), as for the Lean checker, Cert.check_sound_A1 and
          Cert.check_sound_ATri; A1-NS)
pddl      write the instance as a PDDL problem for pddl/multi-zeno-travel.pddl,
          with its front as comments unless --no-front (default file
          zeno<n>n<t>t<p>pMulti.pddl)
generate  write the instance as a data file for -d (default: standard output)

)";

constexpr std::string_view kSolverHelp = R"(
Solver (front):
  --threads N          worker threads (default: all cores)
  --levels MODE        auto (default), sweep (bracket every level) or search
                       (bisect for the breakpoints; for wide level ranges)
  --plans              after the front, print a plan for every point (checked
                       by simulation): one line per plane, legs as
                       from->to[depart,arrive] with the passenger carried (pK)
  --certificate FILE   write a certificate of the front to FILE
  --stats              print solver statistics on stderr
  -h, --help           this help
)";

std::string location(int loc, int n)
{
    if(loc == 0)
        return "CI";
    if(loc == n + 1)
        return "CG";
    return "c" + std::to_string(loc);
}

void printPlans(const zeno::SolveResult& result, int n)
{
    for(std::size_t i = result.front.size(); i-- > 0;)
    {
        std::cout << "\n# cost " << result.front[i].cost << ", makespan " << result.front[i].makespan << "\n";
        const auto& plan = result.plans[i];
        for(std::size_t k = 0; k < plan.planes.size(); ++k)
        {
            std::cout << "plane " << k + 1 << ":";
            for(const auto& leg : plan.planes[k])
            {
                std::cout << " " << location(leg.from, n) << "->" << location(leg.to, n) << "[" << leg.depart << "," << leg.arrive << "]";
                if(leg.passenger >= 0)
                    std::cout << "p" << leg.passenger + 1;
            }
            std::cout << "\n";
        }
    }
}

void printStats(const zeno::SolveStats& s)
{
    std::cerr << "levels " << s.lowestLevel << ".." << s.highestLevel << " (x" << s.scale << ", " << s.levels << " levels)"
              << ", cities " << s.reducedCities << ", max tree " << s.maxTree << "\n"
              << "settled: bracket " << s.closedByBracket << ", pairs " << s.closedByPairs << ", chains " << s.closedByChains
              << ", monotone " << s.closedByMonotonicity << ", exact " << s.exactCalls << "\n"
              << "work: " << s.work.states << " states, " << s.work.relaxations << " relaxations\n"
              << "seconds: table " << s.secondsTable << ", bracket " << s.secondsBracket << ", chains " << s.secondsChains
              << ", exact " << s.secondsExact << ", plans " << s.secondsPlans << "\n";
}

/// Value of an option taking one argument; removes both tokens from `rest`.
std::optional<std::string> takeValue(std::vector<std::string>& rest, std::string_view flag)
{
    for(std::size_t i = 0; i < rest.size(); ++i)
        if(rest[i] == flag)
        {
            if(i + 1 >= rest.size())
                throw std::invalid_argument("missing value for " + std::string(flag));
            std::string value = rest[i + 1];
            rest.erase(rest.begin() + static_cast<std::ptrdiff_t>(i), rest.begin() + static_cast<std::ptrdiff_t>(i) + 2);
            return value;
        }
    return std::nullopt;
}

bool takeFlag(std::vector<std::string>& rest, std::string_view flag)
{
    const auto it = std::ranges::find(rest, flag);
    if(it == rest.end())
        return false;
    rest.erase(it);
    return true;
}

void rejectLeftovers(const std::vector<std::string>& rest)
{
    if(!rest.empty())
        throw std::invalid_argument("unknown option " + rest.front() + " (see zeno --help)");
}

std::ofstream openOutput(const std::string& path)
{
    std::ofstream out(path);
    if(!out)
        throw std::runtime_error("cannot write " + path);
    return out;
}

// Symmetric instances with a central-flight table: which assumption makes the
// front exact, or a warning when neither (A1) nor (AΔ) holds.
void reportFlights(const zeno::Instance& instance, const zeno::Front& front)
{
    if(!instance.central)
        return; // the default table satisfies (A1)
    const zeno::FlightAssumptions flights = zeno::checkFlights(instance);
    if(flights.a1)
    {
        std::cerr << "central flights satisfy (A1)" << (flights.triangle ? " and (AΔ)" : "") << ": the front is exact (Theorem 4.7, Corollary 4.8)\n";
        return;
    }
    if(flights.triangle)
    {
        std::cerr << "central flights satisfy (AΔ), not (A1): the front is exact (Theorem 4.10, Corollary 4.12)\n";
        return;
    }
    const auto gaps = zeno::symmetricGaps(instance, front);
    const auto unproved = static_cast<std::size_t>(std::ranges::count(gaps, zeno::GapBound::Forest));
    if(unproved == 0)
    {
        std::cerr << "central flights satisfy neither (A1) nor (AΔ), but the relaxation L certifies every gap (Lemma 3.4): the front is exact\n";
        return;
    }
    std::cerr << "warning: central flights satisfy neither (A1) nor (AΔ), so the front may not be exact (Example 4.13). Every point is achieved "
              << "without central flights, and the relaxation L (Lemma 3.4) certifies " << gaps.size() - unproved << " of " << gaps.size()
              << " gaps; the others need (A1) or (AΔ):\n";
    for(std::size_t i = 0; i < gaps.size(); ++i)
        if(gaps[i] == zeno::GapBound::Forest)
            std::cerr << "  unproved gap between makespans " << front[i].makespan << " and " << front[i + 1].makespan << ": a plan with makespan < "
                      << front[i + 1].makespan << " may cost less than " << front[i].cost << "\n";
}

const char* proofName(zeno::GapProof proof)
{
    switch(proof)
    {
        case zeno::GapProof::Open: return "open";
        case zeno::GapProof::Relaxed: return "relaxed";
        case zeno::GapProof::Roles: return "roles";
        case zeno::GapProof::Lagrangian: return "lagrangian";
        case zeno::GapProof::Search: return "search";
        case zeno::GapProof::Balanced: return "balanced";
    }
    return "?";
}

// Non-symmetric instances: the certified bracket of zeno::solveBracket.
int runBracket(const zeno::Instance& instance, zeno::SolveOptions options, bool plans, const std::optional<std::string>& certificate, bool stats)
{
    options.plans = plans || certificate.has_value();
    const zeno::BracketResult result = zeno::solveBracket(instance, options);
    for(const auto& point : std::views::reverse(result.upper))
        std::cout << point.cost << " " << point.makespan << "\n";
    if(plans)
    {
        zeno::SolveResult shown;
        shown.front = result.upper;
        shown.plans = result.plans;
        printPlans(shown, instance.n());
    }
    // Every bound but lemma R needs (A1-NS) (Theorem 6.1), which a central-flight
    // table may violate; whether (AΔ) is enough instead is open (Conjecture 6.7).
    const bool a1ns = zeno::checkFlights(instance).a1ns;
    const auto proved = [&](zeno::GapProof proof) { return proof == zeno::GapProof::Relaxed || (a1ns && proof != zeno::GapProof::Open); };
    if(instance.central)
        std::cerr << (a1ns ? "central flights satisfy (A1-NS)\n"
                           : "warning: central flights violate (A1-NS), which every bound but lemma R needs (Theorem 6.1), so only lemma R "
                             "counts below (whether (AΔ) suffices is open: Conjecture 6.7)\n");
    std::size_t closed = 0;
    for(auto proof : result.gapProof)
        closed += proved(proof);
    const bool fastestReached = result.fastestLower == result.upper.front().makespan;
    const bool fastest = fastestReached && proved(result.fastestProof);
    const bool exact = fastest && closed == result.gapProof.size();
    std::cerr << "non-symmetric instance: " << result.upper.size() << " achieved points; fastest makespan "
              << (fastest           ? "certified"
                  : fastestReached ? "not certified (its bound needs (A1-NS))"
                                   : "not certified (bound " + std::to_string(result.fastestLower) + ")")
              << "; " << closed << " of " << result.gapProof.size() << " gaps certified; "
              << (exact ? "the front is exact" : "the front is a bracket");
    const auto assumptions = result.assumptions();
    if(exact && !assumptions.empty())
    {
        std::cerr << ", assuming";
        for(const auto& a : assumptions)
            std::cerr << " " << a;
    }
    std::cerr << "\n";
    for(std::size_t i = 0; i < result.gapProof.size(); ++i)
        if(result.gapProof[i] != zeno::GapProof::Open && !proved(result.gapProof[i]))
            std::cerr << "  unproved gap between makespans " << result.upper[i].makespan << " and " << result.upper[i + 1].makespan
                      << ": closed by the " << proofName(result.gapProof[i]) << " bound, which needs (A1-NS)\n";
        else if(result.gapProof[i] == zeno::GapProof::Open)
            std::cerr << "  open gap between makespans " << result.upper[i].makespan << " and " << result.upper[i + 1].makespan
                      << ": a plan with makespan < " << result.upper[i + 1].makespan << " costs at least " << result.gapLower[i]
                      << (a1ns ? "" : " if (A1-NS) held") << " (achieved: " << result.upper[i].cost << "; "
                      << (result.openReason[i] == zeno::BracketResult::OpenReason::Unscheduled
                              ? "a cheaper balanced configuration exists, no schedule found within the gap"
                              : "the exact balanced program gave up")
                      << ")\n";
    if(certificate)
    {
        if(!result.exact())
            throw std::runtime_error("no certificate: the front is a bracket with open gaps");
        auto out = openOutput(*certificate);
        zeno::writeCertificate(out, zeno::makeBracketCertificate(instance, result));
    }
    if(stats)
        printStats(result.stats);
    return 0;
}

int runFront(const std::vector<std::string>& args)
{
    auto parsed = zeno::cli::parseInstanceArguments(args);
    auto& rest = parsed.rest;
    zeno::SolveOptions options;
    if(auto v = takeValue(rest, "--threads"))
        options.threads = static_cast<unsigned>(zeno::cli::integerValue("--threads", *v));
    if(auto v = takeValue(rest, "--levels"))
    {
        if(*v == "sweep")
            options.levels = zeno::LevelStrategy::Sweep;
        else if(*v == "search")
            options.levels = zeno::LevelStrategy::Search;
        else if(*v != "auto")
            throw std::invalid_argument("--levels takes auto, sweep or search");
    }
    const auto certificate = takeValue(rest, "--certificate");
    const bool plans = takeFlag(rest, "--plans");
    const bool stats = takeFlag(rest, "--stats");
    rejectLeftovers(rest);
    options.plans = plans || certificate.has_value();

    const zeno::Instance instance = zeno::cli::buildInstance(parsed);
    if(!instance.symmetric())
        return runBracket(instance, options, plans, certificate, stats);
    const zeno::SolveResult result = zeno::solveFront(instance, options);
    for(const auto& point : std::views::reverse(result.front))
        std::cout << point.cost << " " << point.makespan << "\n";
    if(plans)
        printPlans(result, instance.n());
    reportFlights(instance, result.front);
    if(certificate)
    {
        auto out = openOutput(*certificate);
        zeno::writeCertificate(out, zeno::makeCertificate(instance, result));
    }
    if(stats)
        printStats(result.stats);
    return 0;
}

int runCheck(const std::vector<std::string>& args)
{
    if(args.size() != 1)
        throw std::invalid_argument("usage: zeno check CERTIFICATE");
    std::ifstream file(args.front());
    if(!file)
        throw std::runtime_error("cannot open " + args.front());
    const zeno::CertificateCheck report = zeno::checkCertificate(zeno::readCertificate(file));
    for(const auto& error : report.errors)
        std::cout << "error: " << error << "\n";
    if(!report.ok)
    {
        std::cout << "certificate rejected\n";
        return 2;
    }
    std::cout << "certificate accepted, assuming";
    for(const auto& a : report.relied)
        std::cout << " " << a;
    std::cout << "\n";
    if(std::ranges::find(report.relied, std::string(zeno::kA1OrTriangle)) != report.relied.end())
        std::cout << zeno::kA1OrTriangle << ": the forest gaps hold when the central flights satisfy (A1) (Theorem 4.7) or (AΔ) "
                  << "(Theorem 4.10, Corollary 4.12); the Lean checker is proved sound under both (Cert.check_sound_A1, Cert.check_sound_ATri)\n";
    return 0;
}

int runPddl(const std::vector<std::string>& args)
{
    auto parsed = zeno::cli::parseInstanceArguments(args);
    const auto file = takeValue(parsed.rest, "-O");
    const bool noFront = takeFlag(parsed.rest, "--no-front");
    rejectLeftovers(parsed.rest);
    const zeno::Instance instance = zeno::cli::buildInstance(parsed);
    auto out = openOutput(file.value_or(zeno::defaultPddlName(instance)));
    if(!noFront && instance.symmetric())
    {
        const zeno::Front front = zeno::solveFront(instance).front;
        // Without (A1) or (AΔ), the front is exact only if L certifies every gap.
        if(zeno::checkFlights(instance).exactSymmetric() || std::ranges::count(zeno::symmetricGaps(instance, front), zeno::GapBound::Forest) == 0)
        {
            zeno::writePddlProblem(out, instance, &front);
            return 0;
        }
        std::cerr << "zeno: warning: central flights satisfy neither (A1) nor (AΔ), so the front may not be exact (Example 4.13); "
                     "it is not written\n";
    }
    zeno::writePddlProblem(out, instance);
    return 0;
}

int runGenerate(const std::vector<std::string>& args)
{
    auto parsed = zeno::cli::parseInstanceArguments(args);
    const auto file = takeValue(parsed.rest, "-O");
    rejectLeftovers(parsed.rest);
    const zeno::Instance instance = zeno::cli::buildInstance(parsed);
    if(!file)
    {
        zeno::writeDataFile(std::cout, instance);
        return 0;
    }
    auto out = openOutput(*file);
    zeno::writeDataFile(out, instance);
    return 0;
}
} // namespace

int main(int argc, char** argv)
{
    try
    {
        std::vector<std::string> args(argv + 1, argv + argc);
        if(std::ranges::any_of(args, [](const std::string& a) { return a == "-h" || a == "--help"; }))
        {
            std::cout << kUsage << zeno::cli::instanceOptionsHelp() << kSolverHelp;
            return 0;
        }
        std::string command = "front";
        if(!args.empty() && (args.front() == "front" || args.front() == "check" || args.front() == "pddl" || args.front() == "generate"))
        {
            command = args.front();
            args.erase(args.begin());
        }
        if(command == "check")
            return runCheck(args);
        if(command == "pddl")
            return runPddl(args);
        if(command == "generate")
            return runGenerate(args);
        return runFront(args);
    }
    catch(const std::exception& e)
    {
        std::cerr << "zeno: " << e.what() << "\n";
        return 1;
    }
}
