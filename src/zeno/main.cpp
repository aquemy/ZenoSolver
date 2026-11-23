// zeno: exact Pareto fronts of MultiZenoTravel instances.
//
//   zeno [front] [instance options] [--threads N] [--stats]
//
// The instance options are those of the 2016 solvers (see `zeno --help`), and
// build the same instance. The front is printed as "cost makespan" lines by
// increasing cost.
#include <zeno/certificate.hpp>
#include <zeno/legacy_input.hpp>
#include <zeno/solve.hpp>

#include <fstream>

#include <cstdlib>
#include <iostream>
#include <map>
#include <optional>
#include <ranges>
#include <stdexcept>
#include <string>
#include <string_view>
#include <vector>

namespace
{
constexpr std::string_view kUsage = R"(usage: zeno [front] [options]
       zeno check CERTIFICATE

Exact Pareto front (cost, makespan) of a symmetric MultiZenoTravel instance,
printed as "cost makespan" lines by increasing cost.

Instance (same meaning as for the 2016 zenoSolver):
  -n N        central cities (default 3)
  -t N        passengers (default 3)
  -p N        planes (default 2), 1 <= p <= t
  -d FILE     data file: durations then costs (2 lines), or west durations,
              east durations, costs (3 lines)
  -C K -D K   generator of costs / durations: 1 log, 2 sqrt, 3 identity (default),
              4 power of two, 5 staircase
  -E K -W K   east / west duration generators (non-symmetric)
  -r R        multiply before truncating to integers (default 1)
  -j -k       cost generator scale / translation
  -l -m       duration generator scale / translation
  -x -y       output scale / translation of both generators
  -F          accepted for compatibility (the front is always printed)

Solver:
  --threads N  worker threads (default: all cores)
  --plans      after the front, print a plan for every point (checked by
               simulation): one line per plane, legs as
               from->to[depart,arrive] with the passenger carried (pK)
  --certificate FILE
               write a certificate of the front to FILE
               (doc/certificate-format.md)
  --stats      print solver statistics on stderr
  -h, --help   this help

zeno check CERTIFICATE verifies a certificate with the reference checker
and prints the assumptions it relied on.
)";

struct CliOptions
{
    zeno::legacy::Options instance;
    zeno::SolveOptions solve;
    bool stats = false;
    bool printPlans = false;
    std::optional<std::string> certificate;
};

double number(std::string_view flag, const std::string& value)
{
    std::size_t used = 0;
    double v = 0;
    try
    {
        v = std::stod(value, &used);
    }
    catch(const std::exception&)
    {
        used = 0;
    }
    if(used != value.size())
        throw std::invalid_argument("invalid value '" + value + "' for " + std::string(flag));
    return v;
}

int integer(std::string_view flag, const std::string& value)
{
    const double v = number(flag, value);
    if(v != static_cast<double>(static_cast<int>(v)))
        throw std::invalid_argument("expected an integer for " + std::string(flag) + ", got '" + value + "'");
    return static_cast<int>(v);
}

std::optional<CliOptions> parse(int argc, char** argv)
{
    CliOptions o;
    std::vector<std::string> args(argv + 1, argv + argc);
    std::size_t i = 0;
    if(i < args.size() && args[i] == "front")
        ++i;
    for(; i < args.size(); ++i)
    {
        const std::string& flag = args[i];
        if(flag == "-h" || flag == "--help")
        {
            std::cout << kUsage;
            return std::nullopt;
        }
        if(flag == "-F")
            continue;
        if(flag == "--stats")
        {
            o.stats = true;
            continue;
        }
        if(flag == "--plans")
        {
            o.solve.plans = true;
            o.printPlans = true;
            continue;
        }
        if(i + 1 >= args.size())
            throw std::invalid_argument("missing value for " + flag);
        const std::string& value = args[++i];
        auto& in = o.instance;
        if(flag == "-n") in.n = integer(flag, value);
        else if(flag == "-t") in.t = integer(flag, value);
        else if(flag == "-p") in.p = integer(flag, value);
        else if(flag == "-d") in.dataFile = value;
        else if(flag == "-C") in.costFunction = integer(flag, value);
        else if(flag == "-D") in.durationFunction = integer(flag, value);
        else if(flag == "-E") in.eastFunction = integer(flag, value);
        else if(flag == "-W") in.westFunction = integer(flag, value);
        else if(flag == "-r") in.adjust = integer(flag, value);
        else if(flag == "-j") in.scaleC = number(flag, value);
        else if(flag == "-k") in.transC = number(flag, value);
        else if(flag == "-l") in.scaleD = number(flag, value);
        else if(flag == "-m") in.transD = number(flag, value);
        else if(flag == "-x") in.x = number(flag, value);
        else if(flag == "-y") in.y = number(flag, value);
        else if(flag == "--threads") o.solve.threads = static_cast<unsigned>(integer(flag, value));
        else if(flag == "--certificate")
        {
            o.certificate = value;
            o.solve.plans = true;
        }
        else
            throw std::invalid_argument("unknown option " + flag + " (see zeno --help)");
    }
    return o;
}

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
} // namespace

int check(const std::string& path)
{
    std::ifstream file(path);
    if(!file)
        throw std::runtime_error("cannot open " + path);
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
    return 0;
}

int main(int argc, char** argv)
{
    try
    {
        if(argc >= 2 && std::string_view(argv[1]) == "check")
        {
            if(argc != 3)
                throw std::invalid_argument("usage: zeno check CERTIFICATE");
            return check(argv[2]);
        }
        const auto options = parse(argc, argv);
        if(!options)
            return 0;
        const zeno::Instance instance = zeno::legacy::buildInstance(options->instance);
        const zeno::SolveResult result = zeno::solveFront(instance, options->solve);
        for(const auto& point : std::views::reverse(result.front))
            std::cout << point.cost << " " << point.makespan << "\n";
        if(options->printPlans)
            printPlans(result, instance.n());
        if(options->certificate)
        {
            std::ofstream out(*options->certificate);
            if(!out)
                throw std::runtime_error("cannot write " + *options->certificate);
            zeno::writeCertificate(out, zeno::makeCertificate(instance, result));
        }
        if(options->stats)
            printStats(result.stats);
    }
    catch(const std::exception& e)
    {
        std::cerr << "zeno: " << e.what() << "\n";
        return 1;
    }
    return 0;
}
