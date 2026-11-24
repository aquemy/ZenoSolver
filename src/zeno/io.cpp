#include <zeno/io.hpp>

#include <algorithm>
#include <cstdint>
#include <ostream>
#include <set>
#include <stdexcept>
#include <string>
#include <utility>

namespace zeno
{
namespace
{
std::size_t at(int v) { return static_cast<std::size_t>(v); }

double numberValue(const std::string& flag, const std::string& value)
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
    if(used != value.size() || value.empty())
        throw std::invalid_argument("invalid value '" + value + "' for " + flag);
    return v;
}
} // namespace

void writePddlProblem(std::ostream& out, const Instance& in, const Front* front)
{
    const int n = in.n(), goal = n + 1;
    const char* indent = "         ";
    out << "(define (problem MULTIZENO-A)\n";
    out << "  (:domain  multi-zeno-travel)\n";
    out << "  (:objects ";
    for(int i = 1; i <= in.p; ++i)
        out << "plane" << i << " ";
    out << "- aircraft\n            ";
    for(int i = 1; i <= in.t; ++i)
        out << "person" << i << " ";
    out << "- person\n            ";
    for(int i = 0; i <= goal; ++i)
        out << "city" << i << " ";
    out << "- city)\n";

    out << "  (:init (= (total-cost) 0)\n" << indent;
    out << "(= (citythreat city0) 0)\n" << indent;
    for(int i = 1; i <= n; ++i)
        out << "(= (citythreat city" << i << ") " << in.c[at(i - 1)] << ")\n" << indent;
    out << "(= (citythreat city" << goal << ") 0)\n" << indent;

    for(int i = 1; i <= n; ++i)
    {
        const Time di = in.d[at(i - 1)], dbari = in.dbar[at(i - 1)];
        out << "\n; city" << i << "\n" << indent;
        out << "(= (timeTerre city0 city" << i << ") " << di << ")\n" << indent;
        out << "(= (timeTerre city" << i << " city0) " << di << ")\n" << indent;
        out << "(= (timeTerre city" << goal << " city" << i << ") " << dbari << ")\n" << indent;
        out << "(= (timeTerre city" << i << " city" << goal << ") " << dbari << ")\n" << indent;
        for(int j = 1; j <= n; ++j)
            if(i != j)
                out << "(= (timeTerre city" << i << " city" << j << ") " << in.centralFlight(i - 1, j - 1) << ")\n" << indent;
    }

    out << "\n; plane init\n" << indent;
    for(int i = 1; i <= in.p; ++i)
        out << "(at plane" << i << " city0)\n" << indent;
    for(int i = 1; i <= in.p; ++i)
        out << "(libre plane" << i << ")\n" << indent;
    out << "\n; person init\n" << indent;
    for(int i = 1; i <= in.t; ++i)
        out << "(at person" << i << " city0)\n" << indent;

    // Every person and every plane must end in C_G.
    out << "\n)\n(:goal (and \n" << indent;
    for(int i = 1; i <= in.t; ++i)
        out << "(at person" << i << " city" << goal << ")\n" << indent;
    for(int i = 1; i <= in.p; ++i)
        out << "(at plane" << i << " city" << goal << ")\n" << indent;
    out << "))\n";
    out << "  (:metric (and (minimize (total-time)) (minimize (total-cost)))))\n";

    const auto row = [&](const char* label, const auto& values) {
        out << "\n; " << label << " : \n; ";
        for(auto v : values)
            out << v << " ";
    };
    if(in.symmetric())
        row("Durations", in.d);
    else
    {
        row("Durations (C_I side)", in.d);
        row("Durations (C_G side)", in.dbar);
    }
    row("Costs", in.c);
    if(in.central)
    {
        out << "\n; Central flights : ";
        for(const auto& flights : *in.central)
        {
            out << "\n; ";
            for(auto v : flights)
                out << v << " ";
        }
    }
    if(front && !front->empty())
    {
        out << "\n; Pareto points : Makespan - Cost\n";
        for(const auto& point : *front)
            out << "; " << point.makespan << " " << point.cost << "\n";
    }
}

std::string defaultPddlName(const Instance& in)
{
    return "zeno" + std::to_string(in.n()) + "n" + std::to_string(in.t) + "t" + std::to_string(in.p) + "pMulti.pddl";
}

void writeDataFile(std::ostream& out, const Instance& in)
{
    const auto row = [&](const auto& values) {
        for(std::size_t i = 0; i < values.size(); ++i)
            out << (i ? " " : "") << values[i];
        out << "\n";
    };
    row(in.d);
    if(!in.symmetric())
        row(in.dbar);
    row(in.c);
    if(in.central)
    {
        out << "central\n";
        for(const auto& flights : *in.central)
            row(flights);
    }
}

namespace cli
{
int integerValue(const std::string& flag, const std::string& value)
{
    const double v = numberValue(flag, value);
    if(v != static_cast<double>(static_cast<int>(v)))
        throw std::invalid_argument("expected an integer for " + flag + ", got '" + value + "'");
    return static_cast<int>(v);
}

namespace
{
std::uint64_t seedValue(const std::string& value)
{
    std::size_t used = 0;
    std::uint64_t v = 0;
    try
    {
        v = std::stoull(value, &used);
    }
    catch(const std::exception&)
    {
        used = 0;
    }
    if(used != value.size() || value.empty() || value.front() == '-' || value.front() == '+')
        throw std::invalid_argument("expected a non-negative integer for --seed, got '" + value + "'");
    return v;
}

std::pair<Cost, Cost> costRange(const std::string& value)
{
    const auto comma = value.find(',');
    if(comma == std::string::npos)
        throw std::invalid_argument("--random-costs takes LO,HI, got '" + value + "'");
    const int lo = integerValue("--random-costs", value.substr(0, comma));
    const int hi = integerValue("--random-costs", value.substr(comma + 1));
    if(lo < 0 || hi < lo)
        throw std::invalid_argument("--random-costs needs 0 <= LO <= HI, got '" + value + "'");
    return {lo, hi};
}
} // namespace

InstanceArguments parseInstanceArguments(const std::vector<std::string>& args)
{
    InstanceArguments parsed;
    auto& o = parsed.options;
    metric::Options m;
    std::set<std::string> given;
    for(std::size_t i = 0; i < args.size(); ++i)
    {
        const std::string& flag = args[i];
        static const std::vector<std::string> withValue{"-n", "-t", "-p", "-d", "-C", "-D", "-E", "-W", "-r", "-j", "-k", "-l", "-m", "-x", "-y",
                                                        "--metric", "--seed", "--hubs", "--coords", "--random-costs"};
        if(flag == "-F")
            continue;
        if(std::ranges::find(withValue, flag) == withValue.end())
        {
            parsed.rest.push_back(flag);
            continue;
        }
        if(i + 1 >= args.size())
            throw std::invalid_argument("missing value for " + flag);
        const std::string& value = args[++i];
        given.insert(flag);
        if(flag == "-n") o.n = integerValue(flag, value);
        else if(flag == "-t") o.t = integerValue(flag, value);
        else if(flag == "-p") o.p = integerValue(flag, value);
        else if(flag == "-d") o.dataFile = value;
        else if(flag == "-C") o.costFunction = integerValue(flag, value);
        else if(flag == "-D") o.durationFunction = integerValue(flag, value);
        else if(flag == "-E") o.eastFunction = integerValue(flag, value);
        else if(flag == "-W") o.westFunction = integerValue(flag, value);
        else if(flag == "-r") o.adjust = numberValue(flag, value);
        else if(flag == "-j") o.scaleC = numberValue(flag, value);
        else if(flag == "-k") o.transC = numberValue(flag, value);
        else if(flag == "-l") o.scaleD = numberValue(flag, value);
        else if(flag == "-m") o.transD = numberValue(flag, value);
        else if(flag == "-x") o.x = numberValue(flag, value);
        else if(flag == "-y") o.y = numberValue(flag, value);
        else if(flag == "--metric")
        {
            if(value == "plane") m.geometry = metric::Geometry::Plane;
            else if(value == "sphere") m.geometry = metric::Geometry::Sphere;
            else throw std::invalid_argument("--metric takes plane or sphere, got '" + value + "'");
        }
        else if(flag == "--hubs")
        {
            if(value == "same") m.hubs = metric::Hubs::Same;
            else if(value == "apart") m.hubs = metric::Hubs::Apart;
            else throw std::invalid_argument("--hubs takes same or apart, got '" + value + "'");
        }
        else if(flag == "--seed") m.seed = seedValue(value);
        else if(flag == "--coords") m.coordsFile = value;
        else if(flag == "--random-costs") m.randomCosts = costRange(value);
    }
    if(given.contains("--metric"))
    {
        for(const char* durations : {"-d", "-D", "-E", "-W", "-l", "-m"})
            if(given.contains(durations))
                throw std::invalid_argument(std::string("--metric: durations are distances, so ") + durations + " does not apply");
        parsed.metric = m;
    }
    else
        for(const char* option : {"--seed", "--hubs", "--coords", "--random-costs"})
            if(given.contains(option))
                throw std::invalid_argument(std::string(option) + " needs --metric plane or --metric sphere");
    return parsed;
}

Instance buildInstance(const InstanceArguments& arguments)
{
    if(arguments.metric)
        return metric::buildInstance(arguments.options, *arguments.metric);
    return legacy::buildInstance(arguments.options);
}

const char* instanceOptionsHelp()
{
    return R"(Instance (the options of the 2016 zenoSolver, without its swap; see below):
  -n N        central cities (default 3)
  -t N        passengers (default 3)
  -p N        planes (default 2), 1 <= p <= t
  -d FILE     data file: durations then costs (2 lines), or C_I-side
              durations, C_G-side durations, costs (3 lines); then, optionally,
              a line "central" and n lines of n central-flight durations
              (symmetric, zero diagonal). Without it, central flights last
              max(d_i, dbar_i) + max(d_j, dbar_j) + 100, which satisfies (A1)
  -C K -D K   generator of costs / durations: 1 log, 2 sqrt, 3 identity (default),
              4 power of two, 5 staircase
  -E K -W K   non-symmetric durations: -E generates the C_I-side durations,
              -W the C_G-side ones
  -r R        multiply before truncating to integers (default 1)
  -j -k       cost generator scale / translation
  -l -m       duration generator scale / translation
  -x -y       output scale / translation of both generators
  -F          accepted for compatibility (the front is always printed)

Metric instances (every flight lasts the distance between its ends):
  --metric plane|sphere  random points, uniform in the square [0, 100]^2
                         (plane), or uniform on a sphere of radius 6371 km with
                         great-circle distances (sphere)
  --seed S               seed of the points and of --random-costs (default 1)
  --hubs same|apart      same (default): C_I and C_G are one point, so the
                         durations are symmetric (S); apart: two points, and the
                         instance is non-symmetric
  --coords FILE          the points instead of random ones: one "x,y" (plane)
                         or "lat,lon" in degrees (sphere) per line, optionally
                         after a label; the hub first (C_I, then C_G with
                         --hubs apart), then the n central cities
  --random-costs LO,HI   uniform random integer costs (default: -C -j -k -x -y,
                         not scaled by -r)
  -r R                   distances are multiplied by R (default 1) and
                         rounded, then every duration becomes its shortest
                         path over the flights, so the table satisfies the
                         triangle inequality (AΔ) exactly. With --hubs same
                         the front is exact (Theorem 4.10, Corollary 4.12)
  -d -D -E -W -l -m do not apply. `zeno generate` writes the table as the
  "central" block of the data file.

Each option means what it says, and data files are read as written. The 2016
solvers swapped durations and costs whenever the first duration exceeded the
second, which their generator always did: a 2016 or paper instance
"-C a -D b" is "-C b -D a" here, and "-C c -E a -W b" is "-C a -E c -W b".
Two exceptions. When truncation ties the first two durations, the 2016 code
did not swap, so its flags mean the same here (-n 10 -D 1 -r 1 starts with
d = (2, 2, ...); `zeno generate` on both forms shows which case applies).
And zeno scales both duration sides of -E/-W with -l/-m, so the -E/-W rule is
exact only if the 2016 instance had the same -j/-k as -l/-m (the defaults
do); otherwise write it as a data file.
)";
}
} // namespace cli
} // namespace zeno
