#include <zeno/io.hpp>

#include <algorithm>
#include <ostream>
#include <stdexcept>
#include <string>

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

    const auto longest = [&](int i) { return std::max(in.d[at(i - 1)], in.dbar[at(i - 1)]); };
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
                out << "(= (timeTerre city" << i << " city" << j << ") " << longest(i) + longest(j) + 100 << ")\n" << indent;
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

InstanceArguments parseInstanceArguments(const std::vector<std::string>& args)
{
    InstanceArguments parsed;
    auto& o = parsed.options;
    for(std::size_t i = 0; i < args.size(); ++i)
    {
        const std::string& flag = args[i];
        static const std::vector<std::string> withValue{"-n", "-t", "-p", "-d", "-C", "-D", "-E", "-W", "-r", "-j", "-k", "-l", "-m", "-x", "-y"};
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
        if(flag == "-n") o.n = integerValue(flag, value);
        else if(flag == "-t") o.t = integerValue(flag, value);
        else if(flag == "-p") o.p = integerValue(flag, value);
        else if(flag == "-d") o.dataFile = value;
        else if(flag == "-C") o.costFunction = integerValue(flag, value);
        else if(flag == "-D") o.durationFunction = integerValue(flag, value);
        else if(flag == "-E") o.eastFunction = integerValue(flag, value);
        else if(flag == "-W") o.westFunction = integerValue(flag, value);
        else if(flag == "-r") o.adjust = integerValue(flag, value);
        else if(flag == "-j") o.scaleC = numberValue(flag, value);
        else if(flag == "-k") o.transC = numberValue(flag, value);
        else if(flag == "-l") o.scaleD = numberValue(flag, value);
        else if(flag == "-m") o.transD = numberValue(flag, value);
        else if(flag == "-x") o.x = numberValue(flag, value);
        else if(flag == "-y") o.y = numberValue(flag, value);
    }
    return parsed;
}

const char* instanceOptionsHelp()
{
    return R"(Instance (the options of the 2016 zenoSolver, without its swap; see below):
  -n N        central cities (default 3)
  -t N        passengers (default 3)
  -p N        planes (default 2), 1 <= p <= t
  -d FILE     data file: durations then costs (2 lines), or C_I-side
              durations, C_G-side durations, costs (3 lines)
  -C K -D K   generator of costs / durations: 1 log, 2 sqrt, 3 identity (default),
              4 power of two, 5 staircase
  -E K -W K   non-symmetric durations: -E generates the C_I-side durations,
              -W the C_G-side ones
  -r R        multiply before truncating to integers (default 1)
  -j -k       cost generator scale / translation
  -l -m       duration generator scale / translation
  -x -y       output scale / translation of both generators
  -F          accepted for compatibility (the front is always printed)

Each option means what it says, and data files are read as written. The 2016
solvers swapped durations and costs whenever the first duration exceeded the
second, which their generator always did: a 2016 or paper instance
"-C a -D b" is "-C b -D a" here, and "-C c -E a -W b" is "-C a -E c -W b".
)";
}
} // namespace cli
} // namespace zeno
