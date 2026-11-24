// Checks the PDDL problem writer against the domain file in pddl/, the
// data-file writer against the instance reader, and the metric generator.
#include <zeno/io.hpp>
#include <zeno/legacy_input.hpp>
#include <zeno/metric.hpp>

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <regex>
#include <set>
#include <sstream>
#include <string>

namespace
{
int failures = 0;

void check(bool ok, const std::string& what)
{
    if(!ok)
    {
        std::cerr << "FAIL: " << what << "\n";
        ++failures;
    }
}

std::string slurp(const std::filesystem::path& path)
{
    std::ifstream in(path);
    std::stringstream ss;
    ss << in.rdbuf();
    return ss.str();
}

// Drop ';' comments so that the structural checks only see PDDL.
std::string stripComments(const std::string& text)
{
    std::string out;
    std::istringstream in(text);
    for(std::string line; std::getline(in, line);)
        out += line.substr(0, line.find(';')) + "\n";
    return out;
}

bool balanced(const std::string& text)
{
    int depth = 0;
    for(char ch : text)
    {
        depth += ch == '(' ? 1 : ch == ')' ? -1 : 0;
        if(depth < 0)
            return false;
    }
    return depth == 0;
}

// The line after the comment "; <label> :".
std::string commentAfter(const std::string& text, const std::string& label)
{
    std::istringstream in(text);
    for(std::string line; std::getline(in, line);)
        if(line.rfind("; " + label, 0) == 0 && std::getline(in, line))
            return line;
    return {};
}

std::set<std::string> matches(const std::string& text, const std::regex& re)
{
    std::set<std::string> out;
    for(auto it = std::sregex_iterator(text.begin(), text.end(), re); it != std::sregex_iterator(); ++it)
        out.insert((*it)[1]);
    return out;
}

std::size_t at(int v) { return static_cast<std::size_t>(v); }

// Every flight of an instance over C_I = 0, the central cities 1..n and
// C_G = n + 1, with -1 for C_I - C_G (no flight). Written without the
// library's centralFlight, so the checks below do not trust it.
std::vector<std::vector<zeno::Time>> flightMatrix(const zeno::Instance& in)
{
    const int n = in.n(), m = n + 2;
    std::vector<std::vector<zeno::Time>> w(at(m), std::vector<zeno::Time>(at(m), 0));
    for(int i = 1; i <= n; ++i)
    {
        w[0][at(i)] = w[at(i)][0] = in.d[at(i - 1)];
        w[at(n + 1)][at(i)] = w[at(i)][at(n + 1)] = in.dbar[at(i - 1)];
        for(int j = 1; j <= n; ++j)
            w[at(i)][at(j)] = (*in.central)[at(i - 1)][at(j - 1)];
    }
    w[0][at(n + 1)] = w[at(n + 1)][0] = -1;
    return w;
}

// (AΔ): dur(a, b) <= dur(a, x) + dur(x, b) whenever the three flights exist.
bool triangleInequality(const std::vector<std::vector<zeno::Time>>& w)
{
    const auto m = w.size();
    for(std::size_t a = 0; a < m; ++a)
        for(std::size_t b = 0; b < m; ++b)
            for(std::size_t x = 0; x < m; ++x)
                if(a != b && x != a && x != b && w[a][b] >= 0 && w[a][x] >= 0 && w[x][b] >= 0 && w[a][b] > w[a][x] + w[x][b])
                    return false;
    return true;
}

std::filesystem::path writeTemp(const std::string& name, const std::string& text)
{
    const auto path = std::filesystem::temp_directory_path() / name;
    std::ofstream out(path);
    out << text;
    return path;
}

zeno::Instance readBack(const zeno::Instance& instance, const std::string& name)
{
    const auto path = std::filesystem::temp_directory_path() / name;
    {
        std::ofstream out(path);
        zeno::writeDataFile(out, instance);
    }
    zeno::legacy::Options options;
    options.n = instance.n();
    options.t = instance.t;
    options.p = instance.p;
    options.dataFile = path.string();
    const zeno::Instance back = zeno::legacy::buildInstance(options);
    std::filesystem::remove(path);
    return back;
}

bool sameInstance(const zeno::Instance& a, const zeno::Instance& b)
{
    return a.d == b.d && a.dbar == b.dbar && a.c == b.c && a.t == b.t && a.p == b.p && a.central == b.central;
}

template<class F>
bool throws(F&& f)
{
    try
    {
        f();
    }
    catch(const std::exception&)
    {
        return true;
    }
    return false;
}

// Metric instances: (AΔ) holds exactly after rounding, (S) with one hub, the
// table survives the data file and reaches the PDDL problem.
void testMetric()
{
    using zeno::metric::Geometry;
    using zeno::metric::Hubs;
    int instances = 0, brokenByRounding = 0, apartSymmetric = 0;
    for(Geometry geometry : {Geometry::Plane, Geometry::Sphere})
        for(Hubs hubs : {Hubs::Same, Hubs::Apart})
            for(double scale : geometry == Geometry::Plane ? std::vector<double>{0.03, 0.1, 0.37, 1, 13} : std::vector<double>{0.0003, 0.001, 0.0047, 0.03, 1})
                for(std::uint64_t seed = 1; seed <= 60; ++seed)
                {
                    zeno::legacy::Options base;
                    base.n = 2 + static_cast<int>(seed % 7);
                    base.t = 4;
                    base.p = 2;
                    base.adjust = scale;
                    zeno::metric::Options m;
                    m.geometry = geometry;
                    m.hubs = hubs;
                    m.seed = seed;
                    const zeno::Instance in = zeno::metric::buildInstance(base, m);
                    ++instances;
                    const std::string where = std::string(geometry == Geometry::Plane ? "plane" : "sphere") + (hubs == Hubs::Same ? " same" : " apart") +
                                              " r=" + std::to_string(scale) + " seed=" + std::to_string(seed);
                    check(in.central.has_value() && in.n() == base.n, "metric instances carry a table: " + where);
                    check(triangleInequality(flightMatrix(in)), "metric table satisfies (AΔ) after rounding: " + where);
                    if(hubs == Hubs::Same)
                        check(in.symmetric(), "--hubs same gives symmetric durations (S): " + where);
                    else
                        apartSymmetric += in.symmetric();

                    // No duration exceeds its rounded distance, and rounding alone
                    // would break (AΔ) on some instances (so the closure is tested).
                    const auto layout = zeno::metric::randomLayout(geometry, hubs, base.n, seed);
                    zeno::Instance rounded = in;
                    const auto round = [&](const zeno::metric::Point& a, const zeno::metric::Point& b) {
                        return static_cast<zeno::Time>(std::llround(scale * zeno::metric::distance(geometry, a, b)));
                    };
                    bool below = true;
                    for(int i = 0; i < base.n; ++i)
                    {
                        rounded.d[at(i)] = round(layout.hubs.front(), layout.cities[at(i)]);
                        rounded.dbar[at(i)] = round(layout.hubs.back(), layout.cities[at(i)]);
                        below = below && in.d[at(i)] <= rounded.d[at(i)] && in.dbar[at(i)] <= rounded.dbar[at(i)];
                        for(int j = 0; j < base.n; ++j)
                        {
                            (*rounded.central)[at(i)][at(j)] = round(layout.cities[at(i)], layout.cities[at(j)]);
                            below = below && (*in.central)[at(i)][at(j)] <= (*rounded.central)[at(i)][at(j)];
                        }
                    }
                    check(below, "the closure never lengthens a flight: " + where);
                    brokenByRounding += !triangleInequality(flightMatrix(rounded));

                    // Data file round trip, table included.
                    check(sameInstance(readBack(in, "zeno-ut-metric.dat"), in), "metric data file round trip: " + where);
                }
    check(brokenByRounding > 0, "rounding breaks (AΔ) on some instances before the closure");
    check(apartSymmetric < instances / 8, "--hubs apart gives non-symmetric durations");
    std::cout << "ut-pddl: " << instances << " metric instances satisfy (AΔ); rounding alone broke it on " << brokenByRounding << "\n";

    // The same seed gives the same cities and C_I with either hub mode.
    {
        const auto same = zeno::metric::randomLayout(Geometry::Plane, Hubs::Same, 5, 42);
        const auto apart = zeno::metric::randomLayout(Geometry::Plane, Hubs::Apart, 5, 42);
        bool equal = same.hubs.size() == 1 && apart.hubs.size() == 2 && same.hubs[0].x == apart.hubs[0].x && same.hubs[0].y == apart.hubs[0].y;
        for(std::size_t i = 0; i < 5; ++i)
            equal = equal && same.cities[i].x == apart.cities[i].x && same.cities[i].y == apart.cities[i].y;
        check(equal, "--hubs apart only adds C_G");
        bool inside = true;
        for(const auto& point : same.cities)
            inside = inside && point.x >= 0 && point.x <= zeno::metric::kSquareSide && point.y >= 0 && point.y <= zeno::metric::kSquareSide;
        check(inside, "plane points lie in the square");
    }

    // The command line: --metric with -C costs, then the data file and the PDDL problem.
    {
        const auto parsed = zeno::cli::parseInstanceArguments({"-n", "6", "-t", "5", "-p", "3", "--metric", "plane", "--seed", "7", "-r", "0.2", "-C", "2", "--plans"});
        check(parsed.metric.has_value() && parsed.metric->seed == 7 && parsed.rest == std::vector<std::string>{"--plans"}, "--metric options parsed");
        const zeno::Instance in = zeno::cli::buildInstance(parsed);
        check(in.c == std::vector<zeno::Cost>{1, 1, 1, 2, 2, 2}, "--metric costs come from -C, not scaled by -r");
        check(sameInstance(zeno::cli::buildInstance(parsed), in), "the same seed gives the same instance");
        check(sameInstance(readBack(in, "zeno-ut-cli.dat"), in), "--metric data file round trip");

        std::ostringstream text;
        zeno::writePddlProblem(text, in);
        const std::string body = stripComments(text.str());
        bool table = true;
        for(int i = 1; i <= in.n(); ++i)
            for(int j = 1; j <= in.n(); ++j)
                if(i != j)
                    table = table && body.find("(= (timeTerre city" + std::to_string(i) + " city" + std::to_string(j) + ") " +
                                               std::to_string((*in.central)[at(i - 1)][at(j - 1)]) + ")") != std::string::npos;
        check(table, "the PDDL problem uses the central-flight table");
        check(body.find("(= (timeTerre city0 city1) " + std::to_string(in.d[0]) + ")") != std::string::npos, "metric hub leg in PDDL");
        check(text.str().find("; Central flights : ") != std::string::npos, "PDDL comments list the table");

        const auto randomCosts = zeno::cli::buildInstance(
            zeno::cli::parseInstanceArguments({"-n", "40", "--metric", "sphere", "--hubs", "apart", "--random-costs", "3,9", "-r", "0.01"}));
        check(std::ranges::all_of(randomCosts.c, [](zeno::Cost c) { return c >= 3 && c <= 9; }) &&
                  std::ranges::find(randomCosts.c, 3) != randomCosts.c.end() && std::ranges::find(randomCosts.c, 9) != randomCosts.c.end(),
              "--random-costs draws in [LO, HI]");
        check(!randomCosts.symmetric(), "--hubs apart is non-symmetric");
    }

    // Coordinates files: labels, comments, commas or spaces; great-circle distances.
    {
        const auto path = writeTemp("zeno-ut-airports.csv", "# airport,lat,lon\nCDG,49.0097,2.5479\n\nLHR, 51.4700, -0.4543\nJFK 40.6413 -73.7781\n35.7720,140.3929\n");
        const auto layout = zeno::metric::readLayout(path.string(), Geometry::Sphere, Hubs::Same);
        check(layout.hubs.size() == 1 && layout.cities.size() == 3, "coordinates file: the hub, then the cities");
        const double cdgJfk = zeno::metric::distance(Geometry::Sphere, layout.hubs[0], layout.cities[1]);
        const double cdgLhr = zeno::metric::distance(Geometry::Sphere, layout.hubs[0], layout.cities[0]);
        check(std::abs(cdgJfk - 5833.5) < 1 && std::abs(cdgLhr - 347.0) < 1, "great-circle distances in km");
        const auto parsed = zeno::cli::parseInstanceArguments({"-n", "3", "-t", "3", "-p", "2", "--metric", "sphere", "--coords", path.string(), "-r", "0.01"});
        const zeno::Instance in = zeno::cli::buildInstance(parsed);
        check(in.d == std::vector<zeno::Time>{3, 58, 97} && in.symmetric(), "--coords durations, in units of 100 km");
        check((*in.central)[0][1] == 55 && (*in.central)[1][2] == 108 && triangleInequality(flightMatrix(in)), "--coords central flights");
        check(throws([&] { (void)zeno::cli::buildInstance(zeno::cli::parseInstanceArguments({"-n", "4", "--metric", "sphere", "--coords", path.string()})); }),
              "--coords needs -n to match the file");
        const auto apart = zeno::metric::readLayout(path.string(), Geometry::Sphere, Hubs::Apart);
        check(apart.hubs.size() == 2 && apart.cities.size() == 2, "coordinates file with two hubs");
        std::filesystem::remove(path);
        const auto bad = writeTemp("zeno-ut-bad.csv", "0,0\n1,x\n");
        check(throws([&] { (void)zeno::metric::readLayout(bad.string(), Geometry::Plane, Hubs::Same); }), "malformed coordinates are rejected");
        std::filesystem::remove(bad);
    }

    // Option errors.
    check(throws([] { (void)zeno::cli::parseInstanceArguments({"--seed", "3"}); }), "--seed needs --metric");
    check(throws([] { (void)zeno::cli::parseInstanceArguments({"--metric", "plane", "-D", "2"}); }), "--metric rejects -D");
    check(throws([] { (void)zeno::cli::parseInstanceArguments({"--metric", "plane", "-d", "file"}); }), "--metric rejects -d");
    check(throws([] { (void)zeno::cli::parseInstanceArguments({"--metric", "torus"}); }), "--metric takes plane or sphere");
    check(throws([] { (void)zeno::cli::parseInstanceArguments({"--metric", "plane", "--hubs", "both"}); }), "--hubs takes same or apart");
    check(throws([] { (void)zeno::cli::parseInstanceArguments({"--metric", "plane", "--random-costs", "5,2"}); }), "--random-costs needs LO <= HI");
    check(throws([] { (void)zeno::cli::buildInstance(zeno::cli::parseInstanceArguments({"--metric", "plane", "-r", "0"})); }), "--metric needs -r > 0");
}

// The central block of data files: read, validated, round-tripped.
void testCentralBlock()
{
    const auto path = writeTemp("zeno-ut-central.dat", "2 3 9 11\n50 44 17 0\ncentral\n0 1 5 6\n1 0 3 6\n5 3 0 1\n6 6 1 0\n");
    zeno::legacy::Options options;
    options.n = 4;
    options.t = 6;
    options.p = 3;
    options.dataFile = path.string();
    const zeno::Instance in = zeno::legacy::buildInstance(options);
    check(in.symmetric() && in.c == std::vector<zeno::Cost>{50, 44, 17, 0}, "data file with a table: durations and costs");
    check(in.central && (*in.central)[0][3] == 6 && (*in.central)[2][3] == 1 && in.centralFlight(3, 2) == 1, "data file with a table: the table");
    check(sameInstance(readBack(in, "zeno-ut-central-back.dat"), in), "table round trip");
    options.adjust = 10;
    const zeno::Instance scaled = zeno::legacy::buildInstance(options);
    check(scaled.central && (*scaled.central)[0][1] == 10 && scaled.d[0] == 20, "-r scales the table like the durations");
    std::filesystem::remove(path);

    for(const char* bad : {"1 2\n3 4\ncentral\n0 1\n2 0\n", "1 2\n3 4\ncentral\n1 1\n1 0\n", "1 2\n3 4\ncentral\n0 1\n", "1 2\n3 4\ncentral\n0 1\n1 0\ncentral\n"})
    {
        const auto file = writeTemp("zeno-ut-bad.dat", bad);
        zeno::legacy::Options o;
        o.n = 2;
        o.dataFile = file.string();
        check(throws([&] { (void)zeno::legacy::buildInstance(o); }), std::string("invalid table rejected: ") + bad);
        std::filesystem::remove(file);
    }
}
} // namespace

int main()
{
    zeno::Instance in;
    in.d = {2, 4, 6};
    in.dbar = in.d;
    in.c = {30, 20, 10};
    in.t = 4;
    in.p = 2;
    const zeno::Front front{{120, 24}, {90, 36}};

    std::ostringstream written;
    zeno::writePddlProblem(written, in, &front);
    const std::string problem = written.str();
    const std::string body = stripComments(problem);

    check(!problem.empty(), "the problem file is written");
    check(balanced(body), "parentheses are balanced");

    // Goals: every person and every plane in C_G = city(n+1).
    const std::string goals = body.substr(body.find("(:goal"));
    for(int i = 1; i <= in.t; ++i)
        check(goals.find("(at person" + std::to_string(i) + " city4)") != std::string::npos, "goal for person" + std::to_string(i));
    for(int i = 1; i <= in.p; ++i)
        check(goals.find("(at plane" + std::to_string(i) + " city4)") != std::string::npos, "goal for plane" + std::to_string(i));

    // Landing costs and flight durations.
    check(body.find("(= (citythreat city1) 30)") != std::string::npos, "landing cost of city1");
    check(body.find("(= (citythreat city4) 0)") != std::string::npos, "landing cost of C_G is 0");
    check(body.find("(= (timeTerre city0 city2) 4)") != std::string::npos, "flight C_I -> city2");
    check(body.find("(= (timeTerre city3 city4) 6)") != std::string::npos, "flight city3 -> C_G");
    check(body.find("(= (timeTerre city1 city3) 108)") != std::string::npos, "central flight city1 -> city3");
    check(body.find("timeTerre city0 city4") == std::string::npos, "no direct flight C_I -> C_G");

    // Trailing comments: labels match their values, front as "makespan cost".
    check(commentAfter(problem, "Durations") == "; 2 4 6 ", "durations comment");
    check(commentAfter(problem, "Costs") == "; 30 20 10 ", "costs comment");
    check(problem.find("; 36 90\n") != std::string::npos && problem.find("; 24 120\n") != std::string::npos, "front comment");

    // The problem only uses predicates and functions declared by the domain.
    const std::string domain = stripComments(slurp(std::filesystem::path(ZS_PDDL_DIR) / "multi-zeno-travel.pddl"));
    check(balanced(domain), "domain parentheses are balanced");
    check(domain.find("(domain multi-zeno-travel)") != std::string::npos, "domain name");
    check(body.find("(:domain  multi-zeno-travel)") != std::string::npos, "problem refers to the domain");
    const std::regex used(R"(\((at|libre|citythreat|timeTerre|total-cost|in)[ )])");
    const std::set<std::string> declared = matches(domain, used);
    for(const auto& symbol : matches(body, used))
        check(declared.contains(symbol), "domain declares " + symbol);

    // Non-symmetric durations: C_I legs use d, C_G legs use dbar, central
    // flights max(d_i, dbar_i) + max(d_j, dbar_j) + 100.
    zeno::Instance ns = in;
    ns.dbar = {5, 1, 7};
    std::ostringstream nsText;
    zeno::writePddlProblem(nsText, ns);
    const std::string nsBody = stripComments(nsText.str());
    check(nsBody.find("(= (timeTerre city0 city1) 2)") != std::string::npos, "non-symmetric C_I leg");
    check(nsBody.find("(= (timeTerre city1 city4) 5)") != std::string::npos, "non-symmetric C_G leg");
    check(nsBody.find("(= (timeTerre city2 city3) 111)") != std::string::npos, "non-symmetric central flight");
    check(commentAfter(nsText.str(), "Durations (C_G side)") == "; 5 1 7 ", "non-symmetric durations comment");

    // Data files round-trip through the reader of -d.
    for(const zeno::Instance& instance : {in, ns})
    {
        const auto path = std::filesystem::temp_directory_path() / "zeno-ut-pddl.dat";
        {
            std::ofstream out(path);
            zeno::writeDataFile(out, instance);
        }
        zeno::legacy::Options options;
        options.n = instance.n();
        options.t = instance.t;
        options.p = instance.p;
        options.dataFile = path.string();
        const zeno::Instance back = zeno::legacy::buildInstance(options);
        std::filesystem::remove(path);
        check(back.d == instance.d && back.dbar == instance.dbar && back.c == instance.c, "data file round trip");
    }

    // Data files are read as written, even with decreasing durations (the 2016
    // solvers swapped durations and costs then; zeno does not).
    {
        const auto path = std::filesystem::temp_directory_path() / "zeno-ut-swap.dat";
        {
            std::ofstream out(path);
            out << "9 2 9 9\n8 7 8 3\n14 13 17 15\n";
        }
        zeno::legacy::Options options;
        options.n = 4;
        options.t = 4;
        options.p = 2;
        options.dataFile = path.string();
        const zeno::Instance literal = zeno::legacy::buildInstance(options);
        check(literal.d == std::vector<zeno::Time>{9, 2, 9, 9} && literal.dbar == std::vector<zeno::Time>{8, 7, 8, 3}
                  && literal.c == std::vector<zeno::Cost>{14, 13, 17, 15},
              "data file read as written");
        std::filesystem::remove(path);
    }

    // Generator options mean what they say, and `zeno generate` output reads
    // back as the same instance.
    {
        const auto roundTrip = [&](const zeno::legacy::Options& generated, const char* what) {
            const zeno::Instance instance = zeno::legacy::buildInstance(generated);
            const auto path = std::filesystem::temp_directory_path() / "zeno-ut-generate.dat";
            {
                std::ofstream out(path);
                zeno::writeDataFile(out, instance);
            }
            zeno::legacy::Options read;
            read.n = generated.n;
            read.t = generated.t;
            read.p = generated.p;
            read.dataFile = path.string();
            const zeno::Instance back = zeno::legacy::buildInstance(read);
            std::filesystem::remove(path);
            check(back.d == instance.d && back.dbar == instance.dbar && back.c == instance.c, what);
            return instance;
        };
        zeno::legacy::Options sym;
        sym.n = 5;
        sym.t = 4;
        sym.p = 2;
        sym.costFunction = 2;
        sym.durationFunction = 4;
        sym.adjust = 10;
        const zeno::Instance generated = roundTrip(sym, "generate round trip (symmetric)");
        // -D 4 (2^i) at l (n + 1 - i): durations 2^5, ..., 2^1 times 10; -C 2 (sqrt i) times 10, truncated.
        check(generated.d == std::vector<zeno::Time>{320, 160, 80, 40, 20}, "-D sets the durations");
        check(generated.c == std::vector<zeno::Cost>{10, 14, 17, 20, 22}, "-C sets the costs");

        zeno::legacy::Options ns = sym;
        ns.costFunction = 3;
        ns.eastFunction = 1;
        ns.westFunction = 3;
        ns.adjust = 100;
        const zeno::Instance nonSymmetric = roundTrip(ns, "generate round trip (-E -W)");
        check(!nonSymmetric.symmetric(), "-E 1 -W 3 is non-symmetric");
        check(nonSymmetric.dbar == std::vector<zeno::Time>{500, 400, 300, 200, 100}, "-W sets the C_G side");
        check(nonSymmetric.c == std::vector<zeno::Cost>{100, 200, 300, 400, 500}, "-C sets the costs");
    }

    // Without a table, nothing changes: no central block in the data file.
    {
        std::ostringstream text;
        zeno::writeDataFile(text, in);
        check(text.str() == "2 4 6\n30 20 10\n", "default instances keep the 2-line data file");
    }
    testMetric();
    testCentralBlock();

    if(failures == 0)
        std::cout << "ut-pddl: all checks passed\n";
    return failures == 0 ? 0 : 1;
}
