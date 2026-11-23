// Checks the PDDL problem writer against the domain file in pddl/, and the
// data-file writer against the instance reader.
#include <zeno/io.hpp>
#include <zeno/legacy_input.hpp>

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

    if(failures == 0)
        std::cout << "ut-pddl: all checks passed\n";
    return failures == 0 ? 0 : 1;
}
