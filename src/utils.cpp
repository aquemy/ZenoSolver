#include <iostream>
#include <fstream>
#include <iomanip>
#include <vector>
#include <functional>
#include <utils.hpp>
#include <map>

void debugPrint(std::string title, std::function<void(void)> f)
{
    std::cerr << std::setfill('=') << std::setw(42) << "=" << std::endl;
    std::cerr << "==" << std::setfill(' ') << std::setw((38 - title.size()) / 2 + 1) << " ";
    std::cerr << title;
    std::cerr << std::setfill(' ') << std::setw((38 - title.size()) / 2 + 1) << "==" << std::endl;
    std::cerr << std::setfill('=') << std::setw(42) << "=" << std::endl;
    f();
}

bool isReadable(const std::string& path) 
{ 
    std::ifstream file(path.c_str()); 
    return !file.fail(); 
}

void generatePDDL(std::string path, unsigned n, unsigned t, unsigned p, const std::vector<double>& c, const std::vector<double>& d, const std::map<int,int>& pareto)
{
    std::ofstream dataFile(path);
    if(!dataFile)
        return;

    // Objects: city0 is C_I, city1..cityn the central cities, city(n+1) is C_G.
    const unsigned goal = n + 1;
    const char* indent = "         ";
    dataFile << "(define (problem MULTIZENO-A)" << std::endl;
    dataFile << "  (:domain  multi-zeno-travel)" << std::endl;
    dataFile << "  (:objects ";
    for(unsigned i = 1; i < p+1; i++)
        dataFile << "plane" << i << " ";
    dataFile << "- aircraft" << std::endl << "            ";
    for(unsigned i = 1; i < t+1; i++)
        dataFile << "person" << i << " ";
    dataFile << "- person" << std::endl << "            ";
    for(unsigned i = 0; i < n+2; i++)
        dataFile << "city" << i << " ";
    dataFile << "- city)" << std::endl;

    dataFile << "  (:init (= (total-cost) 0)" << std::endl << indent;
    dataFile << "(= (citythreat city0) 0)" << std::endl << indent;
    for(unsigned i = 1; i < n+1; i++)
        dataFile << "(= (citythreat city" << i << ") " << c[i-1] << ")" << std::endl << indent;
    dataFile << "(= (citythreat city" << goal << ") 0)" << std::endl << indent;

    // Flights of central city i: to and from C_I and C_G (duration d_i), and to
    // every other central city j (d_i + d_j + 100, so that a direct central
    // flight is never faster than going through C_I or C_G).
    for(unsigned i = 1; i < n+1; i++)
    {
        dataFile << std::endl << "; city" << i << std::endl << indent;
        dataFile << "(= (timeTerre city0 city" << i << ") " << d[i-1] << ")" << std::endl << indent;
        dataFile << "(= (timeTerre city" << i << " city0) " << d[i-1] << ")" << std::endl << indent;
        dataFile << "(= (timeTerre city" << goal << " city" << i << ") " << d[i-1] << ")" << std::endl << indent;
        dataFile << "(= (timeTerre city" << i << " city" << goal << ") " << d[i-1] << ")" << std::endl << indent;
        for(unsigned j = 1; j < n+1; j++)
            if(i != j)
                dataFile << "(= (timeTerre city" << i << " city" << j << ") " << d[i-1]+d[j-1]+100 << ")" << std::endl << indent;
    }

    dataFile << std::endl << "; plane init" << std::endl << indent;
    for(unsigned i = 1; i < p+1; i++)
        dataFile << "(at plane" << i << " city0)" << std::endl << indent;
    for(unsigned i = 1; i < p+1; i++)
        dataFile << "(libre plane" << i << ")" << std::endl << indent;

    dataFile << std::endl << "; person init" << std::endl << indent;
    for(unsigned i = 1; i < t+1; i++)
        dataFile << "(at person" << i << " city0)" << std::endl << indent;

    // Every person and every plane must end in C_G.
    dataFile << std::endl << ")" << std::endl << "(:goal (and " << std::endl << indent;
    for(unsigned i = 1; i < t+1; i++)
        dataFile << "(at person" << i << " city" << goal << ")" << std::endl << indent;
    for(unsigned i = 1; i < p+1; i++)
        dataFile << "(at plane" << i << " city" << goal << ")" << std::endl << indent;
    dataFile << "))" << std::endl;

    dataFile << "  (:metric (and (minimize (total-time)) (minimize (total-cost)))))" << std::endl;

    dataFile << std::endl << "; Durations : " << std::endl << "; ";
    for(auto i : d)
        dataFile << i << " ";
    dataFile << std::endl << "; Costs : " << std::endl << "; ";
    for(auto i : c)
        dataFile << i << " ";

    if(pareto.size() > 0)
    {
        dataFile << std::endl << "; Pareto points : Makespan - Cost" << std::endl;
        for(auto& i : pareto)
            dataFile << "; " << i.second << " " << i.first << std::endl;
    }
}

void generatePDDLPlan(std::string path, unsigned n, unsigned t, unsigned p, const std::vector<double>& c, const std::vector<double>& d, const std::map<int, Plan>& pareto)
{
    auto converted = std::map<int,int>{};
    for(auto i: pareto) {
        converted[i.first] = i.second.m;
    }
    generatePDDL(path, n, t, p, c, d, converted);
}

