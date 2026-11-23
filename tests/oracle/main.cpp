////////////////////////////////////////////////////////////
/// \file main.cpp
/// \brief Brute-force oracle: prints the exact Pareto front of
/// a tiny instance as "cost makespan" lines.
///
/// Accepts the instance options of zeno and builds the instance
/// with the same code (zeno::legacy::buildInstance), so both see
/// identical data. The oracle itself (bruteForce.hpp) shares no
/// code with the solver.
////////////////////////////////////////////////////////////

#include <zeno/io.hpp>
#include <zeno/legacy_input.hpp>

#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

#include "bruteForce.hpp"

int main(int argc, char** argv)
{
    try
    {
        const auto parsed = zeno::cli::parseInstanceArguments(std::vector<std::string>(argv + 1, argv + argc));
        if(!parsed.rest.empty())
            throw std::invalid_argument("unknown option " + parsed.rest.front());
        const zeno::Instance data = zeno::legacy::buildInstance(parsed.options);
        oracle::Instance in;
        in.travelers = static_cast<unsigned>(data.t);
        in.planes = static_cast<unsigned>(data.p);
        for(int i = 0; i < data.n(); ++i)
        {
            in.cost.push_back(data.c[static_cast<std::size_t>(i)]);
            in.west.push_back(data.d[static_cast<std::size_t>(i)]);
            in.east.push_back(data.dbar[static_cast<std::size_t>(i)]);
        }
        for(const auto& point : oracle::paretoFront(in))
            std::cout << point.first << " " << point.second << "\n";
    }
    catch(std::exception& e)
    {
        std::cerr << "Error: " << e.what() << std::endl;
        return 1;
    }
    return 0;
}
