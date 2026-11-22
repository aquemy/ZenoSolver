////////////////////////////////////////////////////////////
/// \file main.cpp
/// \brief Brute-force oracle: prints the exact Pareto front of
/// a tiny instance as "cost makespan" lines.
///
/// Accepts the same options as the solvers and builds the
/// instance with the same code, so both see identical data.
////////////////////////////////////////////////////////////

#include <cmath>
#include <iostream>
#include <stdexcept>

#include <cli.hpp>

#include "bruteForce.hpp"

namespace {

oracle::Int toInt(double v)
{
    if(v != std::floor(v))
        throw std::runtime_error("oracle: instance data is not integral");
    return static_cast<oracle::Int>(v);
}

} // namespace

int main(int argc, char** argv)
{
    try
    {
        TCLAP::CmdLine cmd("ZenoSolver brute-force oracle", ' ', "0.9");
        CliArgs args(cmd);
        cmd.parse(argc, argv);

        const auto data = buildInstance(args);
        oracle::Instance in;
        in.travelers = data.t;
        in.planes = data.p;
        for(unsigned i = 0; i < data.n; ++i)
        {
            in.cost.push_back(toInt(data.c[i]));
            in.west.push_back(toInt(data.d[i]));
            in.east.push_back(toInt(data.de[i]));
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
