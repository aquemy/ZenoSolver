#include <algorithm>
#include <fstream>
#include <functional>
#include <iterator>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

#include <cli.hpp>
#include <genFunctions.hpp>

using namespace std;

CliArgs::CliArgs(TCLAP::CmdLine& cmd)
    : nArg("n","cities","Number of cities",true,3,"int", cmd)
    , tArg("t","travelers","Number of travelers",true,3,"int", cmd)
    , pArg("p","planes","Number of planes",true,2,"int", cmd)
    , rArg("r","adjustCoef", "Multiplicative coefficient before converting to integers.",false,1,"int", cmd)
    , dArg("d","data","File where data (cost and durations) are located",false,"","string", cmd)
    , aArg("a","pruning","Activate / deactivate the pruning by greedily domination.", cmd, false)
    , GArg("G","generatePDDL","Generate PDDL instance file according to data.", cmd, false)
    , SArg("S","forceSymetric","Force to use the symetric algorithm.", cmd, false)
    , BArg("B","betaMax","Ignore higher beta values.", false, 100, "unsigned", cmd)
    , CArg("C","C","Function to generate C", false, 3, "unsigned", cmd)
    , DArg("D","D","Function to generate D", false, 3, "unsigned", cmd)
    // Taking into account the none symetric case
    , DEArg("E","DE","Function to generate DE", false, 3, "unsigned", cmd)
    , DWArg("W","DW","Function to generate DW", false, 3, "unsigned", cmd)
    , ScArg("j","scaleC","Scale factor for C", false, 1, "unsigned", cmd)
    , TcArg("k","transC","Translation factor for C", false, 0, "unsigned", cmd)
    , SdArg("l","scaleD","Scale factor for D", false, 1, "unsigned", cmd)
    , TdArg("m","transD","Translation factor for D", false, 0, "unsigned", cmd)
    , xArg("x","x","Scale factor for D", false, 1, "unsigned", cmd)
    , yArg("y","y","Translation factor for D", false, 0, "unsigned", cmd)
    , genPlan("P","generatePlan","Output the pareto-optimal plans.", cmd, false)
    , FArg("F","printFront","Print the Pareto front as 'cost makespan' lines on stdout.", cmd, false)
    , OArg("O","ouput","Output file for PDDL File", false,"", "string", cmd)
{
}

InstanceData buildInstance(CliArgs& args)
{
    // 1. DATA
    // 1.1 CMD verification
    if(args.nArg.getValue() < 0)
        throw std::domain_error("Number of cities (n) must be positive.");
    if(args.tArg.getValue() < 1)
        throw std::domain_error("Number of passengers (t) must be > 0.");
    if(args.pArg.getValue() < 1)
        throw std::domain_error("Number of planes (p) must be > 0.");
    if(args.tArg.getValue() - args.pArg.getValue() < 1)
        throw std::domain_error("Number of passengers must be strictly higher than the number of planes.");

    unsigned n = args.nArg.getValue();
    unsigned t = args.tArg.getValue();
    unsigned p = args.pArg.getValue();

    // 1.2 Costs and durations
    vector<double> c(n,1);
    vector<double> d(n,1);
    vector<double> de(n,1); // East durations in case the problem is not symetric
    auto symetric = false;

    if(!args.dArg.getValue().empty())
    {
        ifstream dataFile(args.dArg.getValue());
        if(!dataFile)
            throw std::runtime_error("Can't open the data file: "+args.dArg.getValue());

        // One vector of n integers per non-empty line:
        //   2 lines: durations, costs (symetric problem);
        //   3 lines: west durations, east durations, costs.
        vector<vector<double>> rows;
        string s;
        while(getline(dataFile, s))
        {
            istringstream iss(s);
            vector<string> tokens{istream_iterator<string>{iss}, istream_iterator<string>{}};
            if(tokens.empty())
                continue;
            if(tokens.size() != n)
                throw std::runtime_error("The data file is not valid. Check the length of the vectors.");
            vector<double> row(n);
            for(unsigned i = 0; i < n; ++i)
                row[i] = stoi(tokens[i]);
            rows.push_back(row);
        }

        if(rows.size() == 2)
        {
            d = rows[0];
            de = rows[0];
            c = rows[1];
            symetric = true;
        }
        else if(rows.size() == 3)
        {
            d = rows[0];
            de = rows[1];
            c = rows[2];
        }
        else
            throw std::runtime_error("The data file is not valid. Expected 2 lines (durations, costs) "
                                     "or 3 lines (west durations, east durations, costs).");
    }
    else
    {
        auto f = f3;
        auto g = f3;
        auto h = f3;
        switch (args.CArg.getValue())
        {
            case 1:
                f = f1;
                break;
            case 2:
                f = f2;
                break;
            case 3:
                f = f3;
                break;
            case 4:
                f = f4;
                break;
            case 5:
                f = f5;
                break;
        }
        if(args.DEArg.isSet() and args.DWArg.isSet())
        {
            switch (args.DEArg.getValue())
            {
                case 1:
                    g = f1;
                    break;
                case 2:
                    g = f2;
                    break;
                case 3:
                    g = f3;
                    break;
                case 4:
                    g = f4;
                    break;
                case 5:
                    g = f5;
                    break;
            }
            switch (args.DWArg.getValue())
            {
                case 1:
                    h = f1;
                    break;
                case 2:
                    h = f2;
                    break;
                case 3:
                    h = f3;
                    break;
                case 4:
                    h = f4;
                    break;
                case 5:
                    h = f5;
                    break;
            }
        }
        else {
            symetric = true;
            switch (args.DArg.getValue())
            {
                case 1:
                    g = f1;
                    break;
                case 2:
                    g = f2;
                    break;
                case 3:
                    g = f3;
                    break;
                case 4:
                    g = f4;
                    break;
                case 5:
                    g = f5;
                    break;
            }
        }
        // Generate data
        apply(c, f, args.xArg.getValue(), args.yArg.getValue(), args.ScArg.getValue(), args.TcArg.getValue());
        rapply(d, g, args.xArg.getValue(), args.yArg.getValue(), args.SdArg.getValue(), args.TdArg.getValue());
        if(!symetric)
            rapply(de, h, args.xArg.getValue(), args.yArg.getValue(), args.SdArg.getValue(), args.TdArg.getValue());
    }

    // Convert to int
    for(auto& i : c)
        i = (int)(args.rArg.getValue()*i);

    for(auto& i : d)
        i = (int)(args.rArg.getValue()*i);

    for(auto& i : de)
        i = (int)(args.rArg.getValue()*i);

    // Assuming d and c are strictly monoteneous, d must be decreasing for the algorithm
    // TODO: Take into account non-symetric cases
    if(n > 1 && d[0] > d[1]) {
        swap(d,c);
        std::reverse(std::begin(de), std::end(de));
    }


    if(symetric)
        de = d;

    InstanceData instance;
    instance.n = n;
    instance.t = t;
    instance.p = p;
    instance.c = c;
    instance.d = d;
    instance.de = de;
    instance.symetric = symetric;
    return instance;
}
