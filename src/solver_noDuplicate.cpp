#include <iostream>
#include <sstream>
#include <string>
#include <vector>
#include <map>
#include <set>
#include <algorithm>
#include <iterator>
#include <functional>
#include <fstream>
#include <chrono>
#include <random>
#include <ctime>

#ifdef _OPENMP
#include <omp.h>
#endif // _OPENMP

//#define DEBUG

#include <tclap/CmdLine.h>
#include <combiGenerator.hpp>
#include <powerSetGenerator.hpp>
#include <algorithm.hpp>
#include <paretoExtraction.hpp>
#include <genFunctions.hpp>
#include <utils.hpp>

using namespace std;
using std::chrono::high_resolution_clock;
using std::chrono::milliseconds;


int main(int argc, char** argv)
{
    try
  	{
        TCLAP::CmdLine cmd("ZenoSolver", ' ', "0.9");

  	    TCLAP::ValueArg<int> nArg("n","cities","Number of cities",true,3,"int", cmd);
        TCLAP::ValueArg<int> tArg("t","travelers","Number of travelers",true,3,"int", cmd);
        TCLAP::ValueArg<int> pArg("p","planes","Number of planes",true,2,"int", cmd);
        TCLAP::ValueArg<int> rArg("r","adjustCoef", "Multiplicative coefficient before converting to integers.",false,1,"int", cmd);
        TCLAP::ValueArg<string> dArg("d","data","File where data (cost and durations) are located",false,"","string", cmd);
        TCLAP::SwitchArg aArg("a","pruning","Activate / deactivate the pruning by greedily domination.", cmd, false);
        TCLAP::SwitchArg GArg("G","generatePDDL","Generate PDDL instance file according to data.", cmd, false);
        TCLAP::SwitchArg SArg("S","forceSymetric","Force to use the symetric algorithm.", cmd, false);
        TCLAP::ValueArg<unsigned> BArg("B","betaMax","Ignore higher beta values.", false, 100, "unsigned", cmd);
        TCLAP::ValueArg<unsigned> CArg("C","C","Function to generate C", false, 3, "unsigned", cmd);
        TCLAP::ValueArg<unsigned> DArg("D","D","Function to generate D", false, 3, "unsigned", cmd);
        // Taking into account the none symetric case
        TCLAP::ValueArg<unsigned> DEArg("E","DE","Function to generate DE", false, 3, "unsigned", cmd);
        TCLAP::ValueArg<unsigned> DWArg("W","DW","Function to generate DW", false, 3, "unsigned", cmd);
        TCLAP::ValueArg<double> ScArg("j","scaleC","Scale factor for C", false, 1, "unsigned", cmd);
        TCLAP::ValueArg<double> TcArg("k","transC","Translation factor for C", false, 0, "unsigned", cmd);
        TCLAP::ValueArg<double> SdArg("l","scaleD","Scale factor for D", false, 1, "unsigned", cmd);
        TCLAP::ValueArg<double> TdArg("m","transD","Translation factor for D", false, 0, "unsigned", cmd);

        TCLAP::ValueArg<double> xArg("x","x","Scale factor for D", false, 1, "unsigned", cmd);
        TCLAP::ValueArg<double> yArg("y","y","Translation factor for D", false, 0, "unsigned", cmd);

        TCLAP::SwitchArg genPlan("P","generatePlan","Output the pareto-optimal plans.", cmd, false);

        TCLAP::ValueArg<string> OArg("O","ouput","Output file for PDDL File", false,"", "string", cmd);
  	    cmd.parse(argc, argv);

        // 1. DATA
        // 1.1 CMD verification
        if(nArg.getValue() < 0)
            throw std::domain_error("Number of cities (n) must be positive.");
        if(tArg.getValue() < 1)
            throw std::domain_error("Number of passengers (t) must be > 0.");
        if(pArg.getValue() < 1)
            throw std::domain_error("Number of planes (p) must be > 0.");
        if(tArg.getValue() - pArg.getValue() < 1)
            throw std::domain_error("Number of passengers must be strictly higher than the number of planes.");

        unsigned n = nArg.getValue();
        unsigned t = tArg.getValue();
        unsigned p = pArg.getValue();

        bool pruning = aArg.getValue();
        bool forceSym = SArg.getValue();

        string pathPDDL;
        if(OArg.getValue().empty())
            pathPDDL = "zeno"+std::to_string(n)+"n"+std::to_string(t)+"t"+std::to_string(p)+"pMulti.pddl";
        else
            pathPDDL = OArg.getValue();

        // 1.2 Costs and durations
        vector<double> c(n,1);
        vector<double> d(n,1);
        vector<double> de(n,1); // East durations in case the problem is not symetric
        auto symetric = false;

        if(!dArg.getValue().empty())
        {
            ifstream dataFile(dArg.getValue());
            if (dataFile)
            {
                string s;
                getline(dataFile, s);
                istringstream iss(s);
                vector<string> tokens{istream_iterator<string>{iss}, istream_iterator<string>{}};
                if(tokens.size() != n)
                    throw std::runtime_error("The data file is not valid. Check the length of the vectors.");
                for(unsigned i = 0; i < n; ++i)
                    d[i] = stoi(tokens[i]);

                while(!dataFile.eof())
                {
                    getline(dataFile, s);
                    if(s.empty())
                        continue;
                    else 
                    {
                        iss = istringstream(s);
                        tokens = vector<string>{istream_iterator<string>{iss}, istream_iterator<string>{}};
                        if(tokens.size() != n)
                            throw std::runtime_error("The data file is not valid. Check the length of the vectors.");
                        for(unsigned i = 0; i < n; ++i)
                            de[i] = stoi(tokens[i]);
                        break;
                    }

                }

                while(!dataFile.eof())
                {
                    getline(dataFile, s);
                    if(s.empty())
                        c = de;
                    else
                    {
                        iss = istringstream(s);
                        tokens = vector<string>{istream_iterator<string>{iss}, istream_iterator<string>{}};
                        if(tokens.size() != n)
                            throw std::runtime_error("The data file is not valid. Check the length of the vectors.");
                        for(unsigned i = 0; i < n; ++i)
                            c[i] = stoi(tokens[i]);
                    }
                }
            }
            else
                throw std::runtime_error("Can't open the data file: "+dArg.getValue());
            if(c[0] == c[1] && c[0] == 1) // Symetric problem
            {
                c = de;
                de = d;
                symetric = true;
            }
        }
        else
        {
            auto f = f3;
            auto g = f3;
            auto h = f3;
            switch (CArg.getValue())
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
            if(DEArg.isSet() and DWArg.isSet())
            {
                switch (DEArg.getValue())
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
                switch (DWArg.getValue())
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
                switch (DArg.getValue())
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
            apply(c, f, xArg.getValue(), yArg.getValue(), ScArg.getValue(), TcArg.getValue());
            rapply(d, g, xArg.getValue(), yArg.getValue(), SdArg.getValue(), TdArg.getValue());
            if(!symetric)
                rapply(de, h, xArg.getValue(), yArg.getValue(), SdArg.getValue(), TdArg.getValue());
        }

        // Convert to int
        for(auto& i : c)
            i = (int)(rArg.getValue()*i);

        for(auto& i : d)
            i = (int)(rArg.getValue()*i);

        for(auto& i : de)
            i = (int)(rArg.getValue()*i);

        // Assuming d and c are strictly monoteneous, d must be decreasing for the algorithm
        // TODO: Take into account non-symetric cases
        if(d[0] > d[1]) {
            swap(d,c);
            std::reverse(std::begin(de), std::end(de));
        }


        if(symetric)
            de = d;

        #ifdef DEBUG
        std::cerr << "C: ";
        for(auto& i : c)
            std::cerr << i << " ";
        std::cerr << std::endl;

        std::cerr << "DW: ";
        for(auto& i : d)
            std::cerr << i << " ";
        std::cerr << std::endl;

        std::cerr << "DE: ";
        for(auto& i : de)
            std::cerr << i << " ";
        std::cerr << std::endl;
        #endif

        // 2. GENERATE ADMISSIBLE PPP
        //// 2.1. East and West subtuples
        auto t0 = high_resolution_clock::now();
        map<int, Plan> front; // Key using a double ?
        map<int, Plan> pareto;
        int EStatut = NEXT;

        int s = 2*t - p;
        auto w = std::vector<int>(p,0);

        long long int count = 0;

        int countIterations = 0;
        

        int EStatus = NEXT;
        auto e = std::vector<int>(s,0);
        while(EStatus == NEXT)
        {
            int C = 0;
            for_each(begin(e), end(e),[&](unsigned i) { C += c[i]; });

            int Mc = 0;
            for_each(begin(e), end(e),[&](unsigned i) { Mc += d[i] + de[i]; });

            // TODO: Check if the PPP are generated sorted. In this case the max element can be found in O(1)
            auto me = *std::max_element(begin(e), end(e),[&](unsigned i, unsigned j) { return d[i] + de[i] < d[j] + de[j]; });
            int Ml = Mc / p;
            //Ml = std::max(double(Ml), d[me] + de[me]);

            auto MaxM = Mc;
            auto linear = Plan(1);
            linear.m = Mc;
            linear.c = C;
            auto plan = linear;
            if (!front.count(C))
                front[C] = linear;

            // Pruning
            bool dominated = false;
            if(pruning)
            {
                for(auto i = front.find(C); i != --begin(front); --i)
                {
                    if(i->second.m <= Ml)
                    {
                        //std::cout << "Dominated!" << std::endl;
                        dominated = true;
                        break;
                    }
                }
                
            }

            if(!dominated)
            {
                auto mapping = std::map<int, std::pair<int, int>>{};
                auto mapping_inPPP = std::map<int, std::pair<int, int>>{};
                auto sum = int{0};
                for(auto it: e)
                {
                    if(mapping.count(it)) {
                        mapping[it].first++;
                        mapping_inPPP[it].first++;

                    }
                    else {
                        mapping[it] = {1, 0};
                        mapping_inPPP[it] = {1, sum};
                    }
                    sum++;
                }

                auto mapping_v = std::vector<int>(mapping.size());
                auto i = int{0};
                for(auto& j: mapping)
                {
                    j.second.second = i;
                    mapping_v[i] = j.first;
                    ++i;
                }



                // Select p cities for the pattern 1
                auto p1 = std::vector<std::vector<int>>{};
                for(int i = 0; i <= p; i++) {
                    p1 = generatePowerSet(p1, e, mapping_v, mapping, i, mapping_v.size());
                } 
                
                for(auto p1_dist: p1) 
                {
                    auto ppp_c = std::vector<int>(s - 1*p1_dist.size());
                    auto mapping_new = mapping_inPPP;
                    auto mapping_betaSet = std::map<int, std::pair<int, int>>{};

                    auto k = int{0};
                    for(auto& i: p1_dist) {
                        mapping_new[i].first -= 1;
                    }

                    for(auto i: mapping_new) 
                    {
                        for(auto l = 0; l < i.second.first; ++l) {
                            ppp_c[k + l] = i.first;
                        }
                        k += i.second.first;
                    }

                    auto mapping = std::map<int, std::pair<int, int>>{};
                    auto mapping_inPPP = std::map<int, std::pair<int, int>>{};
                    auto sum = int{0};
                    for(auto it: ppp_c)
                    {
                        if(mapping.count(it)) {
                            mapping[it].first++;
                            mapping_inPPP[it].first++;

                        }
                        else {
                            mapping[it] = {1, 0};
                            mapping_inPPP[it] = {1, sum};
                        }
                        sum++;
                    }

                    // Calculate the size of the set of beta values
                    auto betaSetSize = 0;
                    for(auto& i: mapping) 
                    {
                        i.second.first /= 2;
                        betaSetSize += i.second.first;
                    }

                    // Create the vector of beta values
                    auto betaSetValues = std::vector<int>(betaSetSize);
                    k = int{0};

                    auto it = std::begin(mapping);
                    while(it != std::end(mapping)) 
                    {
                        if(it->second.first == 0) {
                            mapping.erase(it++);
                        }
                        else 
                        {
                            for(auto j = 0; j < it->second.first; ++j) {
                                betaSetValues[k + j] = it->first;
                            }
                            k += it->second.first;
                            ++it;
                        }
                    }

                    auto mapping_v = std::vector<int>(mapping.size());
                    auto i = int{0};
                    for(auto& j: mapping)
                    {
                        j.second.second = i;
                        mapping_v[i] = j.first;
                        ++i;
                    }

                    plan = noDuplicate::UpperBound(Mc, Ml, ppp_c, p1_dist, {}, d, de, p);
                    plan.c = C;
                    countIterations++;

                    if(plan.m <= Ml)
                    {
                        if(plan.m < front[C].m)
                            front[C] = plan;
                        break;
                    }

                    auto betaPowerSet = std::vector<std::vector<int>>{};
                    if(i > 0) 
                    {    
                        auto r = std::vector<std::vector<int>>{};
                        for(int i = 0; i <= betaSetSize; i++) {
                        r = generatePowerSet(r, betaSetValues, mapping_v, mapping, i, mapping_v.size());
                            for(unsigned i = 0; i < r.size(); ++i) {
                                betaPowerSet.push_back(r[i]);
                            }
                        } 
                    } 

                    for(auto j: betaPowerSet) 
                    {
                        auto ppp_beta = std::vector<int>(s - p1_dist.size() - 2*j.size());
                        auto mapping_new2 = mapping_new;

                        k = int{0};
                        for(auto& i: j) 
                        {
                            mapping_new2[i].first -= 2;
                        }

                        for(auto i: mapping_new2) 
                        {
                            for(auto l = 0; l < i.second.first; ++l) {
                                ppp_beta[k + l] = i.first;
                            }
                            k += i.second.first;

                        }

                        plan = noDuplicate::UpperBound(Mc, Ml, ppp_beta, p1_dist, j, d, de, p);
                        plan.c = C;
                        MaxM = std::min(plan.m, MaxM);
                        countIterations++;
                        if(MaxM <= Ml)
                        {
                            //std::cout << "optimal! -> Exit from BetaSet" << std::endl;
                            break;
                        }
                    }
                    if(MaxM <= Ml)
                    {
                        //std::cout << "optimal! -> Exit from P1 Distrib" << std::endl;
                        break;
                    }
                }
            }
            if(plan.m < front[C].m)
                front[C] = plan;
            count++;
            EStatus = nextTuple(e, n, s);
        }
        

        pareto = paretoExtractionPlan(front);
        auto t1 = high_resolution_clock::now();
        auto time = std::chrono::duration_cast<milliseconds>(t1 - t0);
        ///*
        for(auto& i : pareto)
           cout << i.second << " " << i.second.c << " " << i.second.m << endl;
        //*/

        if(GArg.getValue())
            generatePDDLPlan(pathPDDL, n,t,p,c,d,pareto);

        cerr << n << " "
             << t << " "
             << p << " "
             << count << " "
             << countIterations << " "
             << front.size() << " "
             << pareto.size() << " "
             << time.count() << endl;
    }
	catch (std::exception &e)  // catch any exceptions
	{
        std::cerr << "Error: " << e.what() << std::endl;
        return 1;
	}

    return 0;
}
