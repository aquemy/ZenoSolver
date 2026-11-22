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
#include <cli.hpp>
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
        CliArgs args(cmd);
        cmd.parse(argc, argv);

        // 1. DATA
        auto instance = buildInstance(args);
        unsigned n = instance.n;
        unsigned t = instance.t;
        unsigned p = instance.p;
        vector<double> c = instance.c;
        vector<double> d = instance.d;
        vector<double> de = instance.de;
        auto symetric = instance.symetric;

        bool pruning = args.aArg.getValue();
        bool forceSym = args.SArg.getValue();
        auto& BArg = args.BArg;
        auto& GArg = args.GArg;

        string pathPDDL;
        if(args.OArg.getValue().empty())
            pathPDDL = "zeno"+std::to_string(n)+"n"+std::to_string(t)+"t"+std::to_string(p)+"pMulti.pddl";
        else
            pathPDDL = args.OArg.getValue();

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
                // Any stored front entry with cost <= C (all keys up to and including C).
                // The former reverse loop decremented begin(), which is undefined behaviour.
                for(auto i = begin(front), last = std::next(front.find(C)); i != last; ++i)
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
        if(args.FArg.getValue())
            for(auto& i : pareto)
                cout << i.first << " " << i.second.m << "\n";
        else
            for(auto& i : pareto)
               cout << i.second << " " << i.second.c << " " << i.second.m << endl;

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
