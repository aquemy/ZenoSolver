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

/* TODO
- Système de build
- Tests
- Optimisation mémoire
- Pruning + Domination
- Calcul de stats
- Calcul itératif en limitant les beta
- Etude boucle intérieur / extérieur
- Système de fonctions génératrices
- Option de génération de plans
- Option de génération de benchmark PDDL
- Gérer les cas triviaux ou paramètres mauvais
- Gérer les options
*/

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
        map<int, int> front; // Key using a double ?
        map<int, int> pareto;
        int EStatut = NEXT;

        std::vector<int> e(t,0);

        long long int count = 0;

        int countIterations = 0;
        ///*
        while(EStatut == NEXT)
        {
            int WStatut = NEXT;
            auto w = std::vector<int>(t-p,0);
            while(WStatut == NEXT)
            {
                // 1. Construction du PPP courant
                int C = 0;
                for_each(begin(e), end(e),[&](unsigned i) { C += c[i]; });
                for_each(begin(w), end(w),[&](unsigned i) { C += c[i]; });
                int Mc = 0;
                for_each(begin(e), end(e),[&](unsigned i) { Mc += d[i] + de[i]; });
                for_each(begin(w), end(w),[&](unsigned i) { Mc += d[i] + de[i]; });
                // TODO: Check if the PPP are generated sorted. In this case the max element can be found in O(1)
                auto me = *std::max_element(begin(e), end(e),[&](unsigned i, unsigned j) { return d[i] + de[i] < d[j] + de[j]; });
                auto mw = *std::max_element(begin(w), end(w),[&](unsigned i, unsigned j) { return d[i] + de[i] < d[j] + de[j]; });
                int Ml = Mc / p;
                Ml = std::max(double(Ml), d[me] + de[me]);
                Ml = std::max(double(Ml), d[mw] + de[mw]);

                if (!front.count(C))
                    front[C] = Mc;

                // Pruning
                bool dominated = false;
                if(pruning)
                {
                    for(auto i = front.find(C); i != --begin(front); --i)
                    {
                        if(i->second <= Ml)
                        {
                            dominated = true;
                            break;
                        }
                    }
                }

                if(!dominated)
                {
                    vector<int> betaSetValue;
                    decltype(w) diff;
                    set_difference (begin(w), end(w), begin(e), end(e), back_inserter(diff));
                    set_difference (begin(w), end(w), begin(diff), end(diff), back_inserter(betaSetValue));

                    // 1.2. Calcul du BetaPowerSet
                    unsigned betaMax = min(BArg.getValue(), (unsigned)betaSetValue.size());
                    set<vector<int>> betaPowerSet;
                    for(unsigned i = 0; i <= betaMax; i++)
                        naive::generatePowerSet(i, betaSetValue, betaPowerSet);

                    // 2. Calcul de la borne max
                    auto bestM = Mc;
                    int MaxM = naive::symetric::UpperBound(Mc, Ml, e, w, betaPowerSet, d, de, p, countIterations);
                    if(MaxM < Mc)
                    {
                        Mc = MaxM;
                        // 3. Compare
                        if(Mc < front[C])
                            front[C] = Mc;
                    }
                    //countIterations += betaPowerSet.size();
                }
                count++;
                //_
                WStatut = nextTuple(w, n, t-p);
            }
            EStatut = nextTuple(e, n, t);
        }

        pareto = paretoExtraction(front);
        auto t1 = high_resolution_clock::now();
        auto time = std::chrono::duration_cast<milliseconds>(t1 - t0);
        /*
        for(auto& i : pareto)
           cout << i.second << " " << i.first << endl;
        //*/

        if(GArg.getValue())
            generatePDDL(pathPDDL, n,t,p,c,d,pareto);
        if(args.FArg.getValue())
            for(auto& i : pareto)
                cout << i.first << " " << i.second << "\n";


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
