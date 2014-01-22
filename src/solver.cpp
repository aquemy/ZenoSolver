#include <iostream>
#include <vector>
#include <algorithm>
#include <functional>
#include <fstream>
#include <chrono>

#ifdef _OPENMP
#include <omp.h>
#endif // _OPENMP

#include <tclap/CmdLine.h>
#include <combiGenerator.hpp>
#include <algorithm.hpp>
#include <ppp.hpp>
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

	    TCLAP::ValueArg<int> nArg("n","cities","Number of cities",true,3,"int", cmd);
        TCLAP::ValueArg<int> tArg("t","travelers","Number of travelers",true,3,"int", cmd);
        TCLAP::ValueArg<int> pArg("p","planes","Number of planes",true,2,"int", cmd);
        TCLAP::SwitchArg sArg("s","saveTuple","Save tuples in file.", cmd, false);
        TCLAP::SwitchArg gArg("g","generateTuple","Generate tuple even if a data file exists.", cmd, false);
        TCLAP::SwitchArg PArg("P","onlyPareto","Return only Pareto optimal points.", cmd, false);
        TCLAP::SwitchArg aArg("a","pruning","Activate / deactivate the pruning by greedily domination.", cmd, true);
        TCLAP::ValueArg<unsigned> BArg("B","betaMax","Ignore higher beta values.", false,100, "unsigned", cmd);
        
	    cmd.parse(argc, argv);
	
        // 1. DATA
        // 1.1 Data verification
        if(nArg.getValue() < 0 
        or tArg.getValue() < 1 
        or pArg.getValue() < 1 
        or (tArg.getValue() - pArg.getValue()) < 1)
        {
            // TODO : Real warning :)
            exit(0); // Cases not handled at the moment. 
        }
        
        unsigned n = nArg.getValue();
        unsigned t = tArg.getValue();
        unsigned p = pArg.getValue();
        
        unsigned initValue = 1;
        vector<double> c(n);
        generate(begin(c), end(c), [&]{ return initValue++; }); 
        vector<double> d(n);
        generate(begin(d), end(d), [&]{ return initValue--; }); 
        
        // Generate data
        apply(c, f3);
        apply(d, f5);
        
        for(auto i : c)
            cerr << i << " ";
        cerr << endl;
        for(auto i : d)
            cerr << i << " ";

        // 2. GENERATE ADMISSIBLE PPP
        //// 2.1. East and West subtuples
        auto t0 = high_resolution_clock::now();
        vector<vector<int>> E, W;
        if(gArg.getValue() or !isReadable("tuple_"+to_string(n)+"_"+to_string(t)+".dat"))
            E = generateTuples(n, t, sArg.getValue());
        else
            E = readTuples(n,t);
        
        if(gArg.getValue() or !isReadable("tuple_"+to_string(n)+"_"+to_string(t-p)+".dat"))
            W = generateTuples(n, t-p, sArg.getValue());
        else
            W = readTuples(n,t-p);
        auto t1 = high_resolution_clock::now();
        milliseconds time = std::chrono::duration_cast<milliseconds>(t1 - t0);
        cerr << "Generation Tuple : " << time.count() << "ms." << endl;
        
        //// 2.2. Cartesian product E x W + Admissible PPP initialization
        t0 = high_resolution_clock::now();
        vector<PPP> PPPSet = cartesianProduct(E, W, c, d, p);
        t1 = high_resolution_clock::now();
        time = std::chrono::duration_cast<milliseconds>(t1 - t0);
        cerr << "Generation PPP from tuples : " << time.count() << "ms." << endl;
        
        auto PPPSetDump = bind(dump, PPPSet, E, W);
        
        /*#ifndef NDEBUG
        debugPrint("ADMISSIBLE PPP-SET", PPPSetDump);
        #endif // DEBUG*/
        
        // 3. COMPUTE THE SIMPLE GREEDY UPPER-BOUND
        t0 = high_resolution_clock::now();
        auto upperBound = bind(SimpleUpperBound, placeholders::_1, E, W, d, p);
        for_each(begin(PPPSet), end(PPPSet), [&upperBound](PPP& ppp){ ppp.Mc = upperBound(ppp); });
        t1 = high_resolution_clock::now();
        time = std::chrono::duration_cast<milliseconds>(t1 - t0);
        cerr << "Greedy Upper Bound : " << time.count() << "ms." << endl;
        /*bool pruningIsActivated = aArg.getValue();
        if(pruningIsActivated)
        {
            auto pruningCriterion = bind(isGreedilyDominated, placeholders::_1, PPPSet);
            PPPSet.erase(remove_if(begin(PPPSet), end(PPPSet), pruningCriterion), end(PPPSet));
        }*/
                                
        // 5. COMPUTE BETA MAX AND THE SET OF POSSIBLE VALUE
        // Note : We compute BetaMax only now because the Greedy Upper-Bound corresponds to Beta = 0
        // REQUIEREMENT : Both tupple of the PPP must be in ascending order !
        //                This avoids sorting PPP in O((t+p)*log(t+p) + t*log(t))
        for_each(begin(PPPSet), end(PPPSet), bind(&PPP::computeBetaMax, placeholders::_1, E, W));
        
        /*#ifndef NDEBUG
        debugPrint("AFTER THE GREEDY ALGORITHM", PPPSetDump);
        #endif // DEBUG*/
        
        /*std::cerr << "Avant : " << std::endl;
        for(auto ppp : PPPSet)
            std::cerr << ppp.Mc << std::endl;*/

        // 5. APPLY MAIN ALGORITHM
        // TODO : Using BetaSet and Pruning
        t0 = high_resolution_clock::now();
        unsigned globalBetaMax = min(BArg.getValue(), t - p);
        #ifdef _OPENMP
        #pragma omp parallel for
        #endif // _OPENMP
        for(unsigned beta = 1; beta <= globalBetaMax; ++beta)
        {
            //debugPrint("BETA = "+to_string(beta), []{});
            for(auto it = begin(PPPSet); it < end(PPPSet); ++it)
            {
                if(it->betaMax >= beta && it->Mc > it->Ms) {
                    //cerr << "________________________" << endl;
                    //dumpPPP(*it, E, W);
                    double MaxM = UpperBound(*it, E, W, d, p, beta);
                    if(MaxM < it->Mc) 
                        it->Mc = MaxM;
                }
            }
            
            // Prunning
            // TODO Smartest pruning system
            /*if(pruningIsActivated)
            {
                auto pruningCriterion = bind(isGreedilyDominated, placeholders::_1, PPPSet);
                PPPSet.erase(remove_if(begin(PPPSet), end(PPPSet), pruningCriterion), end(PPPSet));
            }*/
        }
        t1 = high_resolution_clock::now();
        time = std::chrono::duration_cast<milliseconds>(t1 - t0);
        cerr << "Main algorithm : " << time.count() << "ms." << endl;
        
        /*std::cerr << "Après : " << std::endl;
        for(auto ppp : PPPSet)
            std::cerr << ppp.Mc << std::endl;*/
        /*#ifndef NDEBUG
        debugPrint("FINAL PPP SET WITH OPTIMAL MAKESPAN", PPPSetDump);
        #endif // DEBUG*/

        // 6. COMPUTE PARETO POINTS
        //// 6.1 Clean PPP Set
        cerr << "Number of points : " << PPPSet.size() << endl;
        if(PArg.getValue())
        {
            t0 = high_resolution_clock::now();
            
            sort(begin(PPPSet), end(PPPSet), SortByCost);
            auto it = begin(PPPSet);
            decltype(PPPSet) pareto;
            for(auto i = begin(PPPSet); i <= end(PPPSet); i++)
            {
                if(it->C == i->C)
                {
                    if(it->Mc > i->Mc)
                        it = i;
                }
                else
                {
                    cout << it->C << " " << it->Mc << " " << it->Ms << endl;
                    pareto.push_back(*it);
                    it = i;
                }
            }
            /*sort(begin(pareto), end(pareto), SortByMakespan);
            it = begin(pareto);
            unsigned cardPareto = 0;
            for(auto i = begin(pareto); i <= end(pareto); i++)
            {
                if(it->Mc == i->Mc)
                {
                    if(it->C > i->C)
                        it = i;
                }
                else
                {
                    cout << it->C << " " << it->Mc << " " << it->Ms << endl;
                    it = i;
                    cardPareto++;
                }
            }
            cerr << "Pareto-optimal points : " << cardPareto << endl;*/
            t1 = high_resolution_clock::now();
            time = std::chrono::duration_cast<milliseconds>(t1 - t0);
            cerr << "Pareto extraction : " << time.count() << "ms." << endl;
        }
        else
        {
            for(auto& i : PPPSet)
                cout << i.C << " " << i.Mc << " " << i.Ms << endl;
        }
    } 
	catch (TCLAP::ArgException &e)  // catch any exceptions
	{ 
        std::cerr << "error: " << e.error() << " for arg " << e.argId() << std::endl; 
	}

    return 0;
}
