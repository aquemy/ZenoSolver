#include <iostream>
#include <vector>
#include <algorithm>
#include <functional>
#include <fstream>

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
        TCLAP::SwitchArg PArg("P","onlyPareto","Return only Pareto optimal points.", cmd, true);
        
	    // Parse the argv array.
	    cmd.parse( argc, argv );
	
        // 1. DATA
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
        apply(d, f3);
        
        // 2. GENERATE ADMISSIBLE PPP
        //// 2.1. East and West subtuples
        
        vector<vector<int>> E, W;
        if(gArg.getValue() or !isReadable("tuple_"+to_string(n)+"_"+to_string(t)+".dat"))
            E = generateTuples(n, t, sArg.getValue());
        else
            E = readTuples(n,t);
        
        if(gArg.getValue() or !isReadable("tuple_"+to_string(n)+"_"+to_string(t-p)+".dat"))
            W = generateTuples(n, t-p, sArg.getValue());
        else
            W = readTuples(n,t-p);
        
        //// 2.2. Cartesian product E x W + Admissible PPP initialization
        vector<PPP> PPPSet;
        for(auto& e : E)
        {
            double CostEast = 0;
            for_each(begin(e),end(e),[&](unsigned i) { CostEast += c[i];});
            double MlEast = 0;
            for_each(begin(e),end(e),[&](unsigned i) { MlEast += 2*d[i];});
            for(auto& w : W)
            {
                double Cost = CostEast;
                for_each(begin(w),end(w),[&](unsigned i) { Cost += c[i];});
                double Ml = MlEast;
                for_each(begin(w),end(w),[&](unsigned i) { Ml += 2*d[i];});
                // Note : We compute BetaMax only after the computation of the GreedyUpperBound with Beta=0
                //        In this case it is possible to avoid such a computation for already pruned PPP.
                PPPSet.push_back(PPP(e, w, Cost, Ml / p, Ml));
            }
        }
        
        auto PPPSetDump = bind(dump, PPPSet);
        
        #ifdef DEBUG
        debugPrint("ADMISSIBLE PPP-SET", PPPSetDump);
        #endif // DEBUG
        
        // 3. COMPUTE THE SIMPLE GREEDY UPPER-BOUND
        #ifdef _OPENMP
        #pragma omp parallel for
        #endif // _OPENMP
        for_each(begin(PPPSet), end(PPPSet), bind(SimpleUpperBound, placeholders::_1, d, p, t));
                                
        // 5. COMPUTE BETA MAX AND THE SET OF POSSIBLE VALUE
        // Note : We compute BetaMax only now because the Greedy Upper-Bound corresponds to Beta=0
        // REQUIEREMENT : Both tupple of the PPP must be in ascending order !
        //                This avoids sorting PPP in O((t+p)*log(t+p) + t*log(t))
        #ifdef _OPENMP
        #pragma omp parallel for
        #endif // _OPENMP
        for(auto it = begin(PPPSet); it < end(PPPSet); ++it)
            it->computeBetaMax();
        
    #ifdef DEBUG
        debugPrint("AFTER THE GREEDY ALGORITHM", PPPSetDump);
    #endif // DEBUG

        // 5. APPLY MAIN ALGORITHM
        // TODO : Using BetaSet and Pruning
        unsigned k = 1;
        
        for(unsigned beta = 1; beta <= t-p; beta++)
        {
            //bool improved = false; // If the PPP is not improved, no need to check Greedy Domination
            #ifdef _OPENMP
            #pragma omp parallel for
            #endif // _OPENMP
            for(auto it = begin(PPPSet); it < end(PPPSet); ++it)
            {
                if(it->betaMax >= beta) {
    #ifdef STATS
                    it->nbEval++;
    #endif // STATS
                    double MaxMi = UpperBound(*it, d, p, beta);
                    if(MaxMi < it->Mc) 
                    {
    #ifdef DEBUG    
                    cerr << "IMPROVEMENT : " << endl;
                    cerr << "PPP = (";
                    for(auto& i : it->e)
                        cerr << i << ",";
                    cerr << ")(";
                    for(auto& i : it->w)
                        cerr << i << ",";
                    cerr << ")" << endl;
                    cerr << "Previous Makespan : " << it->Mc << endl;
                    cerr << "New Makespan : " << MaxMi << endl;
    #endif // DEBUG
                    it->Mc = MaxMi;
                    //improved = true;
                    }
                }
            }
            k++;
        }
        
    #ifdef DEBUG
        debugPrint("FINAL PPP SET WITH OPTIMAL MAKESPAN", PPPSetDump);
    #endif // DEBUG

        // 6. COMPUTE PARETO POINTS
        //// 6.1 Clean PPP Set
        sort(begin(PPPSet), end(PPPSet), SortByMakespan);
        stable_sort(begin(PPPSet), end(PPPSet), SortByCost);
        PPPSet.erase(unique(begin(PPPSet), end(PPPSet)), end(PPPSet));

        for(auto it = begin(PPPSet); it < end(PPPSet); ++it)
        {
            it->dominated = true;
            if(PArg.getValue())
            {
                for(const auto& j : PPPSet)
                {
                    if(((j.C <= it->C) && (j.Mc < it->Mc)) 
                    || ((j.C < it->C) && (j.Mc <= it->Mc)))
                        it->dominated = false;
                }
            }
            if(it->dominated) 
            {    
                //#pragma omp critical
                cout << it->C << " " << it->Mc << " " << it->Ms << endl;
            }     
        }
        
    } 
	catch (TCLAP::ArgException &e)  // catch any exceptions
	{ 
        std::cerr << "error: " << e.error() << " for arg " << e.argId() << std::endl; 
	}
    return 0;
}
