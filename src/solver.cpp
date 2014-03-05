#include <iostream>
#include <vector>
#include <algorithm>
#include <functional>
#include <fstream>
#include <chrono>
#include <random>
#include <ctime>

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
        //TCLAP::ValueArg<string> DArg("D","data","File where data (cost and durations) are located",true,"data","string", cmd);
        TCLAP::SwitchArg PArg("P","onlyPareto","Return only Pareto optimal points.", cmd, false);
        TCLAP::SwitchArg aArg("a","pruning","Activate / deactivate the pruning by greedily domination.", cmd, true);
        TCLAP::SwitchArg GArg("G","generatePDDL","Generate PDDL instance file according to data.", cmd, false);
        TCLAP::ValueArg<unsigned> BArg("B","betaMax","Ignore higher beta values.", false,100, "unsigned", cmd);
        TCLAP::ValueArg<unsigned> CArg("C","C","Function to generate C", false, 3, "unsigned", cmd);
        TCLAP::ValueArg<unsigned> DArg("D","D","Function to generate D", false, 3, "unsigned", cmd);
        TCLAP::ValueArg<double> ScArg("j","scaleC","Scale factor for C", false, 1, "unsigned", cmd);
        TCLAP::ValueArg<double> TcArg("k","transC","Translation factor for C", false, 0, "unsigned", cmd);
        TCLAP::ValueArg<double> SdArg("l","scaleD","Scale factor for D", false, 1, "unsigned", cmd);
        TCLAP::ValueArg<double> TdArg("m","transD","Translation factor for D", false, 0, "unsigned", cmd);
        
        TCLAP::ValueArg<double> xArg("x","x","Scale factor for D", false, 1, "unsigned", cmd);
        TCLAP::ValueArg<double> yArg("y","y","Translation factor for D", false, 0, "unsigned", cmd);
        
        TCLAP::ValueArg<string> OArg("O","ouput","Output file for PDDL File", false,"", "string", cmd);
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
        
        string pathPDDL;
        if(OArg.getValue().empty())
            pathPDDL = "zeno"+std::to_string(n)+"n"+std::to_string(t)+"t"+std::to_string(p)+"pMulti.pddl";
        else
            pathPDDL = OArg.getValue();
        
        vector<double> c(n,1);
        vector<double> d(n,1);
        /*ifstream dataFile(DArg.getValue());
        if (dataFile)
        {
            
            
        }
        else
            exit(0); // TODO : real warnings*/
            
        function<double(unsigned)> fc, fd;
        if(DArg.getValue() == 1)
            fd = f1;
        else if(DArg.getValue() == 2)
            fd = f2;
        else if(DArg.getValue() == 3)
            fd = f3;
        else if(DArg.getValue() == 4)
            fd = f4;
        else if(DArg.getValue() == 5)
            fd = f5;
            
        if(CArg.getValue() == 1)
            fc = f1;
        else if(CArg.getValue() == 2)
            fc = f2;
        else if(CArg.getValue() == 3)
            fc = f3;
        else if(CArg.getValue() == 4)
            fc = f4;
        else if(CArg.getValue() == 5)
            fc = f5;
        
        // Generate data
        apply(c, f3, xArg.getValue(), yArg.getValue(), ScArg.getValue(), TcArg.getValue());
        rapply(d, f3, xArg.getValue(), yArg.getValue(), SdArg.getValue(), TdArg.getValue());
        
        // Convert to INT for DAE
        // TODO : Un truc plus propre
        for(auto& i : c)
            i = (int)(100*i);
        
        for(auto& i : d)
            i = (int)(100*i);
        
        // Assuming d and c are strictly monoteneous
        if(d[0] > d[1])
            swap(d,c);
            
        cerr << "c : ";
        for(auto i : c)
            cerr << i << " ";
        cerr << endl;
        cerr << "d : ";
        for(auto i : d)
            cerr << i << " ";
        cerr << endl;    
        /*std::default_random_engine generator;
        generator.seed(std::time(0));
        std::uniform_real_distribution<double> distribution(0.0,10);
        c[0] = distribution(generator);
        d[d.size() - 1] = distribution(generator);
        for(unsigned i = 1; i < c.size(); i++)
        {
            c[i] += distribution(generator) + c[i-1];
            d[d.size()-i-1] += distribution(generator) + d[d.size()-i];
        }*/

        // 2. GENERATE ADMISSIBLE PPP
        //// 2.1. East and West subtuples
        auto t0 = high_resolution_clock::now();
        vector<vector<int>> E = generateTuples(n, t);
        vector<vector<int>> W = generateTuples(n, t-p);
        
        auto t1 = high_resolution_clock::now();
        milliseconds time = std::chrono::duration_cast<milliseconds>(t1 - t0);
        cerr << "Generation Tuple : " << time.count() << "ms." << endl;
        
        //// 2.2. Cartesian product E x W + Admissible PPP initialization
        t0 = high_resolution_clock::now();
        vector<PPP> PPPSet = cartesianProduct(E, W, c, d, p);
        t1 = high_resolution_clock::now();
        time = std::chrono::duration_cast<milliseconds>(t1 - t0);
        cerr << "Generation PPP from tuples : " << time.count() << "ms." << endl;
        
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
        for(auto it = begin(PPPSet); it < end(PPPSet); ++it)
        {
            
            //debugPrint("BETA = "+to_string(beta), []{});
            unsigned betaMax = min(globalBetaMax, it->betaMax);
            for(unsigned beta = 1; beta <= betaMax; ++beta)
            {
                double MaxM = UpperBound(*it, E, W, d, p, beta);
                if(MaxM < it->Mc) 
                    it->Mc = MaxM;
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
        

        // 6. COMPUTE PARETO POINTS
        //// 6.1 Clean PPP Set
        cerr << "Number of points : " << PPPSet.size() << endl;
        if(PArg.getValue())
        {
            t0 = high_resolution_clock::now();
            /*sort(begin(PPPSet), end(PPPSet), SortByCost);
            auto current = begin(PPPSet);
            auto bestCurrent = begin(PPPSet);
            decltype(PPPSet) temp;
            for(auto i = begin(PPPSet); i <= end(PPPSet); i++)
            {
                if(current->C == i->C)
                {
                    if(bestCurrent->Mc > i->Mc)
                        bestCurrent = i;
                }
                else
                {
                    //cout << it->C << " " << it->Mc << " " << it->Ms << endl;
                    temp.push_back(*bestCurrent);
                    current = i;
                    bestCurrent = i;
                }
            }
            
            sort(begin(temp), end(temp), SortByMakespan);
            decltype(PPPSet) pareto;
            current = begin(temp);
            bestCurrent = begin(temp);
            for(auto i = begin(temp); i <= end(temp); i++)
            {
                if(current->Mc == i->Mc)
                {
                    if(bestCurrent->C > i->C)
                        bestCurrent = i;
                }
                else
                {
                    //cout << it->C << " " << it->Mc << " " << it->Ms << endl;
                    pareto.push_back(*bestCurrent);
                    current = i;
                    bestCurrent = i;
                }
            }*/
            
                sort(begin(PPPSet), end(PPPSet), SortByMakespan);
                stable_sort(begin(PPPSet), end(PPPSet), SortByCost);
                PPPSet.erase(unique(begin(PPPSet), end(PPPSet)), end(PPPSet));
                decltype(PPPSet) pareto;
                for(auto it = begin(PPPSet); it < end(PPPSet); ++it)
                {
                    bool dominated = true;
                    for(const auto& j : PPPSet)
                    {
                        if(j.C <= it->C && j.Mc < it->Mc 
                        || j.C < it->C && j.Mc <= it->Mc)
                            dominated = false;
                    }
           
                    if(dominated) {   
                        pareto.push_back(*it); 
                        //cout << it->C << " " << it->Mc << " " << it->Ms << endl;
                    }     
                }
            
            cerr << "Pareto-optimal points : " << pareto.size() << endl;
            t1 = high_resolution_clock::now();
            time = std::chrono::duration_cast<milliseconds>(t1 - t0);
            cerr << "Pareto extraction : " << time.count() << "ms." << endl;
            for(auto& i : pareto)
                cout << i.Mc << " " << i.C << endl;
            // Generate PDDL instance
            if(GArg.getValue())
                generatePDDL(pathPDDL, n,t,p,c,d,pareto);
        }
        else
        {
            for(auto& i : PPPSet)
                cout << i.Mc << " " << i.C  << endl;
                    // Generate PDDL instance
            if(GArg.getValue())
                generatePDDL(pathPDDL, n,t,p,c,d);
        }
    } 
	catch (TCLAP::ArgException &e)  // catch any exceptions
	{ 
        std::cerr << "error: " << e.error() << " for arg " << e.argId() << std::endl; 
	}

    return 0;
}
