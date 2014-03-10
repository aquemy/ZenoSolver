#include <iostream>
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

#include <tclap/CmdLine.h>
#include <combiGenerator.hpp>
#include <powerSetGenerator.hpp>
#include <algorithm.hpp>
#include <ppp.hpp>
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

long long int countIterations = 0;

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
        
        bool pruning = aArg.getValue();
        
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

        // Generate data
        apply(c, f2, xArg.getValue(), yArg.getValue(), ScArg.getValue(), TcArg.getValue());
        rapply(d, f2, xArg.getValue(), yArg.getValue(), SdArg.getValue(), TdArg.getValue());
        
        // Convert to INT for DAE
        // TODO : Un truc plus propre
        for(auto& i : c)
            i = (int)(100*i);
        
        for(auto& i : d)
            i = (int)(100*i);
        
        // Assuming d and c are strictly monoteneous
        if(d[0] > d[1])
            swap(d,c);
        
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
        
        /*cerr << "c : ";
        for(auto i : c)
            cerr << i << " ";
        cerr << endl;
        cerr << "d : ";
        for(auto i : d)
            cerr << i << " ";
        cerr << endl;    */
        
        // 2. GENERATE ADMISSIBLE PPP
        //// 2.1. East and West subtuples
        auto t0 = high_resolution_clock::now();
        map<int, int> front; // Key using a double ?
        map<int, int> pareto;
        int EStatut = GEN_NEXT;
        
        std::vector<int> e(t,0);
        
        long long int count = 0;
        while(EStatut == GEN_NEXT)
        {
            int WStatut = GEN_NEXT;
            std::vector<int> w(t-p,0);
            while(WStatut == GEN_NEXT)
            {
                // TODO : Checker si le PPP est greedily dominé
                
                // 1. Construction du PPP courant
                int C = 0;
                for_each(begin(e), end(e),[&](unsigned i) { C += c[i];});
                for_each(begin(w), end(w),[&](unsigned i) { C += c[i];});
                int Mc = 0;
                for_each(begin(e), end(e),[&](unsigned i) { Mc += 2*d[i];});
                for_each(begin(w), end(w),[&](unsigned i) { Mc += 2*d[i];});
                int Ml = Mc / p;
                
                if (!front.count(C))
                    front[C] = Mc;
                
                bool dominated = false;
                // Pruning
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
                //*/
                  
                if(!dominated)
                {  
                vector<int> betaSetValue;
                decltype(w) diff;
                set_difference (begin(w), end(w), begin(e), end(e), back_inserter(diff));
                set_difference (begin(w), end(w), begin(diff), end(diff), back_inserter(betaSetValue));
                
                /*cerr << "=======================================" << endl;
                cerr << "PPP : (";
                for(auto i : e)
                    cerr << i << ",";
                cerr << ")(";
                for(auto i : w)
                    cerr << i << ",";
                cerr << ")" << endl;
                cerr << "C : " << C << endl;
                cerr << "M : " << Mc << endl;
                cerr << "BetaSetValue : ";
                for(auto i : betaSetValue)
                    cerr << i << " ";
                cerr << endl;*/
                
                // 1.2. Calcul du BetaPowerSet
                unsigned betaMax = betaSetValue.size();
                set<vector<unsigned>> betaPowerSet;
                for(unsigned i = 0; i <= betaMax; i++)
                    generatePowerSet(betaMax, i, betaSetValue, betaPowerSet);
                /*cerr << "BetaPowerSet : ";
                for(auto i : betaPowerSet)
                {
                    cerr << "{";
                    for(auto j : i)
                        cerr << j << ",";
                    cerr << "}" << endl;
                }
                cerr << endl;*/
                // 2. Calcul de la borne max    

                auto bestM = Mc;
                int MaxM = UpperBound(Mc, Ml, e, w, betaPowerSet, d, p);
                if(MaxM < Mc) 
                {
                    Mc = MaxM;    
                    // 3. Compare
                    if(Mc < front[C])
                        front[C] = Mc;
                }
                    
                
                
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
        for(auto& i : pareto)
           cout << i.second << " " << i.first << endl;
           
        if(GArg.getValue())
            generatePDDL(pathPDDL, n,t,p,c,d,pareto);
             
        cerr << n << " " << t << " " << p << " " << count << " " << countIterations << " " << front.size() << " " << pareto.size() << " " << time.count() << endl;
    } 
	catch (TCLAP::ArgException &e)  // catch any exceptions
	{ 
        std::cerr << "error: " << e.error() << " for arg " << e.argId() << std::endl; 
	}

    return 0;
}
