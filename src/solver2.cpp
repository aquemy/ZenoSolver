#include <iostream>
#include <vector>
#include <set>
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
#include <powerSetGenerator.hpp>
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

double UpperBound(double Mc, 
    double Ml, 
    const std::vector<int>& e, 
    const std::vector<int>& w,
    const std::vector<std::vector<unsigned>>& betaPowerSet,
    const std::vector<double>& d,
    
    unsigned p)
{
    using std::begin;
    using std::end;
    
    // Little trick waiting for C++14
    auto rbegin = [](decltype(e) v) { return v.rbegin(); };
    auto rend = [](decltype(e) v) { return v.rend(); };
    
    

    auto bestM = Mc;
    
    for(auto betaSet : betaPowerSet)
    {
        // Delete elements of the betaSet from w        
        std::vector<int> alphaWSet;
        std::set_difference (begin(w), end(w), begin(betaSet), end(betaSet), std::back_inserter(alphaWSet));
        
        // Delete elements of the betaSet from e        
        std::vector<int> alphaESet;
        std::set_difference(begin(e), end(e), begin(betaSet), end(betaSet), std::back_inserter(alphaESet));
    
        std::vector<Si> S(p);
        
        auto itE = rbegin(alphaESet);
        auto itW = rbegin(alphaWSet);
        auto itP = begin(S);
    
        // Perform the greedy algorithm
        while(itW < rend(alphaWSet))
        {
            itP = min_element(begin(S), end(S), compM);
            if(itP->s)
            {
                itP->m += 2*d[*itE];
                itP->s = false;
                itE++;
            }
            else
            {
                itP->m += 2*d[*itW];
                itP->s = true;
                itW++;
            }
        }
        
        while(itE < rend(alphaESet))
        {
            itP = min_element(begin(S),end(S),compMS);
            itP->m += 2*d[*itE];
            itP->s = false;
            itE++;
        }
        
        // Pattern 3
        for(auto i : betaSet)
        {
            // Place only the element we need in order to avoid complete sorting
            std::nth_element(begin(S), begin(S)+1, end(S), compM);
            itP = min_element(begin(S), end(S), compM);
            itP->m += 2*d[i];
            (itP + 1)->m += 2*d[i];
        }
        
        if(bestM > std::max_element(begin(S),end(S), compM)->m)
            bestM = std::max_element(begin(S),end(S), compM)->m;
        if(bestM <= Ml)
            return Ml;
    }
            
    return bestM; 
}

vector<pair<double,double>> paretoExtraction2(vector<pair<double,double>>& front)
{
            auto current = begin(front);
            auto bestCurrent = begin(front);
            vector<pair<double,double>> temp;
            sort(begin(front), end(front), [](pair<double,double> i, pair<double,double> j){ return i.first < j.first; }); // TODO retirer l'étape de tri et insérer au bon endroit...
            for(auto i = begin(front); i <= end(front); i++)
            {
                if(current->first == i->first)
                {
                    if(bestCurrent->second > i->second)
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
            
            sort(begin(temp), end(temp), [](pair<double,double> i, pair<double,double> j){ return i.second < j.second; });
            vector<pair<double,double>> pareto;
            current = begin(temp);
            bestCurrent = begin(temp);
            for(auto i = begin(temp); i <= end(temp); i++)
            {
                if(current->second == i->second)
                {
                    if(bestCurrent->first > i->first)
                        bestCurrent = i;
                }
                else
                {
                    //cout << it->C << " " << it->Mc << " " << it->Ms << endl;
                    pareto.push_back(*bestCurrent);
                    current = i;
                    bestCurrent = i;
                }
            }
            
            return pareto;
}

void paretoExtraction(vector<pair<double,double>>& front)
{

    vector<pair<double,double>> temp;
    sort(begin(front), end(front), [](pair<double,double> i, pair<double,double> j){ return i.second < j.second; });
    stable_sort(begin(front), end(front), [](pair<double,double> i, pair<double,double> j){ return i.first < j.first; });
    front.erase(unique(begin(front), end(front)), end(front));

    //#pragma omp parallel for
    for(auto it = begin(front); it < end(front); ++it)
    {
        bool dominated = true;
        for(const auto& j : front)
        {
            if(j.first <= it->first && j.second < it->second 
            || j.first < it->first && j.second <= it->second)
                dominated = false;
        }
        if(dominated) {    
            cout << it->second << " " << it->first << endl;
        }     
    }
}

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

        // Generate data
        apply(c, f2, xArg.getValue(), yArg.getValue(), ScArg.getValue(), TcArg.getValue());
        rapply(d, f1, xArg.getValue(), yArg.getValue(), SdArg.getValue(), TdArg.getValue());
        
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
        
        if(d[0] > d[1])
            swap(d,c);

        // 2. GENERATE ADMISSIBLE PPP
        //// 2.1. East and West subtuples
        auto t0 = high_resolution_clock::now();
        vector<pair<double, double>> front; // Key using a double ?
        vector<pair<double, double>> pareto;
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
                double C = 0;
                for_each(begin(e), end(e),[&](unsigned i) { C += c[i];});
                for_each(begin(w), end(w),[&](unsigned i) { C += c[i];});
                double Mc = 0;
                for_each(begin(e), end(e),[&](unsigned i) { Mc += 2*d[i];});
                for_each(begin(w), end(w),[&](unsigned i) { Mc += 2*d[i];});
                double Ml = Mc / p;
                
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
                vector<vector<unsigned>> betaPowerSet;
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
                cerr << endl;  */  
                // 2. Calcul de la borne max    

                auto bestM = Mc;
                double MaxM = UpperBound(Mc, Ml, e, w, betaPowerSet, d, p);
                if(MaxM < Mc) 
                    Mc = MaxM;    

                // 3. Compare
                pair<double, double> point(C,Mc);
                front.push_back(point);  
                
                count++;
                //_
                WStatut = nextTuple(w, n, t-p);
            }
            // Copy partial Pareto front
            //front = paretoExtraction(front);
            EStatut = nextTuple(e, n, t);
        }
        
        
        pareto = paretoExtraction2(front);
        for(auto& i : pareto)
           cout << i.second << " " << i.first << endl;
           
        cerr << "PPP traités : " << count << endl;
    } 
	catch (TCLAP::ArgException &e)  // catch any exceptions
	{ 
        std::cerr << "error: " << e.error() << " for arg " << e.argId() << std::endl; 
	}

    return 0;
}
