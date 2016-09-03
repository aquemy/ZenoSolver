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

#include <tclap/CmdLine.h>
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

long long int countIterations = 0;

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
        TCLAP::SwitchArg aArg("a","pruning","Activate / deactivate the pruning by greedily domination.", cmd, true);
        TCLAP::SwitchArg GArg("G","generatePDDL","Generate PDDL instance file according to data.", cmd, false);
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
                        break;
                    iss = istringstream(s);
                    tokens = vector<string>{istream_iterator<string>{iss}, istream_iterator<string>{}};
                    if(tokens.size() != n)
                        throw std::runtime_error("The data file is not valid. Check the length of the vectors.");
                    for(unsigned i = 0; i < n; ++i)
                        de[i] = stoi(tokens[i]);
                }

                while(!dataFile.eof())
                {
                    getline(dataFile, s);
                    std::cout << "c:" << s << std::endl;
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
                c = de;
                de = d;
                symetric = true;
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
                symetric = false;
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
                switch (DEArg.getValue())
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

        // Assuming d and c are strictly monoteneous, d must be decreasing for the algorithm
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

        // 2. GENERATE ADMISSIBLE PPP
        //// 2.1. East and West subtuples
        auto t0 = high_resolution_clock::now();
        map<int, int> front; // Key using a double ?
        map<int, int> pareto;
        int EStatut = NEXT;

        std::vector<int> e(t,0);

        long long int count = 0;
        while(EStatut == NEXT)
        {
            int WStatut = NEXT;
            std::vector<int> w(t-p,0);
            while(WStatut == NEXT)
            {
                // 1. Construction du PPP courant
                int C = 0;
                for_each(begin(e), end(e),[&](unsigned i) { C += c[i]; });
                for_each(begin(w), end(w),[&](unsigned i) { C += c[i]; });
                int Mc = 0;
                for_each(begin(e), end(e),[&](unsigned i) { Mc += 2*d[i]; });
                for_each(begin(w), end(w),[&](unsigned i) { Mc += 2*d[i]; });
                int Ml = Mc / p;

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
                    set<vector<unsigned>> betaPowerSet;
                    for(unsigned i = 0; i <= betaMax; i++)
                        generatePowerSet(i, betaSetValue, betaPowerSet);

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
                    countIterations += betaPowerSet.size();
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
