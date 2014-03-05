#include <iostream>
#include <fstream>
#include <iomanip>
#include <vector>
#include <functional>
#include <utils.hpp>
#include <ppp.hpp>

void debugPrint(std::string title, std::function<void(void)> f)
{
    std::cerr << std::setfill('=') << std::setw(42) << "=" << std::endl;
    std::cerr << "==" << std::setfill(' ') << std::setw((38 - title.size()) / 2 + 1) << " ";
    std::cerr << title;
    std::cerr << std::setfill(' ') << std::setw((38 - title.size()) / 2 + 1) << "==" << std::endl;
    std::cerr << std::setfill('=') << std::setw(42) << "=" << std::endl;
    f();
}

void dump(const std::vector<PPP>& set, 
    const std::vector<std::vector<int>>& E, 
    const std::vector<std::vector<int>>& W)
{
    for(auto& ppp : set)
        dumpPPP(ppp, E, W);
}

void dumpPPP(const PPP& ppp, 
    const std::vector<std::vector<int>>& E, 
    const std::vector<std::vector<int>>& W)
{
    std::cerr << "PPP = (";
    for(auto& i : E[ppp.e])
        std::cerr << i << ",";
    std::cerr << ")(";
    for(auto& i : W[ppp.w])
        std::cerr << i << ",";
    std::cerr << ")" << std::endl;
    std::cerr << " - Cost          : " << ppp.C << std::endl;
    std::cerr << " - Min. Makespan : " << ppp.Ms << std::endl;
    std::cerr << " - Cur. Makespan : " << ppp.Mc << std::endl;
    std::cerr << " - Beta Max      : " << ppp.betaMax << std::endl;
}

bool isReadable(const std::string& path) 
{ 
    std::ifstream file(path.c_str()); 
    return !file.fail(); 
}

void generatePDDL(std::string path, unsigned n, unsigned t, unsigned p, const std::vector<double>& c, const std::vector<double>& d, const std::vector<PPP>& pareto)
{
    std::ofstream dataFile(path);
            if (dataFile)
            {
                dataFile << "(define (problem MULTIZENO-A)" << std::endl;
                dataFile << "  (:domain  multi-zeno-travel)" << std::endl;
                dataFile << "  (:objects ";
                for(unsigned i = 1; i < p+1; i++)
                    dataFile << "plane" << i << " ";
                dataFile << "- aircraft" << std::endl << "            ";
                for(unsigned i = 1; i < t+1; i++)
                    dataFile << "person" << i << " ";
                dataFile << "- person" << std::endl << "            ";
                for(unsigned i = 0; i < n+2; i++)
                    dataFile << "city" << i << " ";
                dataFile << "- city)" << std::endl;
                
                dataFile << "  (:init (= (total-cost) 0)" << std::endl << "         ";
                dataFile << "(= (citythreat city0) 0)" << std::endl << "         ";
                for(unsigned i = 1; i < n+1; i++)
                    dataFile << "(= (citythreat city" << i << ") " << c[i-1] << ")" << std::endl << "         ";
                dataFile << "(= (citythreat city" << n+1 << ") 0)" << std::endl << "         ";
                
                // Edges from C_I to C_G
                for(unsigned i = 1; i < n+1; i++)
                {
                    dataFile << std::endl << "; city" << i << std::endl << "         ";
                    dataFile << "(= (timeTerre city0 city" << i << ") " << d[i-1] << ")" << std::endl << "         ";
                    dataFile << "(= (timeTerre city" << i << " city0) " << d[i-1] << ")" << std::endl << "         ";
                    dataFile << "(= (timeTerre city" << n+1 << " city" << i << ") " << d[i-1] << ")" << std::endl << "         ";
                    dataFile << "(= (timeTerre city" << i << " city" << n+1 << ") " << d[i-1] << ")" << std::endl << "         ";
                    for(unsigned j = 1; j < n+1; j++)
                    {
                        if(i != j)
                        {
                            dataFile << "(= (timeTerre city" << i << " city" << j << ") " << d[i-1]+d[j-1]+100 << ")" << std::endl << "         ";
                        }
                    }
                }
                
                dataFile << std::endl << "; plane init" << std::endl << "         ";
                for(unsigned i = 1; i < p+1; i++)
                    dataFile << "(at plane" << i << " city0)" << std::endl << "         ";
                    
                for(unsigned i = 1; i < p+1; i++)
                    dataFile << "(libre plane" << i << ")" << std::endl << "         ";
                
                dataFile << std::endl << "; person init" << std::endl << "         ";
                for(unsigned i = 1; i < t+1; i++)
                    dataFile << "(at person" << i << " city0)" << std::endl << "         ";   
                    
                dataFile << std::endl << ")" << std::endl << "(:goal (and " << std::endl << "         "; 
                for(unsigned i = 1; i < t+1; i++)    
                    dataFile << "(at person" << i << " city" << n+1 <<")" << std::endl << "         ";   
                dataFile << "))" << std::endl;
                
                dataFile << "  (:metric (and (minimize (total-time)) (minimize (total-cost)))))" << std::endl;
            }
            
            if(pareto.size() > 0)
            {
                dataFile << std::endl << "; Pareto points : Makespan - Cost" << std::endl;
                for(auto& i : pareto)
                    dataFile << "; " << i.Mc << " " << i.C << std::endl;
            }    
}

