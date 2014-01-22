#include <iostream>
#include <fstream>
#include <string>  
#include <cmath>  
#include <iomanip>  
#include <vector>
#include <combiGenerator.hpp>

int nextTuple(std::vector<int>& vec, const int n, const int k)
{
    int j; //index

    //easy case, increase rightmost element
    if(vec[k - 1] < n - 1)
    {
        vec[k - 1]++;
        return(GEN_NEXT);
    }

    //find rightmost element to increase
    for(j = k - 2; j >= 0; j--)
        if(vec[j] != n - 1)
            break;

    //terminate if all elements are n - 1
    if(j < 0)
        return(GEN_TERM);

    //increase
    vec[j]++;

    //set right-hand elements
    for(j += 1; j < k; j++)
        vec[j] = vec[j - 1];

    return(GEN_NEXT);
}

std::vector<std::vector<int>> generateTuples(const int n, const int k, bool serialize)
{
    int genResult = GEN_NEXT;

    std::vector<int> tuple(k,0);
    
    std::vector<std::vector<int>> set;
    while(genResult == GEN_NEXT)
    {
        set.push_back(tuple);
        genResult = nextTuple(tuple, n, k);
    }
    
    if(serialize)
    {
        std::ofstream file("tuple_"+std::to_string(n)+"_"+std::to_string(k)+".dat");
        for(auto s : set)
        {
            for(auto i : s)
                file << i << " ";
            file << std::endl;
        }
    }
    return std::move(set);
}

std::vector<std::vector<int>> readTuples(const int n, const int k)
{
    std::vector<std::vector<int>> set;
    std::vector<int> tuple(k,0);
    std::ofstream file("tuple_"+std::to_string(n)+"_"+std::to_string(k)+".dat");
    std::string line;

    return set;
}
