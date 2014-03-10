#include <iostream>
#include <fstream>
#include <string>  
#include <cmath>  
#include <iomanip>  
#include <vector>
#include <combiGenerator.hpp>

int nextTuple(std::vector<int>& vec, const int n, const int k)
{
    int j;

    if(vec[k-1] < n - 1)
    {
        vec[k - 1]++;
        return(NEXT);
    }

    for(j = k - 2; j >= 0; j--)
        if(vec[j] != n - 1)
            break;

    if(j < 0)
        return(DONE);

    vec[j]++;

    for(j += 1; j < k; j++)
        vec[j] = vec[j - 1];

    return(NEXT);
}

