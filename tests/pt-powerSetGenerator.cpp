#include <powerSetGenerator.hpp>
#include <combiGenerator.hpp>

#include <iostream>
#include <algorithm>
#include <vector>
#include <chrono>
#include <map>
#include <set>

#include <random>
#include <iterator>
#include <functional>

using std::chrono::high_resolution_clock;
using std::chrono::milliseconds;

int overCartesianProduct_withMapping(unsigned int n, unsigned int p, unsigned int t)
{
	int EStatus = NEXT;
	std::vector<int> e(t,0);
	while(EStatus == NEXT)
    {
        int WStatus = NEXT;
        auto w = std::vector<int>(t-p,0);
        while(WStatus == NEXT)
        {
            std::vector<int> betaSetValue;
            decltype(w) diff;
            set_difference (begin(w), end(w), begin(e), end(e), back_inserter(diff));
            set_difference (begin(w), end(w), begin(diff), end(diff), back_inserter(betaSetValue));

            unsigned betaMax = betaSetValue.size();
			auto betaPowerSet = std::vector<std::vector<int>>{};
            
            auto mapping = std::map<int, std::pair<int, int>, std::greater<int>>{};
            auto mapping_v = std::vector<int>{};
            unsigned i = 0;
            for(auto it: betaSetValue)
            {
                if(mapping.count(it))
                	mapping[it].first++;
                else {
                    mapping[it] = {1, i};
                    mapping_v.push_back(it);
                    ++i;
                }
            }
            if(i > 1) 
            {    
                auto r = std::vector<std::vector<int>>{};
                for(int i = 0; i <= betaMax; i++) {
                    r = generatePowerSet(r, betaSetValue, mapping_v, mapping, i, mapping_v.size());
                    for(unsigned i = 0; i < r.size(); ++i) 
                    {
                        betaPowerSet.push_back(r[i]);
                    }
                }
            }
            WStatus = nextTuple(w, n, t-p);
        }
        EStatus = nextTuple(e, n, t);
    }
    return true;
}


int overCartesianProduct_naive(unsigned int n, unsigned int p, unsigned int t)
{
	int EStatus = NEXT;
	std::vector<int> e(t,0);
	while(EStatus == NEXT)
    {
        int WStatus = NEXT;
        auto w = std::vector<int>(t-p,0);
        while(WStatus == NEXT)
        {
            std::vector<int> betaSetValue;
            decltype(w) diff;
            set_difference (begin(w), end(w), begin(e), end(e), back_inserter(diff));
            set_difference (begin(w), end(w), begin(diff), end(diff), back_inserter(betaSetValue));

            unsigned betaMax = betaSetValue.size();
			auto powerSet = std::set<std::vector<int>>();
			for(int i = 0; i <= betaMax; i++) 
			{
				naive::generatePowerSet(i, betaSetValue, powerSet);
			}
            WStatus = nextTuple(w, n, t-p);
        }
        EStatus = nextTuple(e, n, t);
    }
    return true;
}

int main() 
{
	//rm pw.txt; for i in `seq 1 10`; do echo "Size $i" && (echo 3 2 $i | ./pt-powerSetGenerator 2>> pw.txt); done
	auto maxTimePerIteration = 10000;
	auto maxIterations = 100;

	auto n = int{3};
	auto p = int{2};
	auto t = int{3};

	//std::cin >> n >> p >> t;
	auto time1 = int{0};
	auto prev_time1 = time1;
	auto delta = int{5};
	auto tolerance = 1.5;
	auto i = int{0};
	while(time1 < maxTimePerIteration && i < maxIterations) 
	{
		std::cout << n << " " << p << " " << t << std::endl;
		prev_time1 = time1;
		auto t01 = high_resolution_clock::now();
		overCartesianProduct_withMapping(n, p, t);
		auto t11 = high_resolution_clock::now();
	    time1 = std::chrono::duration_cast<milliseconds>(t11 - t01).count();
	    std::cout << "Time first method: " << time1 << std::endl;
	    std::cerr << n << " " << p << " " << t << " " << time1 << " " << std::endl;
	    /*
	    if(prev_time1 > 0 && time1 /  double(prev_time1) < tolerance) {
	    	std::cout << "Increase delta t" << std::endl;
	    	delta++;
	    }
	    */
	    n += delta;
	    i++;
	}

	std::cerr << std::endl << std::endl;

	time1 = int{0};
	prev_time1 = time1;
	n = int{3};
	p = int{2};
	t = int{3};
	i = int{0};
   	while(time1 < maxTimePerIteration && i < maxIterations) 
	{
		std::cout << n << " " << p << " " << t << std::endl;
		prev_time1 = time1;
		auto t01 = high_resolution_clock::now();
		overCartesianProduct_naive(n, p, t);
		auto t11 = high_resolution_clock::now();
	    time1 = std::chrono::duration_cast<milliseconds>(t11 - t01).count();
	    std::cout << "Time second method: " << time1 << std::endl;
	    std::cerr << n << " " << p << " " << t << " " << time1 << " " << std::endl;
	    /*
	    if(prev_time1 > 0 && time1 /  double(prev_time1) < tolerance) {
	    	std::cout << "Increase delta t" << std::endl;
	    	delta++;
	    }
	    */
	    n += delta;
	    i++;
	}
    
	return 1;
}