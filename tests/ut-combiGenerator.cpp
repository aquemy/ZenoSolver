#include <iostream>
#include <stdexcept>
#include <vector>
#include <map>

#include <combiGenerator.hpp>
#include <paretoExtraction.hpp>

#include <algorithm.hpp>
#include <algorithm>

//#ifdef _OPENMP
#include <omp.h>
//#endif // _OPENMP

bool test_combi(int k, int n, const std::vector<std::vector<int>>& expected, bool print = true) 
{
	int statut = NEXT;
	std::vector<int> ppp(k, 0);
	std::vector<std::vector<int>> combi_set;

    while(statut == NEXT)
    {
    	combi_set.push_back(ppp);
    	statut = nextTuple(ppp, n, k);
    }

	if(print) 
	{
		std::cout << "Computed Combi Set : " << std::endl;
		for(auto set : combi_set)
		{
		    for(auto i : set)
		        std::cout << i << " ";
		    std::cout << std::endl;
		}
		std::cout << "Expected Combi Set : " << std::endl;
		for(auto set : expected)
		{
		    for(auto i : set)
		        std::cout << i << " ";
		    std::cout << std::endl;
		}
	}

	try 
	{
		if(expected != combi_set)
		    throw std::logic_error("TEST 1 FAILED");
	}
	catch (std::exception& e)  // catch any exceptions
	{ 
        std::cerr << "Error : " << e.what() << std::endl;
        return false;
	}
	return true;
}


int computeMakespan(
    const std::vector<int>& a,
    const std::vector<int>& ab,
    const std::vector<int>& b,
    const std::vector<double>& d,
    const std::vector<double>& de,
    unsigned p)
{
    using std::begin;
    using std::end;
   
    std::vector<Si> S(p);
        
    auto itE = begin(a);
    auto itW = begin(ab);
    auto itP = begin(S);

    //std::cout << "a ab b - " << a << " " << ab << " " << b << std::endl;

    // Open the P3
    if(p >= b.size()) { // Avoid finding the min element that is costly
        for(unsigned i = 0; i < b.size(); ++i)
            S[i].m = 2*std::max(d[b[i]], de[b[i]]);
    }
    else {
        for(const auto i : b)
        {
            itP = min_element(begin(S), end(S), compM);
            itP->m += 2*std::max(d[i], de[i]);
        }
    }

    //for(auto i : S)
    //	std::cout << "p " << i.m << std::endl;

    // We give one P1 to every plane by plan constraint
    for(unsigned i = 0; i < p; ++i) 
    {
        itP = min_element(begin(S), end(S), compM);
        //std::cout << "  itE " << itE << " ppp[itE] " << ppp[itE] << " add " << d[ppp[itE]] << " " << de[ppp[itE]] << std::endl;
        itP->m += d[*itE] + de[*itE];
        itE++;
    }

    //for(auto i : S)
    //	std::cout << "p1 " << i.m << std::endl;

    for(unsigned i = 0; i < ab.size(); ++i)
    {
        itP = min_element(begin(S), end(S), compM);
        itP->m += d[*itE] + de[*itE];
        itE++;
        itP->m += d[*itW] + de[*itW];
        itW++;
    }

    //for(auto i : S)
    //	std::cout << "p3 " << i.m << std::endl;

    // We close the P3
    for(const auto i : b)
    {
        itP = min_element(begin(S), end(S), compM);
        itP->m += 2*std::min(d[i], de[i]);
    }

    return std::max_element(begin(S),end(S), compM)->m;
}


bool test_ppp(int t, int p, int n, const std::vector<std::vector<int>>& expected, bool print = true) 
{
	
	
	//std::vector<int> ppp(2*t - p, 0);
	std::vector<std::vector<int>> combi_set;

    auto d = std::vector<double>{1,2,3,4,5};
    auto de = std::vector<double>{1,2,3,4,5};
    auto c = std::vector<double>{10,8,6,4,2};

    std::map<int, int> front;
    std::map<int, int> best_reached;

    bool pruning = false;
    int dominated_count = 0;

    #pragma omp parallel for schedule(dynamic)//(nonmonotonic:dynamic)
	for(unsigned k = 0; k < t - p + 1; ++k)
	//unsigned k = t - p;
    {
    	int a = k + p;
    	int ab = a - p;
    	int b = t - a;
    	int C = 0;
    	//std::cout << "k a b ab: " << k << " " << a << " " << b << " " << ab << std::endl;
    	std::vector<int> ppp_a(a, 0);
    	int AStatut = NEXT;
    	int ABStatut = NEXT;
		int BStatut = NEXT;
    	int count = 0;
	    while(AStatut == NEXT)
	    {

	    	std::vector<int> ppp_ab(ab, 0);
	    	ABStatut = NEXT;
	    	while(ABStatut == NEXT)
	    	{
    			std::vector<int> ppp_b(b, 0);
		    	BStatut = NEXT;
		    	while(BStatut == NEXT)
		    	{
		    		C = 0;
		    		for(auto i: ppp_a)
		    			C += c[i];
		    		for(auto i: ppp_ab)
		    			C += c[i];
		    		for(auto i: ppp_b)
		    			C += 2*c[i];
					
					int Mc = 0;
	                for_each(begin(ppp_a), end(ppp_a),[&](unsigned i) { Mc += d[i] + de[i]; });
	                for_each(begin(ppp_ab), end(ppp_ab),[&](unsigned i) { Mc += d[i] + de[i]; });
	                for_each(begin(ppp_b), end(ppp_b),[&](unsigned i) { Mc += d[i] + de[i]; });

		    		//auto me = *std::max_element(begin(e), end(e),[&](unsigned i, unsigned j) { return d[i] + de[i] < d[j] + de[j]; });
	                //auto mw = *std::max_element(begin(w), end(w),[&](unsigned i, unsigned j) { return d[i] + de[i] < d[j] + de[j]; });
	                int Ml = Mc / p;
	                //Ml = std::max(double(Ml), d[me] + de[me]);
	                //Ml = std::max(double(Ml), d[mw] + de[mw]);

	                bool dominated = false;
	                if (!front.count(C))
                    	front[C] = Mc;
	                if(pruning)
	                {

	                    //for(auto i = front.find(C); i != --begin(front); --i)
	                    
	                    {
	                        //if(i->second <= Ml)
	                        if(front.count(C) && front[C] <= Ml)
	                        {
	                            dominated = true;
	                            //std::cout << "DOMINATED" << std::endl;
	                            //++dominated_count;
	                            break;
	                        }
	                    }
	                }


		    		auto M = computeMakespan(ppp_a, ppp_ab, ppp_b, d, de, p);

		    		if(!front.count(C) || front[C] > M) {
    					front[C] = M;
    					//if(pruning)
    					if(false)
	                	{
	                		for(auto i = front.find(C); i != begin(front); --i) {
	                			if(i->second > C)
	                				i->second = C;
	                		}
	                	}
		    		}
		    		
					for(auto i: ppp_a)
						std::cout << i << " ";
					std::cout << "| ";
					for(auto i: ppp_ab)
						std::cout << i << " ";
					std::cout << "| ";
					for(auto i: ppp_b)
						std::cout << i << " ";
					//std::cout << " | C: " << C << " | M: " << M << std::endl;
					//*/
					std::cerr << " | C: " << C << " | M: " << Ml << " < " << Mc << " < " << M << std::endl;
					
					count++;
					if(b == 0) {
						BStatut = DONE;
					} else
						BStatut = nextTuple(ppp_b, n, b);
				}
				if(ab == 0) {
					ABStatut = DONE;
				} else
					ABStatut = nextTuple(ppp_ab, n, ab);
    		}
    		AStatut = nextTuple(ppp_a, n, a);
    	}
    	std::cout << "COUNT: " << count << std::endl;

    	//std::cerr << std::endl << std::endl;
    }
    std::cout << "DOMINATED COUNT: " << dominated_count << std::endl;
    auto pareto = paretoExtraction(front);
    std::cout << "FRONT SIZE: " << pareto.size() << std::endl;
    for(auto& i : pareto)
    	std::cerr << i.second << " " << i.first << std::endl;
}

bool test_ppp_(int t, int p, int n, const std::vector<std::vector<int>>& expected, bool print = true) 
{
	int AStatut = NEXT;
	int ABStatut = NEXT;
	int BStatut = NEXT;
	//std::vector<int> ppp(2*t - p, 0);
	std::vector<std::vector<int>> combi_set;

	int a;
    int ab;
    int b;
    int C = 0;

    auto d = std::vector<double>{1,2,3,4,5};
    auto de = std::vector<double>{1,2,3,4,5};
    auto c = std::vector<double>{10,8,6,4,2};

    std::map<int, int> front;
    std::map<int, int> best_reached;

    bool pruning = false;
    int dominated_count = 0;

    //#pragma omp parallel for
	for(unsigned k = 0; k < t - p + 1; ++k)
	//unsigned k = t - p;
    {
    	a = k + p;
    	ab = a - p;
    	b = t - a;
    	//std::cout << "k a b ab: " << k << " " << a << " " << b << " " << ab << std::endl;
    	std::vector<int> ppp_a(a, 0);
    	AStatut = NEXT;
    	int count = 0;
	    while(AStatut == NEXT)
	    {

	    	std::vector<int> ppp_ab(ab, 0);
	    	ABStatut = NEXT;
	    	while(ABStatut == NEXT)
	    	{
    			std::vector<int> ppp_b(b, 0);
		    	BStatut = NEXT;
		    	while(BStatut == NEXT)
		    	{
		    		C = 0;
		    		for(auto i: ppp_a)
		    			C += c[i];
		    		for(auto i: ppp_ab)
		    			C += c[i];
		    		for(auto i: ppp_b)
		    			C += 2*c[i];
					
					int Mc = 0;
	                for_each(begin(ppp_a), end(ppp_a),[&](unsigned i) { Mc += d[i] + de[i]; });
	                for_each(begin(ppp_ab), end(ppp_ab),[&](unsigned i) { Mc += d[i] + de[i]; });
	                for_each(begin(ppp_b), end(ppp_b),[&](unsigned i) { Mc += d[i] + de[i]; });

		    		//auto me = *std::max_element(begin(e), end(e),[&](unsigned i, unsigned j) { return d[i] + de[i] < d[j] + de[j]; });
	                //auto mw = *std::max_element(begin(w), end(w),[&](unsigned i, unsigned j) { return d[i] + de[i] < d[j] + de[j]; });
	                int Ml = Mc / p;
	                //Ml = std::max(double(Ml), d[me] + de[me]);
	                //Ml = std::max(double(Ml), d[mw] + de[mw]);

	                bool dominated = false;
	                if (!front.count(C))
                    	front[C] = Mc;
	                if(pruning)
	                {

	                    //for(auto i = front.find(C); i != --begin(front); --i)
	                    
	                    {
	                        //if(i->second <= Ml)
	                        if(front.count(C) && front[C] <= Ml)
	                        {
	                            dominated = true;
	                            //std::cout << "DOMINATED" << std::endl;
	                            ++dominated_count;
	                            break;
	                        }
	                    }
	                }


		    		auto M = computeMakespan(ppp_a, ppp_ab, ppp_b, d, de, p);

		    		if(!front.count(C) || front[C] > M) {
    					front[C] = M;
    					//if(pruning)
    					if(false)
	                	{
	                		for(auto i = front.find(C); i != begin(front); --i) {
	                			if(i->second > C)
	                				i->second = C;
	                		}
	                	}
		    		}
		    		/*
					for(auto i: ppp_a)
						std::cout << i << " ";
					std::cout << "| ";
					for(auto i: ppp_ab)
						std::cout << i << " ";
					std::cout << "| ";
					for(auto i: ppp_b)
						std::cout << i << " ";
					std::cout << " | C: " << C << " | M: " << M << std::endl;
					*/
					//std::cerr << C << " " << Ml << " " << Mc << " " << M << std::endl;
					
					count++;
					if(b == 0) {
						BStatut = DONE;
					} else
						BStatut = nextTuple(ppp_b, n, b);
				}
				if(ab == 0) {
					ABStatut = DONE;
				} else
					ABStatut = nextTuple(ppp_ab, n, ab);
    		}
    		AStatut = nextTuple(ppp_a, n, a);
    	}
    	std::cout << "COUNT: " << count << std::endl;

    	//std::cerr << std::endl << std::endl;
    }
    std::cout << "DOMINATED COUNT: " << dominated_count << std::endl;
    auto pareto = paretoExtraction(front);
    std::cout << "FRONT SIZE: " << pareto.size() << std::endl;
    for(auto& i : pareto)
    	std::cerr << i.second << " " << i.first << std::endl;
}


int main()
{
	auto k = int{1};
	auto n = int{0};
	auto expected = std::vector<std::vector<int>>{{0}};
	/*
	test_combi(k, n, expected);

	k = int{1};
	n = int{1};
	expected = std::vector<std::vector<int>>{{0}};
	test_combi(k, n, expected);

	k = int{1};
	n = int{2};
	expected = std::vector<std::vector<int>>{{0}, {1}};
	test_combi(k, n, expected);

	k = int{1};
	n = int{10};
	expected = std::vector<std::vector<int>>(n);
	for(int i = 0; i < n; ++i)
		expected[i] = std::vector<int>(1, i);
	test_combi(k, n, expected);

	k = int{5};
	n = int{1};
	expected = std::vector<std::vector<int>>(1);
	expected[0] = std::vector<int>(k, 0);
	test_combi(k, n, expected);

	k = int{5};
	n = int{2};
	expected = std::vector<std::vector<int>>{
		{0,0,0,0,0}, {0,0,0,0,1}, {0,0,0,1,1},
		{0,0,1,1,1}, {0,1,1,1,1}, {1,1,1,1,1}
	};
	test_combi(k, n, expected);

	k = int{3};
	n = int{3};
	expected = std::vector<std::vector<int>>{
		{0,0,0}, {0,0,1}, {0,0,2}, {0,1,1},
		{0,1,2}, {0,2,2}, {1,1,1}, {1,1,2},
		{1,2,2}, {2,2,2}        
	};
	test_combi(k, n, expected);
	*/
	test_ppp(4, 2, 4, expected);




    return 0;
}
