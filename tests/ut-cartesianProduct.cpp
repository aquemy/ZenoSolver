#include <iostream>
#include <stdexcept>
#include <vector>

#include <combiGenerator.hpp>
#include <ppp.hpp>
#include <utils.hpp>


using namespace std;

int main()
{ 
    vector<PPP> expected;
    
	try 
	{
	    // TEST 1
	    unsigned n = 2;
        unsigned t = 2;
        unsigned p = 1;
	    vector<vector<int>> E = generateTuples(n, t);
        vector<vector<int>> W = generateTuples(n, t-p);
        vector<double> c = {3,2};
        vector<double> d = {2,4};
        
	    vector<PPP> PPPSet = cartesianProduct(E, W, c, d, p);
	    
	    expected.push_back(PPP(0,0,9,12/p,12));
	    expected.push_back(PPP(0,1,8,16/p,16));
	    expected.push_back(PPP(1,0,8,16/p,16));
	    expected.push_back(PPP(1,1,7,20/p,20));
	    expected.push_back(PPP(2,0,7,20/p,20));
	    expected.push_back(PPP(2,1,6,24/p,24));
	    
	    cout << "Computed Cartesian Product : " << endl;
	    dump(PPPSet, E, W);
	    cout << "Expected Cartesian Product : " << endl;
	    dump(expected, E, W);
	    
	    if(expected != PPPSet)
	        throw logic_error("TEST 1 FAILED");
    } 
	catch (exception& e)  // catch any exceptions
	{ 
        cerr << "Error : " << e.what() << endl;
        return 1;
	}

    return 0;
}
