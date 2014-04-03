#include <iostream>
#include <stdexcept>
#include <vector>

#include <algorithm.hpp>

using namespace std;

int main()
{
    // Old version
    // TODO : new one ! :-)
    /*
    double upperBound;
    double expected;
    unsigned p;
    vector<double> c = {3,2,1};
    
	try 
	{
        // TEST 1
	    vector<vector<int>> E = {{1,1,1,2,2}};
        vector<vector<int>> W = {{1,1,2}};
        vector<double> d = {2,4,6};
        p = 2;
	    vector<PPP> PPPSet = cartesianProduct(E, W, c, d, p);
	    upperBound = SimpleUpperBound(PPPSet[0], E, W, d, p);
	    expected = 44;
	    
	    cout << "Computed Upper Bound : " << upperBound << endl;
	    cout << "Expected Upper Bound : " << expected << endl;
	    
	    if(expected != upperBound)
	        throw logic_error("TEST 1 FAILED");
	        
	    // TEST 2
	    E = {{1,1,1,2,2}};
        W = {{1,1,2}};
        d = {2,3,12};
        p = 2;
	    PPPSet = cartesianProduct(E, W, c, d, p);
	    upperBound = SimpleUpperBound(PPPSet[0], E, W, d, p);
	    expected = 54;
	    
	    cout << "Computed Upper Bound : " << upperBound << endl;
	    cout << "Expected Upper Bound : " << expected << endl;
	    
	    if(expected != upperBound)
	        throw logic_error("TEST 2 FAILED");
	        
	    // TEST 3
	    E = {{1,1,1,2,2}};
        W = {{1,2}};
        d = {2,4,6};
        p = 3;
	    PPPSet = cartesianProduct(E, W, c, d, p);
	    upperBound = SimpleUpperBound(PPPSet[0], E, W, d, p);
	    expected = 28;
	    
	    cout << "Computed Upper Bound : " << upperBound << endl;
	    cout << "Expected Upper Bound : " << expected << endl;
	    
	    if(expected != upperBound)
	        throw logic_error("TEST 3 FAILED");
	    
	    // TEST 4
	    E = {{1,1,1,2,2}};
        W = {{1,2}};
        d = {2,3,12};
        p = 3;
	    PPPSet = cartesianProduct(E, W, c, d, p);
	    upperBound = SimpleUpperBound(PPPSet[0], E, W, d, p);
	    expected = 36;
	    
	    cout << "Computed Upper Bound : " << upperBound << endl;
	    cout << "Expected Upper Bound : " << expected << endl;
	    
	    if(expected != upperBound)
	        throw logic_error("TEST 4 FAILED");         
    } 
	catch (exception& e)  // catch any exceptions
	{ 
        cerr << "Error : " << e.what() << endl;
        return 1;
	}*/

    return 0;
}
