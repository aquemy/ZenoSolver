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
    vector<int> expected;
    unsigned p;
    vector<double> c = {3,2,1};
    vector<double> d = {2,4,6};
    
	try 
	{
        // TEST 1
	    vector<vector<int>> E = {{1,1,1,2,2}};
        vector<vector<int>> W = {{1,1,2}};
        p = 2;
	    vector<PPP> PPPSet = cartesianProduct(E, W, c, d, p);
	    PPPSet[0].computeBetaMax(E,W);

	    expected = {1,1,2};
	    
	    cout << "Computed Beta Set : " << endl;
	    for(auto i : PPPSet[0].betaSet)
	        cout << i << " ";
	    cout << endl;
	    cout << "Expected Beta Set: " << endl;
	    for(auto i : expected)
	        cout << i << " ";
	    cout << endl;
	    
	    if(expected != PPPSet[0].betaSet)
	        throw logic_error("TEST 1 FAILED");
	    
	    // TEST 2
	    E = {{1,1,1,2,2}};
        W = {{0,1,2}};
        p = 2;
	    PPPSet = cartesianProduct(E, W, c, d, p);
	    PPPSet[0].computeBetaMax(E,W);

	    expected = {1,2};
	    
	    cout << "Computed Beta Set : " << endl;
	    for(auto i : PPPSet[0].betaSet)
	        cout << i << " ";
	    cout << endl;
	    cout << "Expected Beta Set: " << endl;
	    for(auto i : expected)
	        cout << i << " ";
	    cout << endl;
	    
	    if(expected != PPPSet[0].betaSet)
	        throw logic_error("TEST 2 FAILED");
	        
	    // TEST 3
	    E = {{2,2,2,2,2}};
        W = {{0,1,2}};
        p = 2;
	    PPPSet = cartesianProduct(E, W, c, d, p);
	    PPPSet[0].computeBetaMax(E,W);

	    expected = {2};
	    
	    cout << "Computed Beta Set : " << endl;
	    for(auto i : PPPSet[0].betaSet)
	        cout << i << " ";
	    cout << endl;
	    cout << "Expected Beta Set: " << endl;
	    for(auto i : expected)
	        cout << i << " ";
	    cout << endl;
	    
	    if(expected != PPPSet[0].betaSet)
	        throw logic_error("TEST 3 FAILED");   
	        
	    // TEST 4
	    E = {{2,2,2,2,2}};
        W = {{1,1,1}};
        p = 2;
	    PPPSet = cartesianProduct(E, W, c, d, p);
	    PPPSet[0].computeBetaMax(E,W);

	    expected = {};
	    
	    cout << "Computed Beta Set : " << endl;
	    for(auto i : PPPSet[0].betaSet)
	        cout << i << " ";
	    cout << endl;
	    cout << "Expected Beta Set: " << endl;
	    for(auto i : expected)
	        cout << i << " ";
	    cout << endl;
	    
	    if(expected != PPPSet[0].betaSet)
	        throw logic_error("TEST 3 FAILED");              
    } 
	catch (exception& e)  // catch any exceptions
	{ 
        cerr << "Error : " << e.what() << endl;
        return 1;
	}
	*/

    return 0;
}
