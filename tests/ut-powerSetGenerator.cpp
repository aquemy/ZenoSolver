#include <iostream>
#include <stdexcept>
#include <vector>

#include <powerSetGenerator.hpp>

using namespace std;

int main()
{
    vector<vector<unsigned>> powerSet;
    decltype(powerSet) expected;
    vector<int> v = {3,4,2,9};

	try 
	{
	    // TEST 1 : Only one element
	    generatePowerSet(1, 1, v, powerSet);
	    expected = {{3}};
	    
	    cout << "Computed PowerSet : " << endl;
	    for(auto set : powerSet)
	    {
	        for(auto i : set)
	            cout << i << " ";
	        cout << endl;
	    }
	    cout << "Expected PowerSet : " << endl;
	    for(auto set : expected)
	    {
	        for(auto i : set)
	            cout << i << " ";
	        cout << endl;
	    }
	    
	    if(expected != powerSet)
	        throw logic_error("TEST 1 FAILED");
	        
	    // TEST 2 : One element in all
	    powerSet.clear();
	    generatePowerSet(4, 1, v, powerSet);
	    decltype(powerSet) expected = {{3},{4},{2},{9}};
	    
	    cout << "Computed PowerSet : " << endl;
	    for(auto set : powerSet)
	    {
	        for(auto i : set)
	            cout << i << " ";
	        cout << endl;
	    }
	    cout << "Expected PowerSet : " << endl;
	    for(auto set : expected)
	    {
	        for(auto i : set)
	            cout << i << " ";
	        cout << endl;
	    }
	    
	    if(expected != powerSet)
	        throw logic_error("TEST 2 FAILED");
	        
	    // TEST 3 : All elements in all
	    powerSet.clear();
	    generatePowerSet(4, 4, v, powerSet);
	    expected = {{3,4,2,9}};
	    
	    cout << "Computed PowerSet : " << endl;
	    for(auto set : powerSet)
	    {
	        for(auto i : set)
	            cout << i << " ";
	        cout << endl;
	    }
	    cout << "Expected PowerSet : " << endl;
	    for(auto set : expected)
	    {
	        for(auto i : set)
	            cout << i << " ";
	        cout << endl;
	    }
	    
	    if(expected != powerSet)
	        throw logic_error("TEST 1 FAILED");
	        
	    // TEST 3 : 2 elements in all
	    powerSet.clear();
	    generatePowerSet(4, 2, v, powerSet);
	    expected = {{3,4},
	                {3,2},
	                {4,2},
	                {3,9},
	                {4,9},
	                {2,9},
	                };
	    
	    cout << "Computed PowerSet : " << endl;
	    for(auto set : powerSet)
	    {
	        for(auto i : set)
	            cout << i << " ";
	        cout << endl;
	    }
	    cout << "Expected PowerSet : " << endl;
	    for(auto set : expected)
	    {
	        for(auto i : set)
	            cout << i << " ";
	        cout << endl;
	    }
	    
	    if(expected != powerSet)
	        throw logic_error("TEST 3 FAILED");        

    } 
	catch (exception& e)  // catch any exceptions
	{ 
        cerr << "Error : " << e.what() << endl;
        return 1;
	}

    return 0;
}
