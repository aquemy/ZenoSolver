#include <iostream>
#include <stdexcept>
#include <vector>

#include <combiGenerator.hpp>

using namespace std;

int main()
{
    vector<vector<int>> E;
    decltype(E) expected;
    
	try 
	{
	    // WITHOUT SERIALIZATION
	    // TEST 1 : One in one
        E = generateTuples(1, 1);
        expected = {{0}};
        
	    cout << "Computed TupleSet : " << endl;
	    for(auto tuple : E)
	    {
	        for(auto i : tuple)
	            cout << i << " ";
	        cout << endl;
	    }
	    cout << "Expected TupleSet : " << endl;
	    for(auto tuple : expected)
	    {
	        for(auto i : tuple)
	            cout << i << " ";
	        cout << endl;
	    }
	    
	    if(expected != E)
	        throw logic_error("TEST 1 FAILED");
	        
	    // TEST 2 : One in one
        E = generateTuples(2, 1);
        expected = {{0}, {1}};
        
	    cout << "Computed TupleSet : " << endl;
	    for(auto tuple : E)
	    {
	        for(auto i : tuple)
	            cout << i << " ";
	        cout << endl;
	    }
	    cout << "Expected TupleSet : " << endl;
	    for(auto tuple : expected)
	    {
	        for(auto i : tuple)
	            cout << i << " ";
	        cout << endl;
	    }	    
	    
	    if(expected != E)
	        throw logic_error("TEST 1 FAILED");
	        
	        
	    // TEST 3 : Two in one
        E = generateTuples(2, 2);
        expected = {{0,0}, {0,1}, {1,1}};
        
	    cout << "Computed TupleSet : " << endl;
	    for(auto tuple : E)
	    {
	        for(auto i : tuple)
	            cout << i << " ";
	        cout << endl;
	    }
	    cout << "Expected TupleSet : " << endl;
	    for(auto tuple : expected)
	    {
	        for(auto i : tuple)
	            cout << i << " ";
	        cout << endl;
	    }	    
	    
	    if(expected != E)
	        throw logic_error("TEST 3 FAILED");
	    
    } 
	catch (exception& e)  // catch any exceptions
	{ 
        cerr << "Error : " << e.what() << endl;
        return 1;
	}

    return 0;
}
