#include <iostream>
#include <algorithm>
#include <stdexcept>
#include <vector>

#include <powerSetGenerator.hpp>

bool test_powerSet(const std::vector<int>& setValue, const std::vector<std::vector<int>>& expected, bool print = true) 
{
	auto mapping = std::map<int, std::pair<int, int>, std::greater<int>>{};
    auto mapping_v = std::vector<int>{};
    unsigned i = calculateMapping(setValue, mapping, mapping_v);
	auto powerSet = std::vector<std::vector<int>>{};

	auto r = std::vector<std::vector<int>>{};
    for(int i = 0; i <= setValue.size(); i++) {
        r = generatePowerSet(r, setValue, mapping_v, mapping, i, mapping_v.size());
        for(unsigned i = 0; i < r.size(); ++i) {
            powerSet.push_back(r[i]);
        }
    } 

	if(print) 
	{
		std::cout << "Computed PowerSet : " << std::endl;
		for(auto set : powerSet)
		{
		    for(auto i : set)
		        std::cout << i << " ";
		    std::cout << std::endl;
		}
		std::cout << "Expected PowerSet : " << std::endl;
		for(auto set : expected)
		{
		    for(auto i : set)
		        std::cout << i << " ";
		    std::cout << std::endl;
		}
	}

	try 
	{
		if(expected != powerSet)
		    throw std::logic_error("TEST FAILED");
	}
	catch (std::exception& e)  // catch any exceptions
	{ 
        std::cerr << "Error : " << e.what() << std::endl;
        return false;
	}
	return true;
}


int main()
{
	auto setValue = std::vector<int>{};
	auto expected = std::vector<std::vector<int>>{};
	test_powerSet(setValue, expected);

	setValue = std::vector<int>{0};
	expected = std::vector<std::vector<int>>{{0}};
	test_powerSet(setValue, expected);

	setValue = std::vector<int>{1};
	expected = std::vector<std::vector<int>>{{1}};
	test_powerSet(setValue, expected);

	setValue = std::vector<int>{9999};
	expected = std::vector<std::vector<int>>{{9999}};
	test_powerSet(setValue, expected);

	setValue = std::vector<int>{5,6};
	expected = std::vector<std::vector<int>>{{5}, {6}, {5,6}};
	test_powerSet(setValue, expected);

	setValue = std::vector<int>{5,5};
	expected = std::vector<std::vector<int>>{{5}, {5,5}};
	test_powerSet(setValue, expected);

	setValue = std::vector<int>{5,9};
	expected = std::vector<std::vector<int>>{{5}, {9}, {5,9}};
	test_powerSet(setValue, expected);

	int n = {10};
	setValue = std::vector<int>(n, 5);
	expected = std::vector<std::vector<int>>(n);
	for(int i = 0; i < n; ++i)
		expected[i] = std::vector<int>(i+1, 5);
	test_powerSet(setValue, expected);

	n = {2};
	setValue = std::vector<int>{3,2,2,1,1};
	expected = std::vector<std::vector<int>>{
		{3},{2},{1},
		{3,2},{3,1},{2,2},{2,1},{1,1},
		{3,2,2},{3,2,1},{3,1,1},{2,2,1},{2,1,1},
		{3,2,2,1}, {3,2,1,1},{2,2,1,1},
		{3,2,2,1,1}
	};
	test_powerSet(setValue, expected);

    return 0;
}
