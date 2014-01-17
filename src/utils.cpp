#include <iostream>
#include <fstream>
#include <iomanip>
#include <vector>
#include <functional>
#include <utils.hpp>
#include <ppp.hpp>

void debugPrint(std::string _title, std::function<void(void)> _f)
{
    std::cerr << std::setfill('=') << std::setw(42) << "=" << std::endl;
    std::cerr << "==" << std::setfill(' ') << std::setw((38 - _title.size()) / 2 + 1) << " ";
    std::cerr << _title;
    std::cerr << std::setfill(' ') << std::setw((38 - _title.size()) / 2 + 1) << "==" << std::endl;
    std::cerr << std::setfill('=') << std::setw(42) << "=" << std::endl;
    _f();
}

void dump(const std::vector<PPP>& _set)
{
    for(auto& ppp : _set)
        std::cerr << ppp << std::endl;
}

bool isReadable(const std::string & _path) 
{ 
    std::ifstream file(_path.c_str()); 
    return !file.fail(); 
} 
