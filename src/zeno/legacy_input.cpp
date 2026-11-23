#include <zeno/legacy_input.hpp>

#include <algorithm>
#include <cmath>
#include <fstream>
#include <functional>
#include <sstream>
#include <stdexcept>
#include <utility>
#include <vector>

namespace zeno::legacy
{
namespace
{
std::function<double(double)> generator(int code)
{
    switch(code)
    {
        case 1: return [](double i) { return std::log(i); };
        case 2: return [](double i) { return std::sqrt(i); };
        case 3: return [](double i) { return i; };
        case 4: return [](double i) { return std::pow(2.0, i); };
        case 5:
            // The 2016 functions take an unsigned argument.
            return [](double i) {
                const auto k = static_cast<unsigned>(i);
                return 5.0 * (k / 2) + 0.1 * (k % 2);
            };
        default: return [](double i) { return i; }; // the 2016 default branch keeps f3
    }
}

// The 2016 generator functions take `unsigned`: the argument is truncated.
double callUnsigned(const std::function<double(double)>& f, double argument)
{
    return f(static_cast<double>(static_cast<unsigned>(argument)));
}

std::vector<std::vector<double>> readRows(const std::string& path, int n)
{
    std::vector<std::vector<double>> rows;
    std::ifstream file(path);
    if(!file)
        throw std::runtime_error("cannot open the data file: " + path);
    for(std::string line; std::getline(file, line);)
    {
        std::istringstream in(line);
        std::vector<double> row;
        for(std::string token; in >> token;)
            row.push_back(std::stoi(token));
        if(row.empty())
            continue;
        if(static_cast<int>(row.size()) != n)
            throw std::runtime_error("the data file is not valid: every line needs n = " + std::to_string(n) + " values");
        rows.push_back(std::move(row));
    }
    return rows;
}
} // namespace

Instance buildInstance(const Options& o)
{
    if(o.n < 1 || o.t < 1 || o.p < 1)
        throw std::invalid_argument("n, t and p must be positive");
    const auto n = static_cast<std::size_t>(o.n);
    std::vector<double> c(n, 1), d(n, 1), de(n, 1);
    bool symmetric = false;

    if(o.dataFile)
    {
        const auto rows = readRows(*o.dataFile, o.n);
        if(rows.size() == 2)
        {
            d = de = rows[0];
            c = rows[1];
            symmetric = true;
        }
        else if(rows.size() == 3)
        {
            d = rows[0];
            de = rows[1];
            c = rows[2];
        }
        else
            throw std::runtime_error("the data file is not valid: expected 2 lines (durations, costs) or 3 lines (west durations, east durations, costs)");
    }
    else
    {
        const auto f = generator(o.costFunction);
        auto g = generator(3), h = generator(3);
        if(o.eastFunction && o.westFunction)
        {
            g = generator(*o.eastFunction);
            h = generator(*o.westFunction);
        }
        else
        {
            symmetric = true;
            g = generator(o.durationFunction);
        }
        for(std::size_t i = 0; i < n; ++i)
            c[i] = o.x * callUnsigned(f, o.scaleC * static_cast<double>(i + 1) + o.transC) + o.y;
        const auto reversed = [&](std::vector<double>& v, const std::function<double(double)>& fn) {
            for(std::size_t i = 0; i < n; ++i)
                v[i] = o.x * callUnsigned(fn, o.scaleD * static_cast<double>(n - i) + o.transD) + o.y;
        };
        reversed(d, g);
        if(!symmetric)
            reversed(de, h);
    }

    // The 2016 conversion to integers truncates toward zero (a cast to int).
    for(auto* v : {&c, &d, &de})
        for(auto& value : *v)
            value = static_cast<double>(static_cast<int>(o.adjust * value));

    if(n > 1 && d[0] > d[1])
    {
        std::swap(d, c);
        std::ranges::reverse(de);
    }
    if(symmetric)
        de = d;

    Instance instance;
    instance.t = o.t;
    instance.p = o.p;
    for(std::size_t i = 0; i < n; ++i)
    {
        instance.d.push_back(static_cast<Time>(d[i]));
        instance.dbar.push_back(static_cast<Time>(de[i]));
        instance.c.push_back(static_cast<Cost>(c[i]));
    }
    instance.validate();
    return instance;
}
} // namespace zeno::legacy
