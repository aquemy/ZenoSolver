#include <zeno/legacy_input.hpp>

#include <algorithm>
#include <cmath>
#include <fstream>
#include <functional>
#include <optional>
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

struct DataFile
{
    std::vector<std::vector<double>> rows;                 ///< durations and costs
    std::optional<std::vector<std::vector<double>>> table; ///< after the line "central"
};

DataFile readDataFile(const std::string& path, int n)
{
    DataFile data;
    std::ifstream file(path);
    if(!file)
        throw std::runtime_error("cannot open the data file: " + path);
    for(std::string line; std::getline(file, line);)
    {
        std::istringstream in(line);
        std::vector<std::string> tokens;
        for(std::string token; in >> token;)
            tokens.push_back(token);
        if(tokens.empty())
            continue;
        if(tokens.front() == "central")
        {
            if(data.table || tokens.size() != 1)
                throw std::runtime_error("the data file is not valid: 'central' must appear once, alone on its line");
            data.table.emplace();
            continue;
        }
        std::vector<double> row;
        for(const auto& token : tokens)
            row.push_back(std::stoi(token));
        if(static_cast<int>(row.size()) != n)
            throw std::runtime_error("the data file is not valid: every line needs n = " + std::to_string(n) + " values");
        (data.table ? *data.table : data.rows).push_back(std::move(row));
    }
    if(data.table && static_cast<int>(data.table->size()) != n)
        throw std::runtime_error("the data file is not valid: the central-flight table needs n = " + std::to_string(n) + " rows");
    return data;
}

double truncated(double adjust, double value)
{
    // The 2016 conversion to integers truncates toward zero (a cast to int).
    return static_cast<double>(static_cast<int>(adjust * value));
}
} // namespace

std::vector<Cost> generatedCosts(const Options& o, double adjust)
{
    const auto f = generator(o.costFunction);
    std::vector<Cost> c;
    for(int i = 1; i <= o.n; ++i)
        c.push_back(static_cast<Cost>(truncated(adjust, o.x * callUnsigned(f, o.scaleC * static_cast<double>(i) + o.transC) + o.y)));
    return c;
}

Instance buildInstance(const Options& o)
{
    if(o.n < 1 || o.t < 1 || o.p < 1)
        throw std::invalid_argument("n, t and p must be positive");
    const auto n = static_cast<std::size_t>(o.n);
    std::vector<double> c(n, 1), d(n, 1), de(n, 1);
    bool symmetric = false;
    std::optional<std::vector<std::vector<double>>> table;

    if(o.dataFile)
    {
        auto data = readDataFile(*o.dataFile, o.n);
        const auto& rows = data.rows;
        table = std::move(data.table);
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
            throw std::runtime_error("the data file is not valid: expected 2 lines (durations, costs) or 3 lines (west durations, east durations, costs)"
                                     ", then optionally the line 'central' and the central-flight table");
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

    for(auto* v : {&c, &d, &de})
        for(auto& value : *v)
            value = truncated(o.adjust, value);

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
    if(table)
    {
        FlightTable central;
        for(const auto& row : *table)
        {
            central.emplace_back();
            for(double value : row)
                central.back().push_back(static_cast<Time>(truncated(o.adjust, value)));
        }
        instance.central = std::move(central);
    }
    instance.validate();
    return instance;
}
} // namespace zeno::legacy
