#include <zeno/metric.hpp>

#include <algorithm>
#include <cmath>
#include <fstream>
#include <limits>
#include <numbers>
#include <random>
#include <sstream>
#include <stdexcept>

namespace zeno::metric
{
namespace
{
std::size_t at(int v) { return static_cast<std::size_t>(v); }

double radians(double degrees) { return degrees * std::numbers::pi / 180.0; }

/// Uniform in [0, 1), from the 53 high bits: the same on every platform,
/// unlike std::uniform_real_distribution.
double unit(std::mt19937_64& engine) { return static_cast<double>(engine() >> 11) * 0x1.0p-53; }

Point randomPoint(Geometry geometry, std::mt19937_64& engine)
{
    const double u = unit(engine), v = unit(engine);
    if(geometry == Geometry::Plane)
        return {kSquareSide * u, kSquareSide * v};
    // Uniform on the sphere: the sine of the latitude is uniform in [-1, 1].
    return {std::asin(2 * u - 1) * 180.0 / std::numbers::pi, 360.0 * v - 180.0};
}

std::optional<double> number(const std::string& token)
{
    std::size_t used = 0;
    double v = 0;
    try
    {
        v = std::stod(token, &used);
    }
    catch(const std::exception&)
    {
        return std::nullopt;
    }
    if(used != token.size() || !std::isfinite(v))
        return std::nullopt;
    return v;
}

// Durations fit the int values of data files (so `zeno generate` output reads
// back), and stay far below the overflow of every sum in the solver.
constexpr double kMaxDuration = static_cast<double>(std::int64_t{1} << 31);
} // namespace

double distance(Geometry geometry, const Point& a, const Point& b)
{
    if(geometry == Geometry::Plane)
        return std::hypot(a.x - b.x, a.y - b.y);
    const double lat1 = radians(a.x), lat2 = radians(b.x);
    const double sinLat = std::sin((lat2 - lat1) / 2), sinLon = std::sin(radians(b.y - a.y) / 2);
    const double h = sinLat * sinLat + std::cos(lat1) * std::cos(lat2) * sinLon * sinLon;
    return 2 * kEarthRadius * std::asin(std::min(1.0, std::sqrt(h)));
}

Layout randomLayout(Geometry geometry, Hubs hubs, int n, std::uint64_t seed)
{
    std::mt19937_64 engine(seed);
    Layout layout;
    layout.hubs.push_back(randomPoint(geometry, engine));
    for(int i = 0; i < n; ++i)
        layout.cities.push_back(randomPoint(geometry, engine));
    if(hubs == Hubs::Apart)
        layout.hubs.push_back(randomPoint(geometry, engine));
    return layout;
}

Layout readLayout(const std::string& path, Geometry geometry, Hubs hubs)
{
    std::ifstream file(path);
    if(!file)
        throw std::runtime_error("cannot open the coordinates file: " + path);
    std::vector<Point> points;
    int lineNumber = 0;
    for(std::string line; std::getline(file, line);)
    {
        ++lineNumber;
        const auto where = path + ", line " + std::to_string(lineNumber) + ": ";
        std::replace(line.begin(), line.end(), ',', ' ');
        std::istringstream words(line);
        std::vector<std::string> tokens;
        for(std::string w; words >> w;)
            tokens.push_back(w);
        if(tokens.empty() || tokens.front().starts_with('#'))
            continue;
        if(tokens.size() == 3 && !number(tokens.front()))
            tokens.erase(tokens.begin()); // a label
        if(tokens.size() != 2)
            throw std::runtime_error(where + "expected two coordinates, optionally after a label");
        const auto x = number(tokens[0]), y = number(tokens[1]);
        if(!x || !y)
            throw std::runtime_error(where + "the coordinates are not numbers");
        if(geometry == Geometry::Sphere && std::abs(*x) > 90)
            throw std::runtime_error(where + "a latitude lies in [-90, 90] (the file lists lat,lon)");
        points.push_back({*x, *y});
    }
    const std::size_t hubCount = hubs == Hubs::Same ? 1 : 2;
    if(points.size() <= hubCount)
        throw std::runtime_error("the coordinates file " + path + " needs " + (hubs == Hubs::Same ? "the hub" : "C_I, C_G") +
                                 " and at least one central city");
    Layout layout;
    layout.hubs.assign(points.begin(), points.begin() + static_cast<std::ptrdiff_t>(hubCount));
    layout.cities.assign(points.begin() + static_cast<std::ptrdiff_t>(hubCount), points.end());
    return layout;
}

Durations roundedDurations(const Layout& layout, Geometry geometry, double scale)
{
    if(!(scale > 0) || !std::isfinite(scale))
        throw std::invalid_argument("metric instances need a positive scale (-r)");
    if(layout.hubs.empty() || layout.hubs.size() > 2)
        throw std::invalid_argument("a layout has one or two hubs");
    // Locations: the hubs (C_I, then C_G if apart), then the central cities.
    std::vector<Point> points = layout.hubs;
    points.insert(points.end(), layout.cities.begin(), layout.cities.end());
    const int hubs = static_cast<int>(layout.hubs.size());
    const int m = static_cast<int>(points.size());
    constexpr Time kNone = std::numeric_limits<Time>::max() / 4;
    std::vector<std::vector<Time>> w(at(m), std::vector<Time>(at(m), 0));
    for(int a = 0; a < m; ++a)
        for(int b = a + 1; b < m; ++b)
        {
            Time value = kNone;
            if(!(hubs == 2 && a == 0 && b == 1)) // no flight C_I - C_G
            {
                const double scaled = std::round(scale * distance(geometry, points[at(a)], points[at(b)]));
                if(!(scaled < kMaxDuration))
                    throw std::invalid_argument("metric durations reach 2^31: lower -r");
                value = static_cast<Time>(scaled);
            }
            w[at(a)][at(b)] = w[at(b)][at(a)] = value;
        }
    // Shortest paths (Floyd-Warshall) over the flights, in integers.
    for(int x = 0; x < m; ++x)
        for(int a = 0; a < m; ++a)
            for(int b = 0; b < m; ++b)
                w[at(a)][at(b)] = std::min(w[at(a)][at(b)], w[at(a)][at(x)] + w[at(x)][at(b)]);

    Durations out;
    const int n = m - hubs, goal = hubs - 1;
    for(int i = 0; i < n; ++i)
    {
        out.d.push_back(w[0][at(hubs + i)]);
        out.dbar.push_back(w[at(goal)][at(hubs + i)]);
        out.central.emplace_back();
        for(int j = 0; j < n; ++j)
            out.central.back().push_back(w[at(hubs + i)][at(hubs + j)]);
    }
    return out;
}

Instance buildInstance(const legacy::Options& base, const Options& metric)
{
    if(base.n < 1 || base.t < 1 || base.p < 1)
        throw std::invalid_argument("n, t and p must be positive");
    Layout layout;
    if(metric.coordsFile)
    {
        layout = readLayout(*metric.coordsFile, metric.geometry, metric.hubs);
        if(static_cast<int>(layout.cities.size()) != base.n)
            throw std::runtime_error("the coordinates file " + *metric.coordsFile + " lists " + std::to_string(layout.cities.size()) +
                                     " central cities, but n = " + std::to_string(base.n) + " (-n)");
    }
    else
        layout = randomLayout(metric.geometry, metric.hubs, base.n, metric.seed);
    Durations durations = roundedDurations(layout, metric.geometry, base.adjust);

    Instance instance;
    instance.t = base.t;
    instance.p = base.p;
    instance.d = std::move(durations.d);
    instance.dbar = std::move(durations.dbar);
    instance.central = std::move(durations.central);
    if(metric.randomCosts)
    {
        const auto [lo, hi] = *metric.randomCosts;
        if(lo < 0 || hi < lo)
            throw std::invalid_argument("--random-costs needs 0 <= LO <= HI");
        // A stream of its own, so that costs do not move the points.
        std::mt19937_64 engine(metric.seed ^ 0x9e3779b97f4a7c15ULL);
        const auto range = static_cast<std::uint64_t>(hi - lo) + 1;
        for(int i = 0; i < base.n; ++i)
            instance.c.push_back(lo + static_cast<Cost>(engine() % range));
    }
    else
        instance.c = legacy::generatedCosts(base, 1);
    instance.validate();
    return instance;
}
} // namespace zeno::metric
