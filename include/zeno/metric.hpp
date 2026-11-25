#pragma once

#include <zeno/instance.hpp>
#include <zeno/legacy_input.hpp>

#include <cstdint>
#include <optional>
#include <string>
#include <utility>
#include <vector>

/// Metric instances: the cities are points, and every flight lasts the
/// distance between its ends (zeno --metric). Their central-flight tables
/// satisfy the triangle inequality (AΔ) exactly, after rounding, so under (S)
/// the front is exact by Theorems 4.4 and 4.5 of
/// doc/theory/exact-front.md, although central flights are fast and (A1) fails.
namespace zeno::metric
{
enum class Geometry : std::uint8_t
{
    Plane,  ///< Euclidean distances
    Sphere, ///< great-circle distances on a sphere of radius kEarthRadius
};

enum class Hubs : std::uint8_t
{
    Same,  ///< C_I and C_G are one point, so d = dbar: (S) holds exactly
    Apart, ///< two points: the instance is non-symmetric
};

/// A location: (x, y) in the plane, or (latitude, longitude) in degrees.
struct Point
{
    double x = 0, y = 0;
};

/// Mean radius of the Earth, in km: sphere distances are in km.
inline constexpr double kEarthRadius = 6371.0;
/// Random plane points are drawn uniformly in [0, kSquareSide]^2.
inline constexpr double kSquareSide = 100.0;

struct Options
{
    Geometry geometry = Geometry::Plane;
    Hubs hubs = Hubs::Same;
    std::uint64_t seed = 1;
    std::optional<std::string> coordsFile;            ///< read the points instead of drawing them
    std::optional<std::pair<Cost, Cost>> randomCosts; ///< uniform integer costs in [lo, hi]; else -C
};

/// The points of an instance: hubs is {C_I} under Hubs::Same (it is also
/// C_G), {C_I, C_G} under Hubs::Apart.
struct Layout
{
    std::vector<Point> hubs;
    std::vector<Point> cities;
};

/// Euclidean distance, or the great-circle distance (haversine formula).
[[nodiscard]] double distance(Geometry geometry, const Point& a, const Point& b);

/// Random points: C_I, then the n central cities, then C_G under Hubs::Apart
/// (so the same seed gives the same cities for both). Uniform in the square
/// [0, kSquareSide]^2, or uniform on the sphere. The generator is a
/// std::mt19937_64 seeded with `seed`, read without the standard
/// distributions, so a seed gives the same points on every platform.
[[nodiscard]] Layout randomLayout(Geometry geometry, Hubs hubs, int n, std::uint64_t seed);

/// Reads a coordinates file: one point per line, "x,y" (plane) or "lat,lon"
/// in degrees (sphere), separated by commas or spaces, optionally after a
/// label ("CDG,49.0097,2.5479"). Blank lines and lines starting with '#' are
/// skipped. The first point is C_I (and C_G under Hubs::Same), the second C_G
/// under Hubs::Apart, the others are the central cities. Throws
/// std::runtime_error on a malformed line.
[[nodiscard]] Layout readLayout(const std::string& path, Geometry geometry, Hubs hubs);

/// Integer flight durations of a layout.
struct Durations
{
    std::vector<Time> d, dbar; ///< hub legs (d = dbar under Hubs::Same)
    FlightTable central;       ///< central flights
};

/// Every distance is multiplied by `scale` and rounded to the nearest integer.
/// Rounding can break the triangle inequality, so every duration is then
/// replaced by the shortest path between its ends over the flights (every
/// pair of locations except C_I - C_G). The result satisfies (AΔ) exactly, and
/// no duration exceeds its rounded distance. Throws std::invalid_argument
/// unless scale > 0 and the durations stay below 2^31.
[[nodiscard]] Durations roundedDurations(const Layout& layout, Geometry geometry, double scale);

/// The instance of `zeno --metric`: n, t and p from `base`, durations from the
/// points (randomLayout from the seed, or readLayout), scaled by base.adjust
/// (-r). Costs are drawn uniformly from randomCosts, or else given by the cost
/// generator of `base` (-C -j -k -x -y), truncated as in 2016 but not scaled
/// by -r. Throws std::invalid_argument or std::runtime_error.
[[nodiscard]] Instance buildInstance(const legacy::Options& base, const Options& metric);
} // namespace zeno::metric
