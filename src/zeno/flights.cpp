#include <zeno/flights.hpp>

#include <algorithm>

namespace zeno
{
FlightAssumptions checkFlights(const Instance& in)
{
    const int n = in.n(), goal = n + 1;
    const auto at = [](int v) { return static_cast<std::size_t>(v); };
    FlightAssumptions out;
    out.a1 = in.symmetric();
    out.a1ns = true;
    for(int i = 0; i < n; ++i)
        for(int j = i + 1; j < n; ++j)
        {
            const Time dij = in.centralFlight(i, j);
            const Time west = in.d[at(i)] + in.d[at(j)], east = in.dbar[at(i)] + in.dbar[at(j)];
            out.a1 = out.a1 && dij >= west;
            out.a1ns = out.a1ns && dij >= std::min(west, east);
        }

    // Locations 0 = C_I, 1..n the central cities, n + 1 = C_G. Every pair but
    // C_I - C_G has a flight, so the triangles are the triples without both hubs.
    const auto dur = [&](int a, int b) -> Time {
        if(a > b)
            std::swap(a, b);
        if(a == 0)
            return in.d[at(b - 1)];
        if(b == goal)
            return in.dbar[at(a - 1)];
        return in.centralFlight(a - 1, b - 1);
    };
    const auto hubs = [&](int a, int b) { return (a == 0 && b == goal) || (a == goal && b == 0); };
    out.triangle = true;
    for(int a = 0; a <= goal && out.triangle; ++a)
        for(int b = a + 1; b <= goal && out.triangle; ++b)
        {
            if(hubs(a, b))
                continue;
            const Time ab = dur(a, b);
            for(int x = 0; x <= goal; ++x)
                if(x != a && x != b && !hubs(a, x) && !hubs(x, b) && ab > dur(a, x) + dur(x, b))
                {
                    out.triangle = false;
                    break;
                }
        }
    return out;
}
} // namespace zeno
