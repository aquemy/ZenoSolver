# Airports: from Atlanta to Beijing

A MultiZenoTravel instance built from real data. The initial city C_I is Hartsfield Jackson Atlanta
International Airport (ATL). The goal city C_G is Beijing Capital International Airport (PEK). The
11 central cities are large airports through which a passenger can travel from ATL to PEK: DXB, MUC,
FRA, AMS, SFO, SEA, ORD, LAS, DFW, DEN and IAH.

The instance is non-symmetric because ATL and PEK are two different points. With direct flights
between the central airports it satisfies (AΔ) but not (A1-NS). Its exact Pareto front is open: see
the open problems at the end of the [paper](https://quemy.info/ZenoSolver/paper/index.html#sec-open).

| File | Content |
|---|---|
| `atl-pek.coords` | IATA code, latitude and longitude of the 13 airports, with C_I first and C_G second (the `--coords` format). |
| `atl-pek-direct.dat` | The 3-line data file: durations from ATL, durations to PEK, landing costs. It is followed by the `central` table of flight durations between the central airports (direct flights). |
| `atl-pek.dat` | The first three lines of `atl-pek-direct.dat`. It is the hub-and-spoke variant: with no `central` table, `zeno` gives every flight between central cities a duration longer than any detour through ATL or PEK, so (A1-NS) holds. |

Durations are great-circle distances on a sphere of radius 6,371 km, in units of 100 km, rounded to
integers. The landing cost of airport i is made up: it is c_i = 2 / (d(ATL, i) + d(i, PEK)), with
the distances in km, multiplied by 10^7 and rounded to an integer.

## Source and licence

The coordinates come from [`airports.dat`](https://raw.githubusercontent.com/jpatokal/openflights/master/data/airports.dat)
of [OpenFlights](https://openflights.org/data.php). It is made available under the
[Open Database License (ODbL) v1.0](https://opendatacommons.org/licenses/odbl/1-0/). Only 13 rows
are kept, with their name and place as comments, in `atl-pek.coords`. The two data files are derived
from them.

## Regenerating the files

From this directory, with a built `zeno` on the `PATH`:

```sh
# durations, and the table of direct flights, from the coordinates (-r 0.01: units of 100 km)
zeno generate --metric sphere --hubs apart --coords atl-pek.coords -n 11 -r 0.01 -O atl-pek-direct.dat

# replace the third line (zeno writes the costs 1 to 11) by c_i = round(2e7 / (d(ATL, i) + d(i, PEK)))
costs=$(python3 - atl-pek.coords <<'EOF'
import math, sys
rows = [l.split(",") for l in open(sys.argv[1]) if l.strip() and not l.startswith("#")]
pts = [(math.radians(float(lat)), math.radians(float(lon))) for _, lat, lon in rows]
def km(p, q):
    h = (math.sin((q[0] - p[0]) / 2) ** 2
         + math.cos(p[0]) * math.cos(q[0]) * math.sin((q[1] - p[1]) / 2) ** 2)
    return 2 * 6371 * math.asin(math.sqrt(h))
print(*(round(2e7 / (km(pts[0], x) + km(x, pts[1]))) for x in pts[2:]))
EOF
)
awk -v c="$costs" 'NR == 3 { $0 = c } { print }' atl-pek-direct.dat > tmp.dat && mv tmp.dat atl-pek-direct.dat

# the hub-and-spoke variant: without the table of direct flights
head -n 3 atl-pek-direct.dat > atl-pek.dat
```

To solve them, for example with t = 6 passengers and p = 3 planes:

```sh
zeno -d atl-pek.dat -n 11 -t 6 -p 3 --plans --certificate atl-pek-p3.cert
zeno check atl-pek-p3.cert
zeno -d atl-pek-direct.dat -n 11 -t 6 -p 3
```
