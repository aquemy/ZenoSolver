```text
$ zeno --help
usage: zeno [front] [instance options] [solver options]
       zeno check CERTIFICATE
       zeno pddl [instance options] [-O FILE] [--no-front]
       zeno generate [instance options] [-O FILE]

front     Pareto front (cost, makespan) as "cost makespan" lines by
          increasing cost (the default command). Exact for symmetric
          instances whose central flights satisfy (A1) or the triangle
          inequality (AΔ) (Theorem 4.10, Corollary 4.12; in Lean,
          solveFront_isParetoFront_ATri): the default table satisfies (A1),
          --metric tables (AΔ). With a central-flight table,
          stderr says which holds, or warns that the front may not be exact
          (Example 4.13). For non-symmetric instances: achieved points
          (simulated plans) and, on stderr, which gaps a lower bound
          certifies
check     verify a front certificate (doc/certificate-format.md) and print
          the assumptions it relied on (S; A1|AD: central flights satisfy
          (A1) or (AΔ), as for the Lean checker, Cert.check_sound_A1 and
          Cert.check_sound_ATri; A1-NS)
pddl      write the instance as a PDDL problem for pddl/multi-zeno-travel.pddl,
          with its front as comments unless --no-front (default file
          zeno<n>n<t>t<p>pMulti.pddl)
generate  write the instance as a data file for -d (default: standard output)

Instance (the options of the 2016 zenoSolver, without its swap; see below):
  -n N        central cities (default 3)
  -t N        passengers (default 3)
  -p N        planes (default 2), 1 <= p <= t
  -d FILE     data file: durations then costs (2 lines), or C_I-side
              durations, C_G-side durations, costs (3 lines); then, optionally,
              a line "central" and n lines of n central-flight durations
              (symmetric, zero diagonal). Without it, central flights last
              max(d_i, dbar_i) + max(d_j, dbar_j) + 100, which satisfies (A1)
  -C K -D K   generator of costs / durations: 1 log, 2 sqrt, 3 identity (default),
              4 power of two, 5 staircase
  -E K -W K   non-symmetric durations: -E generates the C_I-side durations,
              -W the C_G-side ones
  -r R        multiply before truncating to integers (default 1)
  -j -k       cost generator scale / translation
  -l -m       duration generator scale / translation
  -x -y       output scale / translation of both generators
  -F          accepted for compatibility (the front is always printed)

Metric instances (every flight lasts the distance between its ends):
  --metric plane|sphere  random points, uniform in the square [0, 100]^2
                         (plane), or uniform on a sphere of radius 6371 km with
                         great-circle distances (sphere)
  --seed S               seed of the points and of --random-costs (default 1)
  --hubs same|apart      same (default): C_I and C_G are one point, so the
                         durations are symmetric (S); apart: two points, and the
                         instance is non-symmetric
  --coords FILE          the points instead of random ones: one "x,y" (plane)
                         or "lat,lon" in degrees (sphere) per line, optionally
                         after a label; the hub first (C_I, then C_G with
                         --hubs apart), then the n central cities
  --random-costs LO,HI   uniform random integer costs (default: -C -j -k -x -y,
                         not scaled by -r)
  -r R                   distances are multiplied by R (default 1) and
                         rounded, then every duration becomes its shortest
                         path over the flights, so the table satisfies the
                         triangle inequality (AΔ) exactly. With --hubs same
                         the front is exact (Theorem 4.10, Corollary 4.12)
  -d -D -E -W -l -m do not apply. `zeno generate` writes the table as the
  "central" block of the data file.

Each option means what it says, and data files are read as written. The 2016
solvers swapped durations and costs whenever the first duration exceeded the
second, which their generator always did: a 2016 or paper instance
"-C a -D b" is "-C b -D a" here, and "-C c -E a -W b" is "-C a -E c -W b".
Two exceptions. When truncation ties the first two durations, the 2016 code
did not swap, so its flags mean the same here (-n 10 -D 1 -r 1 starts with
d = (2, 2, ...); `zeno generate` on both forms shows which case applies).
And zeno scales both duration sides of -E/-W with -l/-m, so the -E/-W rule is
exact only if the 2016 instance had the same -j/-k as -l/-m (the defaults
do); otherwise write it as a data file.

Solver (front):
  --threads N          worker threads (default: all cores)
  --levels MODE        auto (default), sweep (bracket every level) or search
                       (bisect for the breakpoints; for wide level ranges)
  --plans              after the front, print a plan for every point (checked
                       by simulation): one line per plane, legs as
                       from->to[depart,arrive] with the passenger carried (pK)
  --certificate FILE   write a certificate of the front to FILE
  --stats              print solver statistics on stderr
  -h, --help           this help
```
