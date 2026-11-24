```text
$ zeno --help
usage: zeno [front] [instance options] [solver options]
       zeno check CERTIFICATE
       zeno pddl [instance options] [-O FILE] [--no-front]
       zeno generate [instance options] [-O FILE]

front     Pareto front (cost, makespan) as "cost makespan" lines by
          increasing cost (the default command). Exact for symmetric
          instances. For non-symmetric ones: achieved points (simulated
          plans) and, on stderr, which gaps a lower bound certifies
check     verify a front certificate (doc/certificate-format.md) and print
          the assumptions it relied on
pddl      write the instance as a PDDL problem for pddl/multi-zeno-travel.pddl,
          with its front as comments unless --no-front (default file
          zeno<n>n<t>t<p>pMulti.pddl)
generate  write the instance as a data file for -d (default: standard output)

Instance (same meaning as for the 2016 zenoSolver):
  -n N        central cities (default 3)
  -t N        passengers (default 3)
  -p N        planes (default 2), 1 <= p <= t
  -d FILE     data file: durations then costs (2 lines), or C_I-side
              durations, C_G-side durations, costs (3 lines)
  -C K -D K   generator of costs / durations: 1 log, 2 sqrt, 3 identity (default),
              4 power of two, 5 staircase
  -E K -W K   non-symmetric durations: -E generates the C_I-side durations,
              -W the C_G-side ones (as the 2016 code does)
  -r R        multiply before truncating to integers (default 1)
  -j -k       cost generator scale / translation
  -l -m       duration generator scale / translation
  -x -y       output scale / translation of both generators
  -F          accepted for compatibility (the front is always printed)

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
