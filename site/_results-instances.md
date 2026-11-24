| Instance | Arguments | Front | `zeno` | 2016 `zenoSolver` | `zeno-front` | `zeno-check` | Certificate |
|---|---|--:|--:|--:|--:|--:|--:|
| `quick/n5t5p2` | `-n 5 -t 5 -p 2` | 17 | 3.6 ms | 5.2 ms | 40 ms | 22 ms | 4 kB |
| `quick/n6t5p3` | `-n 6 -t 5 -p 3` | 16 | 3.7 ms | 5.2 ms | 40 ms | 22 ms | 3 kB |
| `quick/n10t4p2` | `-n 10 -t 4 -p 2` | 28 | 3.7 ms | 14 ms | 40 ms | 22 ms | 5 kB |
| `quick/lpt-counterexample` | `-n 2 -t 5 -p 2 -d lpt-counterexample.dat` | 6 | 2.1 ms | 2.3 ms | 40 ms | 24 ms | 1 kB |
| `quick/multiples` | `-n 6 -t 6 -p 3 -d multiples.dat` | 16 | 2.1 ms | 20 ms | 40 ms | 22 ms | 4 kB |
| `regimes/r1-n200t3p2` | `-n 200 -t 3 -p 2` | 399 | 3.7 ms | timeout | 410 ms | 34 ms | 68 kB |
| `regimes/r2-n20t6p2` | `-n 20 -t 6 -p 2` | 96 | 3.6 ms | timeout | 40 ms | 27 ms | 29 kB |
| `regimes/r3-n8t26p25` | `-n 8 -t 26 -p 25` | 15 | 3.4 ms | timeout | 50 ms | 29 ms | 13 kB |
| `regimes/r4-n50t30p5` | `-n 50 -t 30 -p 5` | 540 | 8.1 ms | timeout | 700 ms | 214 ms | 877 kB |
| `regimes/r5-n100t60p10` | `-n 100 -t 60 -p 10` | 1090 | 61 ms | timeout | 10.1 s | 2.1 s | 3.9 MB |
| `paper-table1/n3t3p2` | `-n 3 -t 3 -p 2` | 5 | 2.2 ms | 3.2 ms | 40 ms | 22 ms | 1 kB |
| `paper-table1/n4t4p2` | `-n 4 -t 4 -p 2` | 10 | 2.2 ms | 3.2 ms | 40 ms | 22 ms | 2 kB |
| `paper-table1/n5t5p2` | `-n 5 -t 5 -p 2` | 17 | 2.1 ms | 5.7 ms | 40 ms | 22 ms | 4 kB |
| `paper-table1/n6t6p2` | `-n 6 -t 6 -p 2` | 26 | 2.1 ms | 56 ms | 40 ms | 24 ms | 7 kB |
| `paper-table1/n7t7p2` | `-n 7 -t 7 -p 2` | 37 | 3.3 ms | 1.0 s | 40 ms | 22 ms | 12 kB |
| `paper-table1/n8t8p2` | `-n 8 -t 8 -p 2` | 50 | 2.1 ms | 17.8 s | 40 ms | 24 ms | 18 kB |
| `paper-table1/n9t9p2` | `-n 9 -t 9 -p 2` | 65 | 2.1 ms | timeout | 40 ms | 25 ms | 28 kB |
| `paper-table1/n10t10p2` | `-n 10 -t 10 -p 2` | 82 | 2.1 ms | timeout | 40 ms | 25 ms | 41 kB |
| `families/linear` | `-n 10 -t 8 -p 3 -C 3 -D 3` | 46 | 2.2 ms | timeout | 40 ms | 24 ms | 17 kB |
| `families/log` | `-n 10 -t 8 -p 3 -C 1 -D 1 -r 100` | 46 | 3.7 ms | timeout | 50 ms | 28 ms | 19 kB |
| `families/sqrt` | `-n 10 -t 8 -p 3 -C 2 -D 2 -r 100` | 81 | 3.7 ms | timeout | 160 ms | 57 ms | 38 kB |
| `families/pow2` | `-n 10 -t 8 -p 3 -C 4 -D 4` | 46 | 5.0 ms | timeout | 100 ms | 35 ms | 20 kB |
| `families/staircase` | `-n 10 -t 8 -p 3 -C 5 -D 5 -r 10` | 133 | 3.7 ms | timeout | 60 ms | 32 ms | 57 kB |
| `families/log-linear` | `-n 10 -t 8 -p 3 -r 100 -C 3 -D 1` | 46 | 3.6 ms | timeout | 60 ms | 29 ms | 19 kB |
| `families/sqrt-linear` | `-n 10 -t 8 -p 3 -r 100 -C 3 -D 2` | 75 | 3.7 ms | timeout | 100 ms | 42 ms | 35 kB |
| `adversarial/lpt-counterexample` | `-n 2 -t 5 -p 2 -d lpt-counterexample.dat` | 6 | 2.1 ms | 2.3 ms | 40 ms | 22 ms | 1 kB |
| `adversarial/clustered` | `-n 8 -t 9 -p 3 -d clustered.dat` | 66 | 3.6 ms | timeout | 40 ms | 29 ms | 30 kB |
| `adversarial/multiples` | `-n 6 -t 8 -p 3 -d multiples.dat` | 26 | 3.6 ms | 571 ms | 40 ms | 24 ms | 10 kB |
| `adversarial/near-equal` | `-n 10 -t 9 -p 4 -d near-equal.dat` | 37 | 3.6 ms | timeout | 100 ms | 25 ms | 18 kB |
| `adversarial/three-partition-m4` | `-n 12 -t 8 -p 4 -d three-partition-m4.dat` | 48 | 3.6 ms | timeout | 40 ms | 25 ms | 19 kB |
| `scaling-n/n5` | `-n 5 -t 6 -p 3` | 13 | 2.1 ms | 8.3 ms | 40 ms | 23 ms | 3 kB |
| `scaling-n/n10` | `-n 10 -t 6 -p 3` | 28 | 2.2 ms | 696 ms | 40 ms | 24 ms | 8 kB |
| `scaling-n/n20` | `-n 20 -t 6 -p 3` | 58 | 3.3 ms | timeout | 40 ms | 27 ms | 16 kB |
| `scaling-n/n40` | `-n 40 -t 6 -p 3` | 118 | 3.6 ms | timeout | 50 ms | 29 ms | 34 kB |
| `scaling-n/n80` | `-n 80 -t 6 -p 3` | 238 | 3.6 ms | timeout | 100 ms | 31 ms | 71 kB |
| `scaling-n/n160` | `-n 160 -t 6 -p 3` | 478 | 3.7 ms | timeout | 380 ms | 56 ms | 153 kB |
| `scaling-t/t4` | `-n 8 -t 4 -p 3` | 15 | 2.1 ms | 3.7 ms | 40 ms | 22 ms | 3 kB |
| `scaling-t/t6` | `-n 8 -t 6 -p 3` | 22 | 2.1 ms | 143 ms | 40 ms | 24 ms | 6 kB |
| `scaling-t/t8` | `-n 8 -t 8 -p 3` | 36 | 2.1 ms | 8.1 s | 40 ms | 24 ms | 13 kB |
| `scaling-t/t10` | `-n 8 -t 10 -p 3` | 43 | 3.6 ms | timeout | 40 ms | 28 ms | 19 kB |
| `scaling-t/t12` | `-n 8 -t 12 -p 3` | 50 | 3.6 ms | timeout | 40 ms | 29 ms | 27 kB |
| `scaling-t/t16` | `-n 8 -t 16 -p 3` | 71 | 3.6 ms | timeout | 50 ms | 32 ms | 53 kB |
| `scaling-t/t20` | `-n 8 -t 20 -p 3` | 92 | 3.6 ms | timeout | 50 ms | 34 ms | 89 kB |
| `scaling-t/t30` | `-n 8 -t 30 -p 3` | 134 | 3.6 ms | timeout | 90 ms | 54 ms | 201 kB |
| `scaling-t/t40` | `-n 8 -t 40 -p 3` | 183 | 3.9 ms | timeout | 150 ms | 95 ms | 375 kB |
| `scaling-p/p1` | `-n 8 -t 13 -p 1` | 176 | 3.6 ms | timeout | 50 ms | 33 ms | 117 kB |
| `scaling-p/p2` | `-n 8 -t 13 -p 2` | 85 | 3.4 ms | timeout | 50 ms | 27 ms | 53 kB |
| `scaling-p/p3` | `-n 8 -t 13 -p 3` | 57 | 3.5 ms | timeout | 40 ms | 27 ms | 34 kB |
| `scaling-p/p4` | `-n 8 -t 13 -p 4` | 43 | 3.6 ms | timeout | 40 ms | 25 ms | 25 kB |
| `scaling-p/p5` | `-n 8 -t 13 -p 5` | 36 | 3.7 ms | timeout | 40 ms | 25 ms | 20 kB |
| `scaling-p/p6` | `-n 8 -t 13 -p 6` | 29 | 2.2 ms | timeout | 40 ms | 26 ms | 16 kB |
| `scaling-p/p7` | `-n 8 -t 13 -p 7` | 22 | 3.3 ms | timeout | 40 ms | 24 ms | 11 kB |
| `scaling-p/p8` | `-n 8 -t 13 -p 8` | 22 | 3.7 ms | timeout | 40 ms | 24 ms | 11 kB |
| `scaling-p/p9` | `-n 8 -t 13 -p 9` | 15 | 3.4 ms | timeout | 40 ms | 25 ms | 7 kB |
| `scaling-p/p10` | `-n 8 -t 13 -p 10` | 15 | 2.2 ms | 14.5 s | 50 ms | 24 ms | 7 kB |
| `scaling-p/p11` | `-n 8 -t 13 -p 11` | 15 | 2.1 ms | 2.7 s | 40 ms | 24 ms | 7 kB |
| `scaling-p/p12` | `-n 8 -t 13 -p 12` | 15 | 2.1 ms | 354 ms | 40 ms | 22 ms | 7 kB |
| `scaling-D/r1` | `-n 10 -t 8 -p 3 -C 2 -D 2 -r 1` | 6 | 2.1 ms | timeout | 40 ms | 26 ms | 2 kB |
| `scaling-D/r10` | `-n 10 -t 8 -p 3 -C 2 -D 2 -r 10` | 73 | 3.6 ms | timeout | 50 ms | 33 ms | 30 kB |
| `scaling-D/r100` | `-n 10 -t 8 -p 3 -C 2 -D 2 -r 100` | 81 | 3.7 ms | timeout | 150 ms | 61 ms | 38 kB |
| `scaling-D/r1000` | `-n 10 -t 8 -p 3 -C 2 -D 2 -r 1000` | 82 | 5.1 ms | timeout | 340 ms | 113 ms | 42 kB |
| `scaling-D/r10000` | `-n 10 -t 8 -p 3 -C 2 -D 2 -r 10000` | 82 | 9.4 ms | timeout | 1.8 s | 610 ms | 47 kB |
| `scaling-distinct/k2` | `-n 24 -t 8 -p 3 -d distinct-2.dat` | 10 | 2.2 ms | timeout | 40 ms | 24 ms | 4 kB |
| `scaling-distinct/k4` | `-n 24 -t 8 -p 3 -d distinct-4.dat` | 34 | 3.7 ms | timeout | 50 ms | 26 ms | 14 kB |
| `scaling-distinct/k8` | `-n 24 -t 8 -p 3 -d distinct-8.dat` | 82 | 3.6 ms | timeout | 50 ms | 27 ms | 35 kB |
| `scaling-distinct/k24` | `-n 24 -t 8 -p 3 -d distinct-24.dat` | 274 | 3.7 ms | timeout | 240 ms | 39 ms | 118 kB |
