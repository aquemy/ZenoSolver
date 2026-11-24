| Solver | Finished | Median | Slowest | Conditions |
|---|---|---|---|---|
| `zeno` (C++, all cores) | 66 of 66 | 3.6 ms | 61 ms (`regimes/r5-n100t60p10`) | 30 s timeout, median of 3 runs |
| 2016 `zenoSolver` | 21 of 66 | 20 ms (finished only) | timeout on 45 | 30 s timeout, median of 3 runs |
| 2016 `zenoSolver_naive` | 21 of 66 | 20 ms (finished only) | timeout on 45 | 30 s timeout, median of 3 runs |
| 2016 `zenoSolver_noDuplicate` | 21 of 66 | 38 ms (finished only) | timeout on 45 | 30 s timeout, median of 3 runs |
| Lean `zeno-front` (verified solver) | 66 of 66 | 40 ms | 10.1 s (`regimes/r5-n100t60p10`) | 60 s timeout, one run; front equal to `zeno front` on 66 of 66 |
| Lean `zeno-check` on `zeno`'s certificates | 66 of 66 accepted | 26 ms | 2.1 s (`regimes/r5-n100t60p10`) | 4.9 s in total |
