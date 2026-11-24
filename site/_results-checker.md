| Set | Certificates | Verdicts | Median | Slowest |
|---|--:|---|--:|---|
| Lean `zeno-check`, test certificates (`lean/test/certificates`, versions 1 and 2) | 37 | 19 accepted, 18 rejected (each as expected) | 24 ms | 2.4 s (`rejected/v2-balanced-missing-point`) |
| Lean `zeno-check`, version 2 certificates of random non-symmetric instances | 152 | 151 accepted, 1 rejected | 23 ms | 2.3 s (`v2-random/e1w2`) |
| Lean `zeno-check`, certificates whose cities all survive the dominance merge | 8 | 8 accepted, 0 rejected | 185 ms | 12.5 s (`many-cities/n40t20p8C2D2r100`) |
| C++ `zeno check`, test certificates | 25 | 13 accepted, 12 rejected (each as expected) | 2.1 ms | 5.1 ms (`accepted/forest-r25`) |
