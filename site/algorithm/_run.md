```sh
$ zeno -n 3 -t 3 -p 2 -d site/problem/example.dat --plans --stats
4 20
14 16
20 14
24 12
30 10
36 8

# cost 4, makespan 20
plane 1: CI->c3[0,5]p1 c3->CI[5,10] CI->c3[10,15]p2 c3->CG[15,20]p2
plane 2: CI->c3[0,5]p3 c3->CG[5,10]p3 CG->c3[10,15] c3->CG[15,20]p1

# cost 14, makespan 16
plane 1: CI->c2[0,3]p1 c2->CI[3,6] CI->c3[6,11]p2 c3->CG[11,16]p2
plane 2: CI->c3[0,5]p3 c3->CG[5,10]p3 CG->c2[10,13] c2->CG[13,16]p1

# cost 20, makespan 14
plane 1: CI->c1[0,2]p1 c1->CI[2,4] CI->c3[4,9]p2 c3->CG[9,14]p2
plane 2: CI->c3[0,5]p3 c3->CG[5,10]p3 CG->c1[10,12] c1->CG[12,14]p1

# cost 24, makespan 12
plane 1: CI->c2[0,3]p1 c2->CI[3,6] CI->c2[6,9]p2 c2->CG[9,12]p2
plane 2: CI->c2[0,3]p3 c2->CG[3,6]p3 CG->c2[6,9] c2->CG[9,12]p1

# cost 30, makespan 10
plane 1: CI->c1[0,2]p1 c1->CI[2,4] CI->c2[4,7]p2 c2->CG[7,10]p2
plane 2: CI->c2[0,3]p3 c2->CG[3,6]p3 CG->c1[6,8] c1->CG[8,10]p1

# cost 36, makespan 8
plane 1: CI->c1[0,2]p1 c1->CI[2,4] CI->c1[4,6]p2 c1->CG[6,8]p2
plane 2: CI->c1[0,2]p3 c1->CG[2,4]p3 CG->c1[4,6] c1->CG[6,8]p1
levels 4..10 (x1, 7 levels), cities 3, max tree 2
settled: bracket 7, pairs 0, chains 0, monotone 0, exact 0
work: 17 states, 266 relaxations
seconds: table 1.791e-06, bracket 5.7167e-05, chains 0, exact 0, plans 3.7542e-05
```
