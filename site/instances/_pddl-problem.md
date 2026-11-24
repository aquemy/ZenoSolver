```text
$ zeno pddl -n 2 -t 2 -p 1 -O example.pddl
```

```lisp
(define (problem MULTIZENO-A)
  (:domain  multi-zeno-travel)
  (:objects plane1 - aircraft
            person1 person2 - person
            city0 city1 city2 city3 - city)
  (:init (= (total-cost) 0)
         (= (citythreat city0) 0)
         (= (citythreat city1) 1)
         (= (citythreat city2) 2)
         (= (citythreat city3) 0)
         
; city1
         (= (timeTerre city0 city1) 2)
         (= (timeTerre city1 city0) 2)
         (= (timeTerre city3 city1) 2)
         (= (timeTerre city1 city3) 2)
         (= (timeTerre city1 city2) 103)
         
; city2
         (= (timeTerre city0 city2) 1)
         (= (timeTerre city2 city0) 1)
         (= (timeTerre city3 city2) 1)
         (= (timeTerre city2 city3) 1)
         (= (timeTerre city2 city1) 103)
         
; plane init
         (at plane1 city0)
         (libre plane1)
         
; person init
         (at person1 city0)
         (at person2 city0)
         
)
(:goal (and 
         (at person1 city3)
         (at person2 city3)
         (at plane1 city3)
         ))
  (:metric (and (minimize (total-time)) (minimize (total-cost)))))

; Durations : 
; 2 1 
; Costs : 
; 1 2 
; Pareto points : Makespan - Cost
; 6 6
; 8 5
; 10 4
; 12 3
```
