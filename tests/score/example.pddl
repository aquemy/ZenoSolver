(define (problem MULTIZENO-A)
  (:domain  multi-zeno-travel)
  (:objects plane1 plane2 - aircraft
            person1 person2 person3 - person
            city0 city1 city2 city3 city4 - city)
  (:init (= (total-cost) 0)
         (= (citythreat city0) 0)
         (= (citythreat city1) 9)
         (= (citythreat city2) 6)
         (= (citythreat city3) 1)
         (= (citythreat city4) 0)
         
; city1
         (= (timeTerre city0 city1) 2)
         (= (timeTerre city1 city0) 2)
         (= (timeTerre city4 city1) 2)
         (= (timeTerre city1 city4) 2)
         (= (timeTerre city1 city2) 105)
         (= (timeTerre city1 city3) 107)
         
; city2
         (= (timeTerre city0 city2) 3)
         (= (timeTerre city2 city0) 3)
         (= (timeTerre city4 city2) 3)
         (= (timeTerre city2 city4) 3)
         (= (timeTerre city2 city1) 105)
         (= (timeTerre city2 city3) 108)
         
; city3
         (= (timeTerre city0 city3) 5)
         (= (timeTerre city3 city0) 5)
         (= (timeTerre city4 city3) 5)
         (= (timeTerre city3 city4) 5)
         (= (timeTerre city3 city1) 107)
         (= (timeTerre city3 city2) 108)
         
; plane init
         (at plane1 city0)
         (at plane2 city0)
         (libre plane1)
         (libre plane2)
         
; person init
         (at person1 city0)
         (at person2 city0)
         (at person3 city0)
         
)
(:goal (and 
         (at person1 city4)
         (at person2 city4)
         (at person3 city4)
         (at plane1 city4)
         (at plane2 city4)
         ))
  (:metric (and (minimize (total-time)) (minimize (total-cost)))))

; Durations : 
; 2 3 5 
; Costs : 
; 9 6 1 
; Pareto points : Makespan - Cost
; 8 36
; 10 30
; 12 24
; 14 20
; 16 14
; 20 4
