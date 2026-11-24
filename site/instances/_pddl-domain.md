```lisp
; MultiZenoTravel domain (PDDL 2.1, level 3: durative actions and numeric fluents).
;
; Cities: city0 is the initial city C_I, city1..cityN are the central cities,
; city(N+1) is the goal city C_G. Every person starts in C_I and must reach C_G;
; every plane starts in C_I and must end in C_G.
;
; - fly takes (timeTerre ?from ?to) time units and adds (citythreat ?to) to the
;   total cost when the plane lands. citythreat is 0 for C_I and C_G.
; - A plane carries at most one person: (libre ?a) holds while it is empty.
; - board and debark are instantaneous. Under PDDL 2.1 epsilon-separation a plan
;   with k actions on its critical path ends at M + O(k * epsilon), where M is the
;   sum of the flight durations on that path. ZenoSolver reports M, i.e. the
;   makespan in the limit epsilon -> 0.
;
; See README.md, section "PDDL".

(define (domain multi-zeno-travel)
  (:requirements :typing :durative-actions :fluents)
  (:types city locatable - object
          aircraft person - locatable)

  (:predicates
    (at ?x - locatable ?c - city)
    (in ?p - person ?a - aircraft)
    (libre ?a - aircraft))

  (:functions
    (timeTerre ?from ?to - city)
    (citythreat ?c - city)
    (total-cost))

  (:action board
    :parameters (?p - person ?a - aircraft ?c - city)
    :precondition (and (at ?p ?c) (at ?a ?c) (libre ?a))
    :effect (and (not (at ?p ?c)) (in ?p ?a) (not (libre ?a))))

  (:action debark
    :parameters (?p - person ?a - aircraft ?c - city)
    :precondition (and (in ?p ?a) (at ?a ?c))
    :effect (and (not (in ?p ?a)) (libre ?a) (at ?p ?c)))

  (:durative-action fly
    :parameters (?a - aircraft ?from ?to - city)
    :duration (= ?duration (timeTerre ?from ?to))
    :condition (at start (at ?a ?from))
    :effect (and (at start (not (at ?a ?from)))
                 (at end (at ?a ?to))
                 (at end (increase (total-cost) (citythreat ?to))))))
```
