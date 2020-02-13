open classical

variable p: Prop 
#check em p 

theorem dne {p: Prop} (h: ¬ ¬ p) : p :=
  (em p).elim 
    (assume hp: p, hp)
    (assume hnp: ¬ p, absurd hnp h)
  
#check by_cases
