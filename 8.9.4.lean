
def fact: nat -> nat
| 0 := 1
| (n+1) := (n+1) * (fact n)

example: fact 5 = 120 := rfl

def c: nat -> nat
| 0 := 1
| 1 := 1
| (n+1) := (c n) * 2*(2*n + 1)/(n+2)

#eval c 1
#eval c 5
example: c 5 = 42 := rfl
#eval c 10

lemma lt_pred (x: nat) (h: 0 < x): (x-1) < x := nat.sub_lt h (nat.lt.base 0)
def fact' := well_founded.fix nat.lt_wf (λ x f, if h : x > 0 then x * (f (x-1) (lt_pred x h) ) else 1)
#eval fact' 8
example: fact' 8 = fact 8 := rfl.

lemma fact'_succ (n: nat): fact' (n+1) = (n+1)*(fact' n) := rfl.
theorem commutes (n: nat): fact n = fact' n := begin
induction n, reflexivity,
case nat.succ: n ih {
  simp [fact, fact'_succ, ih],
}
end
