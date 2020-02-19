namespace hidden

inductive empty : Type

#check empty.cases_on

inductive unit : Type
| star : unit

#check unit.star
#check unit.cases_on

def k42: unit -> ℕ := λ _, 42

inductive bool : Type
| ff : bool
| tt : bool

#check bool.ff
#check bool.tt
#check bool.cases_on

def band: bool -> bool -> bool := λ (x y), bool.cases_on x bool.ff y 
#reduce band bool.tt bool.tt
#reduce band bool.tt bool.ff
#reduce band bool.ff bool.tt
#reduce band bool.ff bool.ff

def bor: bool -> bool -> bool := λ (x y), bool.cases_on x y bool.tt
#reduce bor bool.tt bool.tt
#reduce bor bool.tt bool.ff
#reduce bor bool.ff bool.tt
#reduce bor bool.ff bool.ff

def bnot: bool -> bool := fun x, bool.cases_on x bool.tt bool.ff
#reduce bnot bool.tt
#reduce bnot bool.ff

end hidden