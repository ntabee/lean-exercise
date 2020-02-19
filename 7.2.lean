#check option.cases_on

def comp {α β γ : Type*} (f: α -> option β) (g: β -> option γ) (x: α): option γ :=
  option.cases_on (f x) option.none (λ y, g y)

#print comp
#reduce comp (λ x, some (x*x)) (λ x, some (x+1)) 10
example: comp (λ x, some (x*x)) (λ x, some (x+1)) 10 = some 101 := by rsimp

#reduce comp (λ x, none) (λ x, some (x+1)) 10
example: comp (λ x, none) (λ x, some (x+1)) 10 = none := by rsimp

def pipe {α β : Type*} (x: option α) (f: α -> option β): option β :=
  option.cases_on x option.none (λ y, f y)

#print pipe
infixl `>>`:50 := pipe

#reduce (some 10) >> (λ x, some $ x*x) >> (λ x, some $ x+1).
#reduce (some 10) >> (λ x, none) >> (λ x, some $ x+1).
#reduce none >> (λ x, some $ x*x) >> (λ x, some $x+1).

def ibool: inhabited bool := inhabited.mk tt
def inat: inhabited ℕ := inhabited.mk 0

theorem ipair: ∀α β : Type*, inhabited α × inhabited β -> inhabited (α × β) := begin
intros α β h,
cases h with a b,
from inhabited.mk (a.default, b.default)
end

theorem ifun: ∀ α β : Type*, (α -> inhabited β) -> inhabited (α -> β) := begin
intros α β f,
from inhabited.mk (λ x: α, (f x).default)
end

