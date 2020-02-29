inductive aexpr : Type
| const : ℕ → aexpr
| var : ℕ → aexpr
| plus : aexpr → aexpr → aexpr
| times : aexpr → aexpr → aexpr

open aexpr

def sample_aexpr : aexpr :=
plus (times (var 0) (const 7)) (times (const 2) (var 1))

-- BEGIN
def aeval (v : ℕ → ℕ) : aexpr → ℕ
| (const n)    := n
| (var n)      := v n
| (plus e₁ e₂)  := (aeval e₁) + (aeval e₂)
| (times e₁ e₂) := (aeval e₁) * (aeval e₂)

def sample_val : ℕ → ℕ
| 0 := 5
| 1 := 6
| _ := 0

-- Try it out. You should get 47 here.
#eval aeval sample_val sample_aexpr
-- END

-- BEGIN
def simp_const : aexpr → aexpr
| (plus (const n₁) (const n₂))  := const (n₁ + n₂)
| (times (const n₁) (const n₂)) := const (n₁ * n₂)
| e                             := e

def fuse : aexpr → aexpr
| (plus e₁ e₂)  := simp_const (plus (fuse e₁) (fuse e₂))
| (times e₁ e₂) := simp_const (times (fuse e₁) (fuse e₂))
| e := e

#eval aeval sample_val (fuse sample_aexpr)

theorem simp_const_eq (v : ℕ → ℕ) :
  ∀ e : aexpr, aeval v (simp_const e) = aeval v e
| (const n) := rfl
| (var n) := rfl
| (plus e1 e2) := begin
  cases e1, {
    cases e2, reflexivity,
    repeat { dsimp [simp_const], reflexivity }      
  }, 
  repeat {
    dsimp [simp_const], reflexivity
  }
end
| (times e1 e2) := begin
  cases e1, {
    cases e2, reflexivity,
    repeat { dsimp [simp_const], reflexivity }      
  }, 
  repeat {
    dsimp [simp_const], reflexivity
  }
end

theorem fuse_eq (v : ℕ → ℕ) :
  ∀ e : aexpr, aeval v (fuse e) = aeval v e
| (plus e1 e2) := begin
  dsimp [fuse],
  simp [simp_const_eq],
  dsimp [aeval],
  simp [fuse_eq e1, fuse_eq e2],
end
| (times e1 e2) := begin
  dsimp [fuse],
  simp [simp_const_eq],
  dsimp [aeval],
  simp [fuse_eq e1, fuse_eq e2],
end
| (const _) := rfl
| (var _) := rfl
-- END
