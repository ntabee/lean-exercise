namespace hidden

-- BEGIN
inductive nat : Type
| zero : nat
| succ : nat → nat
-- END

@[pattern]
def Z := nat.zero
@[pattern]
def S := nat.succ

def K₁ := S Z
def K₂ := S K₁
def K₃ := S K₂
def K₄ := S K₃
def K₅ := S K₄

def pred: nat -> nat
| Z := Z
| (S n) := n
.
theorem pr₀ : pred Z = Z := rfl.
theorem pr₁ : pred K₁ = Z := rfl.
theorem pr₂ : pred K₂ = K₁ := rfl.

theorem pred_succ_zero (n: nat): pred (S n) = n := rfl.

def sub: nat -> nat -> nat
| n Z := n
| n (S m) := pred (sub n m)
.
#reduce sub Z K₂
#reduce sub K₅ K₂

example: sub Z K₅ = Z := rfl.
theorem sub_n_0: ∀(n: nat), sub n Z = n
| Z := rfl
| (S n) := rfl

theorem sub_0_m: ∀ (m:nat), sub Z m = Z
| Z := rfl
| (S m) := by rw[sub, sub_0_m]; reflexivity.

lemma sub_succ (n m: nat): sub (S n) (S m) = sub n m := begin
induction m,
case nat.zero: {
  reflexivity
},
case nat.succ: m ih {
  have: sub (S n) (S (S m)) = pred (sub (S n) (S m)), from rfl,
  have: sub (S n) (S (S m)) = pred (sub n m), by rw[this, ih],
  have: pred (sub n m) = sub n (S m), by reflexivity,
  assumption
}
end

theorem sub_n_n: ∀(n: nat), sub n n = Z
| Z := rfl
| (S n) := by rw[sub_succ, sub_n_n]
.

def add: nat -> nat -> nat
| m Z := m
| m (S n) := S (add m n)
.

lemma add_n_succ (m n: nat): add m (S n) = S (add m n) := rfl.
lemma add_m_succ (m: nat): ∀ (n: nat), add (S m) n = S (add m n)
| Z := rfl
| (S n) := begin
  simp [add_n_succ],
  rw add_m_succ,
end

lemma add_m_0 (m: nat): add m Z = m := rfl. 
lemma add_0_n: ∀ (n: nat), add Z n = n
| Z := rfl
| (S n) := by simp [add_n_succ, add_0_n n]
.

theorem add_assoc (a b: nat): ∀(c: nat), add (add a b) c = add a (add b c)
| Z := rfl
| (S c) := by simp[add_n_succ, add_assoc c]
.

theorem add_comm (m: nat): ∀(n: nat), add m n = add n m
| Z := by simp[add_m_0, add_0_n]
| (S n) := by simp[add_n_succ, add_m_succ, add_comm n]
.

#reduce add K₁ K₂

def mul: nat -> nat -> nat
| _ Z := Z
| m (S n) := add m (mul m n)
.
#reduce mul Z K₂
#reduce mul K₂ Z
#reduce mul K₁ K₂
#reduce mul K₂ K₂
#reduce mul K₅ K₂

lemma mul_succ_n (m n: nat): mul m (S n) = add m (mul m n) := rfl.
lemma mul_succ_m (m: nat): ∀ (n: nat), mul (S m) n = add (mul m n) n
| Z := rfl
| (S n) := by simp[mul_succ_n, mul_succ_m n, add_n_succ, add_m_succ, add_assoc]
.

theorem mul_m_0 (m: nat): mul m Z = Z := rfl.
theorem mul_0_n: ∀ (n: nat), mul Z n = Z
| Z := rfl
| (S n) := by simp[mul_succ_n, mul_0_n n]; reflexivity
.

theorem mul_m_1 (m: nat): mul m K₁ = m := rfl
theorem mul_1_n (n: nat): mul K₁ n = n := begin
  rw [K₁],
  simp [mul_succ_m, mul_0_n, add_0_n],
end

theorem mul_comm (m: nat): ∀(n: nat), mul m n = mul n m
| Z := by simp[mul_m_0, mul_0_n]
| (S n) := by simp [mul_succ_n, mul_succ_m, mul_comm n, add_comm]
.

theorem mul_dist (b c: nat): ∀ (a: nat), mul a (add b c) = add (mul a b) (mul a c) 
| Z := by simp [mul_0_n]; reflexivity
| (S a) := begin
  simp[mul_succ_m, add_assoc, mul_dist a],
  rw [<-add_assoc (mul a c), add_comm (mul a c), <-add_assoc b],
end

theorem mul_assoc (a b: nat): ∀(c: nat), mul (mul a b) c = mul a (mul b c)
| Z := rfl
| (S c) := by simp[mul_succ_n, mul_assoc c, mul_dist]
.

theorem succ_nonzero (n: nat): S n ≠ Z := by trivial.
def nonzero := {n: nat // n ≠ Z}
def nonzero.mk (n: nat) (h: n ≠ Z): nonzero := ⟨n,h⟩
def nz := nonzero.mk.
#check nz K₂ (by apply succ_nonzero)

def pow: nonzero -> nat -> nat
| _ Z := K₁
| m (S n) := mul m.val (pow m n)

def nzK₁ := nz (S Z) (by apply succ_nonzero)
def nzK₂ := nz (S K₁) (by apply succ_nonzero)
def nzK₃ := nz (S K₂) (by apply succ_nonzero)
def nzK₄ := nz (S K₃) (by apply succ_nonzero)
def nzK₅ := nz (S K₄) (by apply succ_nonzero)

#reduce pow nzK₂ Z
#reduce pow nzK₁ K₂
#reduce pow nzK₂ K₂
#reduce pow nzK₃ K₂

theorem pow_by_0 (m: nonzero): pow m Z = K₁ := rfl.
theorem pow_by_1 (m: nonzero): pow m K₁ = m.val := rfl.
theorem pow_by_succ (m: nonzero) (n: nat): pow m (S n) = mul m.val (pow m n) := rfl.
theorem pow_of_1: ∀ (n: nat), pow nzK₁ n = K₁
| Z := rfl
| (S n) := begin
  have o: nzK₁.val = K₁, from rfl,
  have: pow nzK₁ (S n) = mul nzK₁.val (pow nzK₁ n), by rw [pow_by_succ],
  simp [o, mul_1_n] at this,
  simp [pow_of_1 n] at this, assumption
end

theorem pow_by_add (m: nonzero) (a: nat): ∀(b: nat), pow m (add a b) = mul (pow m a) (pow m b)
| Z := rfl
| (S b) := by simp [add_n_succ, pow_by_succ, pow_by_add b, mul_comm, mul_assoc].

end hidden