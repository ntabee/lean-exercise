namespace hidden

-- BEGIN
inductive nat : Type
| zero : nat
| succ : nat → nat
-- END

def Z := nat.zero
def S := nat.succ

def K₁ := S Z
def K₂ := S K₁
def K₃ := S K₂
def K₄ := S K₃
def K₅ := S K₄

def pred (n: nat): nat := begin
cases n,
case nat.zero: { exact Z },
case nat.succ: m { exact m }
end

theorem pr₀ : pred Z = Z := rfl.
theorem pr₁ : pred K₁ = Z := rfl.
theorem pr₂ : pred K₂ = K₁ := rfl.

theorem pred_succ_zero (n: nat): pred (S n) = n := rfl.

def sub (n m: nat): nat := nat.rec_on m n (λ m n_sub_m, pred n_sub_m).

#reduce sub Z K₂
#reduce sub K₅ K₂


example: sub nat.zero K₅ = nat.zero := rfl
theorem sub_n_0 (n: nat): sub n Z = n := rfl
theorem sub_0_m (m: nat): sub Z m = Z := begin
induction m,
case nat.zero: { reflexivity },
case nat.succ: m ih {
  calc sub Z (S m) = pred (sub Z m): rfl
   ... = pred Z: by rw ih
}
end

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

theorem sub_n_n (n: nat): sub n n = Z := begin
induction n,
case nat.zero: { reflexivity },
case nat.succ: n ih {
  have: sub (nat.succ n) (nat.succ n) = sub n n, from sub_succ n n,
  rw [this], assumption
}
end

def add (m n : nat) : nat := nat.rec_on n m (λ n add_m_n, S add_m_n)

lemma add_n_succ (m n: nat): add m (nat.succ n) = nat.succ (add m n) := rfl.
lemma add_m_succ (m n: nat): add (nat.succ m) n = nat.succ (add m n) := begin
induction n, reflexivity,
case nat.succ: n ih {
  simp[add_n_succ], assumption
}
end

lemma add_m_0 (m: nat): add m Z = m := rfl. 
lemma add_0_n (n: nat): add Z n = n := begin
induction n, reflexivity,
case nat.succ: n ih {
  simp[add_n_succ], assumption
}
end

theorem add_assoc (a b c: nat): add (add a b) c = add a (add b c) := begin
induction c, reflexivity,
case nat.succ: c ih {
  simp [add_n_succ], assumption,
}
end

theorem add_comm (m n : nat) : add m n = add n m :=
begin
  induction n,
  case nat.zero : { rw[<-Z, add_m_0, add_0_n] },
  case nat.succ : n ih { rw [add_n_succ, add_m_succ, ih] }
end

#reduce add K₁ K₂

def mul (m n: nat): nat := nat.rec_on n Z (λ n acc, add m acc)

#reduce mul Z K₂
#reduce mul K₂ Z
#reduce mul K₁ K₂
#reduce mul K₂ K₂
#reduce mul K₅ K₂

lemma mul_succ_n (m n: nat): mul m (nat.succ n) = add m (mul m n) := rfl.
lemma mul_succ_m (m n: nat): mul (nat.succ m) n = add (mul m n) n := begin
induction n, reflexivity,
case nat.succ: n ih {
  simp [mul_succ_n],
  rw ih,
  simp [add_n_succ, add_m_succ],
  simp [add_assoc],
}
end

theorem mul_m_0 (m: nat): mul m Z = Z := rfl.
theorem mul_0_n (n: nat): mul Z n = Z := begin
induction n,
  case nat.zero: {reflexivity},
  case nat.succ: n ih {
    rw [mul_succ_n Z n],
    rw ih, reflexivity
  }
end

theorem mul_m_1 (m: nat): mul m K₁ = m := rfl
theorem mul_1_n (n: nat): mul K₁ n = n := begin
  rw [K₁, S, Z],
  simp [mul_succ_m], 
  rw [<-Z, mul_0_n n, add_0_n] 
end

theorem mul_comm (m n: nat): mul m n = mul n m := begin
induction m, 
case nat.zero { 
  rw [<-Z, mul_m_0, mul_0_n],
},
case nat.succ: m ih {
  rw [mul_succ_n, mul_succ_m, ih, add_comm],
}
end

theorem mul_dist (a b c: nat): mul a (add b c) = add (mul a b) (mul a c) := begin
induction a,
case nat.zero {
  rw [<-Z, mul_0_n, mul_0_n, mul_0_n], reflexivity
},
case nat.succ: a ih {
  rw [mul_succ_m, mul_succ_m, mul_succ_m, ih],
  repeat { rw [add_assoc] },
  repeat { rw [<-add_assoc]},
  repeat { rw [add_assoc] },
  rw [<-add_assoc (mul a c), <-add_assoc b, add_comm (mul a c)],
}
end

theorem mul_assoc (a b c: nat): mul (mul a b) c = mul a (mul b c) := begin
induction c, reflexivity,
case nat.succ: c ih {
  rw [mul_succ_n, ih, mul_succ_n, mul_dist]
}
end

theorem succ_nonzero (n: nat): S n ≠ Z := by trivial.
def nonzero := {n: nat // n ≠ Z}
def nonzero.mk (n: nat) (h: n ≠ Z): nonzero := ⟨n,h⟩
def nz := nonzero.mk.
#check nz K₂ (by apply succ_nonzero)

def pow (m: nonzero) (n: nat): nat := nat.rec_on n K₁ (λ n acc, mul m.val acc)

def nzK₁ := nz (S Z) (by apply succ_nonzero)
def nzK₂ := nz (S K₁) (by apply succ_nonzero)
def nzK₃ := nz (S K₂) (by apply succ_nonzero)
def nzK₄ := nz (S K₃) (by apply succ_nonzero)
def nzK₅ := nz (S K₄) (by apply succ_nonzero)

#reduce pow nzK₂ Z
#reduce pow nzK₁ K₂
#reduce pow nzK₂ K₂
#reduce pow nzK₅ K₂

theorem pow_by_0 (m: nonzero): pow m Z = K₁ := rfl.
theorem pow_by_1 (m: nonzero): pow m K₁ = m.val := rfl.
theorem pow_by_succ (m: nonzero) (n: nat): pow m (nat.succ n) = mul m.val (pow m n) := rfl.
theorem pow_of_1 (n: nat): pow nzK₁ n = K₁ := begin
induction n, reflexivity,
case nat.succ: n ih {
  have o: nzK₁.val = K₁, from rfl,
  have: pow nzK₁ (nat.succ n) = mul nzK₁.val (pow nzK₁ n), by rw [pow_by_succ],
  rw [o, mul_1_n] at this,
  rw [this, ih]
}
end

theorem pow_by_add (m: nonzero) (a b: nat): pow m (add a b) = mul (pow m a) (pow m b) := begin
induction b, reflexivity,
case nat.succ: b ih {
  have sab: add a (nat.succ b) = nat.succ (add a b), by reflexivity,
  calc pow m (add a (nat.succ b)) = pow m (nat.succ (add a b)): by rw sab
    ... = mul m.val (pow m (add a b)): by rw pow_by_succ
    ... = mul m.val (mul (pow m a) (pow m b)): by rw ih
    ... = mul (mul m.val (pow m b)) (pow m a): by rw [mul_comm (pow m a), mul_assoc]
    ... = mul (pow m (nat.succ b)) (pow m a): by rw <-pow_by_succ
    ... = mul (pow m a) (pow m (nat.succ b)): by rw mul_comm
}
end

end hidden