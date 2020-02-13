namespace hidden

def divides (m n : ℕ) : Prop := ∃ k, m * k = n

instance : has_dvd nat := ⟨divides⟩

def even (n : ℕ) : Prop := 2 ∣ n -- You can enter the '∣' character by typing \mid

section
  variables m n : ℕ

  #check m ∣ n
  #check m^n
  #check even (m^n +3)
end

end hidden

def prime (n : ℕ) : Prop := ∀ m: ℕ, m ∣ n -> m = 1 ∨ m = n

def infinitely_many_primes : Prop := ∀ n: ℕ, prime n -> ∃ n': ℕ, n' > n ∧ prime n'

def Fermat_prime (n : ℕ) : Prop := prime n ∧ ∃ m: ℕ, n = 2^2^m

def infinitely_many_Fermat_primes : Prop := ∀ n: ℕ, Fermat_prime n -> ∃ n': ℕ, n' > n ∧ Fermat_prime n'

def goldbach_conjecture : Prop := ∀ n: ℕ, 2 ∣ n -> ∃ (m m': ℕ), n = m + m' ∧ prime m ∧ prime m'

def Goldbach's_weak_conjecture : Prop := ∀ n: ℕ, n > 5 ∧ ¬ (2 ∣ n) -> 
  ∃ (p1 p2 p3: ℕ), prime p1 ∧ prime p2 ∧ prime p3 ∧ n = p1 + p2 + p3 

def Fermat's_last_theorem : Prop := ∀ (a b c n: ℕ), n > 2 -> a^n + b^n ≠ c^n