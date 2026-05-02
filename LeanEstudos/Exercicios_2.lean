-- Exercicios da seção 2
import Init.Data.Nat.Div.Basic


theorem ex1 : ¬ (∃ a: Nat, 2*a= 1) := by
  intro h
  have h1 : 0 = 1 % 2 := by omega
  contradiction

theorem ex2 (n: Nat) : (∃ a: Nat, n=2*a) → (∃ b: Nat, 2*n = 2*b):= by
  intro h
  cases h with
  | intro a ha
  have eq : 2*n = 2*(2*a) := by omega
  exact ⟨2*a, eq⟩

theorem ex3 (a b : Nat) : (a ∣ b) → (a ∣ (b+b)) := by
  intro h1
  cases h1 with
  |intro k hk
  have eq : b + b = a*(k+k) := by rw [hk, Nat.left_distrib]
  exact ⟨k+k, eq⟩

theorem ex4 (a b c: Nat) : (a ∣ b)→ (a ∣ c) → (a ∣ (b+c)) := by
  intro h1 h2
  cases h1 with
  | intro k1 hk1
  cases h2 with
  | intro k2 hk2
  have eq : b + c = a*(k1+k2) := by rw [hk1, hk2, Nat.left_distrib]
  exact ⟨ k1+k2, eq ⟩

theorem ex5 (a b c: Nat) : (a ∣ b) → (a ∣ (b*c)) := by
  intro h1
  cases h1 with
  | intro k hk
  have eq : b*c = a*(k*c) := by rw [hk, Nat.mul_assoc]
  exact ⟨ k*c, eq ⟩

theorem ex6 (a b c: Nat) : (a∣b) → (b∣c) → (a∣c) := by
  intro h1 h2
  cases h1 with
  | intro k1 hk1
  cases h2 with
  | intro k2 hk2
  have eq : c = a*(k1*k2) := by rw [hk2, hk1, Nat.mul_assoc]
  exact ⟨ k1*k2, eq ⟩
