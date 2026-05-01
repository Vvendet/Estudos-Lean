-- Exercícios da seção 1

theorem ex1 (n : Nat): (∃ k: Nat, n = 4 * k) → (∃ m: Nat, n = 2*m):= by
  intro h
  cases h with
  | intro k hk
  have h2 : n = 2 * (2 * k) := Nat.mul_assoc 2 2 k ▸ hk
  exact ⟨2 * k, h2⟩

theorem ex2 (n m : Nat): (∃ a: Nat, n = 2 * a) ∧ (∃ b: Nat, m = 2 * b) → (∃ c: Nat, n + m = 2 * c) := by
  intro h1
  cases h1 with
  | intro h2 h3 =>
    cases h2 with
    | intro a ha =>
      cases h3 with
      | intro b hb =>
        have h4 : n + m = 2 * a + 2 * b := by simp [ha, hb]
        have h5 : n + m = 2 * (a + b) := by simp [h4, Nat.mul_add]
        exact ⟨a + b, h5⟩

theorem ex3 (n : Nat): (∃ a: Nat, n=2*a) → (∃ b: Nat, n*n = 4*b):=
  by
    intro h
    cases h with
    | intro a ha
    have comutacao1 : a*2 = 2*a := by rw [Nat.mul_comm]
    have associacao3 : 2*(2*a) = 2*2*a:= by rw [Nat.mul_assoc]
    have n_square1 : n*n = 2*a*2*a := by simp [ha, Nat.mul_assoc]
    have n_square2 : n*n = 4*(a*a) := by simp [n_square1, comutacao1, associacao3,Nat.mul_assoc]
    exact ⟨a*a,n_square2⟩

theorem ex4 (n : Nat): (∃ a: Nat, n= 2*a) → ¬(∃ b: Nat, n = 2*b + 1) := by
  intro h_even h_odd
  cases h_even with
  | intro a ha =>
    cases h_odd with
    | intro b hb =>
    have h1 : 0 = 1 % 2 := by omega
    contradiction
