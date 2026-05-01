import Init.Data.Nat.Basic

theorem first_theorem : ∀ a : Nat,  a + 0 = a := by
  intro a
  rfl

theorem second_theorem : ∀ a : Nat, a + 0 = 0 +a := by
  intro a
  simp

theorem third_theorem : ∀ a b : Nat, a + b = b + a := by
  intro a b
  induction a with
  | zero =>
    simp
  | succ n ih =>
    simp [Nat.succ_add]
    simp [ih]
    simp [Nat.add_assoc]

example : (1 = 1) → (2 = 2) := fun _ => rfl
