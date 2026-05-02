import Init.Data.Nat.Basic

example : True ∧ True := by
  constructor
  -- Now we have TWO goals:
  -- case left:  ⊢ True
  -- case right: ⊢ True
  · trivial   -- Solve first goal
  · trivial   -- Solve second goal

example : True ∧ True := by
  constructor
  { trivial }  -- First goal
  { trivial }  -- Second goal

-- Or just chain them (when order is unambiguous)
example : True ∧ True := by
  constructor <;> trivial  -- Apply trivial to all goals

example (a b : Nat) : a + b = b + a := by
  -- State: a b : Nat ⊢ a + b = b + a

  rw [Nat.add_comm]
  -- State: a b : Nat ⊢ b + a = b + a

-- exercicio a = b → b = a
example (a b : Nat) : a = b → b = a := by
  intro h
  rw [h]
  -- State: a b : Nat, h : a = b ⊢ b = a

example (a b : Nat) : a + b = b + a := by
  simp [Nat.add_comm]


-- exact: specify the proof term
example (P : Prop) (hp : P) : P := by
  exact hp

-- assumption: auto-search hypotheses
example (P : Prop) (hp : P) : P := by
  assumption  -- Finds hp automatically

-- rfl: definitional equality
example : (2 : Nat) = 2 := by
  rfl

-- trivial: handles True and similar goals
example : True := by
  trivial

example (P Q : Prop) : P → Q → P := by
  intro hp hq
  exact hp

example (a b c : Nat) : a + b + c = c + b + a := by
  have h1: (a + b) + c = c + (a + b) := Nat.add_comm (a + b) c
  have h2:  c + (a + b) = c + (b + a) := by rw [Nat.add_comm a b]
  have h3: c + (b + a) = c + b + a := Eq.symm (Nat.add_assoc c b a)
  rw [h1, h2, h3]

theorem e7 (a b c: Nat) : (a ∣ b) → (a∣c) → (∀ x y : Nat, a∣(x*b + y*c)) := by
  intro h1 h2
  cases h1 with
  | intro k1 hk1
  cases h2 with
  | intro k2 hk2
  intro x y
  have eq : x*b + y*c = a*(x*k1 + y*k2) := by
    rw [hk1, hk2]
    have lema1 : x*(a*k1) = a*(x*k1) := by simp [Nat.mul_left_comm]
    have lema2 : y*(a*k2) = a*(y*k2) := by simp [Nat.mul_left_comm]
    rw [lema1,lema2, Nat.mul_add]
  exact ⟨x*k1 + y*k2, eq⟩
