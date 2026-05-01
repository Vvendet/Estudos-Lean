import LeanEstudos.Basic
import Init.Data.Nat.Basic
---------------------------------------------------------
------------ TIPOS --------------------------------------
-- Equality is a proposition
#check (5 = 5)        -- 5 = 5 : Prop
#check (1 + 1 = 2)    -- 1 + 1 = 2 : Prop
#check (1 + 1 = 3)    -- 1 + 1 = 3 : Prop (still a valid Prop, just false)

-- Equality for any type
#check ("hello" = "hello")  -- "hello" = "hello" : Prop
#check ([1,2] = [1,2])      -- [1, 2] = [1, 2] : Prop

-- True: a proposition that's trivially provable
#check True       -- True : Prop
example : True := trivial

-- A prova de True possui apenas um termo, por isso é true.
-- Quando uma proposição não possui termos, é falso.

-- False: a proposition with no proof
#check False      -- False : Prop
-- example : False := ???  -- Impossible! No term has type False



---------------------------------------------------------
------------ FUCÇÕES--------------------------------------
example : (1 = 1) → (2 = 2) := fun _ => rfl

-- "If A then B" is the type A → B
-- A proof is a function from proofs of A to proofs of B

example : True → True := fun _ => trivial

-- "If 1 = 1, then 2 = 2"
example : (1 = 1) → (2 = 2) := fun _ => rfl

-- Read: given a proof of 1 = 1, return a proof of 2 = 2
-- The proof of 1 = 1 isn't even used—2 = 2 is independently true



---------------------------------------------------------
------------ OPERADORES LÓGICOS --------------------------------------
-- AND is defined like a structure
-- structure And (a b : Prop) : Prop where
--   left : a
--   right : b

-- To prove A ∧ B, provide proofs of both
example : True ∧ True := ⟨trivial, trivial⟩

example : (1 = 1) ∧ (2 = 2) := ⟨rfl, rfl⟩

-- Access parts with .left and .right (or .1 and .2)
example (h : True ∧ (1 = 1)) : True := h.left
example (h : True ∧ (1 = 1)) : 1 = 1 := h.right

-- OR has two constructors
-- inductive Or (a b : Prop) : Prop where
--   | inl : a → Or a b
--   | inr : b → Or a b

-- Prove left side
example : True ∨ False := Or.inl trivial

-- Prove right side
example : False ∨ True := Or.inr trivial

-- Either side works
example : (1 = 1) ∨ (1 = 2) := Or.inl rfl

-- NEGACAO
-- ¬A is defined as A → False
#print Not  -- def Not (a : Prop) : Prop := a → False

-- To prove ¬A, assume A and derive a contradiction
example : ¬False := fun h => h  -- If False, then False (trivially)

-- 1 ≠ 2 means (1 = 2) → False
example : 1 ≠ 2 := by decide


--QUANTIFICADORES

-- ∀ x : T, P x is a dependent function type
-- A proof is a function that works for any x

example : ∀ n : Nat, 0 + n = n := by
  intro n
  simp

-- Multiple quantifiers
example : ∀ a b : Nat, a + b = b + a := Nat.add_comm

-- ∃ x : T, P x is a dependent pair (witness + proof)
-- Provide a specific x and prove P holds for it

example : ∃ n : Nat, n > 5 := ⟨10, by decide⟩

example : ∃ n : Nat, n + n = 10 := ⟨5, rfl⟩

-- The witness and proof are bundled together
example : ∃ s : String, s.length = 5 := ⟨"hello", rfl⟩

theorem tt1 (P  :Prop) (Q : Prop) (hp : P) (hq : Q): P ∧ Q :=  ⟨ hp ,  hq⟩

------------------------------------------------------

example :  1 + 3 = 3 + 1:= rfl

example : 1 + 3 = 3 + 1 := by omega



-- exercício 1 (3 formas de demonstrar a transitividade lógica, se P implica Q e Q implica R, então P implica R)


theorem transitividade_logica (P : Prop) (Q : Prop) (R:Prop) (hr : R) :
(P → Q) → (Q → R) → ( P → R ) := fun _ => fun _ => fun _ => hr

theorem trans_imp (P Q R : Prop) :
  (P → Q) → (Q → R) → (P → R) := by
  intro hPQ
  intro hQR
  intro hP
  exact hQR (hPQ hP)

theorem trans_imp2 (P Q R : Prop) :
  (P → Q) → (Q → R) → (P → R) :=
  fun hPQ hQR hP => hQR (hPQ hP)

----- Exercício 2
-- (∀x,P(x)→Q(x))→((∀x,P(x))→(∀x,Q(x)))

theorem transitivdade_polinomial (x: Type) (P Q :  x → Prop)  :
(∀ x , P x → Q x) → (∀ x, P x) → (∀ x, Q x):= by
  intro hPQ
  intro hP
  intro a
  have hPa : P a := hP a
  have hQa : Q a := hPQ a hPa
  exact hQa

theorem transitivdade_polinomial2 (x: Type) (P Q :  x → Prop)  :
(∀ x , P x → Q x) → (∀ x, P x) → (∀ x, Q x):=
  fun hPQ hP a => hPQ a (hP a)

-- Exercício 3
-- (∃x,P(x)∧Q(x))→(∃x,P(x))

theorem transitivdade_polinomial3 (x: Type) (P Q :  x → Prop)  :
(∃ x , P x ∧ Q x) → (∃ x, P x) := by
  intro h
  cases h with
  | intro a hPQ =>
    have hPa : P a := hPQ.left
    exact ⟨a, hPa⟩

theorem transitivdade_polinomial4 (x: Type) (P Q :  x → Prop)  :
(∃ x , P x ∧ Q x) → (∃ x, P x) :=
  fun h =>
  match h with
  | ⟨a, hPQ⟩ =>
    have hPa : P a := hPQ.left
    ⟨a, hPa⟩

-- exercício 4
-- (∀x,P(x)→Q(x))→((∃x,P(x))→(∃x,Q(x))))

theorem transitivdade_polinomial5 (x: Type) (P Q : x → Prop) :
(∀ x, P x → Q x) → ((∃ x, P x) → (∃ x, Q x)) := by
  intro hPQ
  intro hP
  cases hP with
  | intro a hPa =>
    have hQa : Q a := hPQ a hPa
    exact ⟨a, hQa⟩

theorem transitivdade_polinomial6 (x: Type) (P Q : x → Prop) :
(∀ x, P x → Q x) → ((∃ x, P x) → (∃ x, Q x)) :=
  fun hPQ hP =>
  match hP with
  | ⟨a, hPa⟩ =>
    have hQa : Q a := hPQ a hPa
    ⟨a, hQa⟩
