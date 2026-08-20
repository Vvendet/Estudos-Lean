import Mathlib
import Mathlib.Data.Set.Basic
import Mathlib.Data.Rel
import Mathlib.Logic.Relation

structure ARS (α : Type) where
  red : SetRel α  α -- Definição de sistema abstrato de redução (ARS)
                                  -- Um conjunto de pares ordenados (a, b) onde a reduz a b
                                  -- α é o conjunto e Set (α × α) é a relação.

def Reduces {α : Type} (R : ARS α) (a b : α) : Prop :=
    (a, b) ∈ R.red    -- Definimos a noção de redução:
                      -- a reduz a b se o par (a, b) pertence à relação de
                      -- redução R.red.

theorem Reduces_iff {α : Type} (R : ARS α) (a b : α) : Reduces R a b ↔ (a, b) ∈ R.red :=
  by
  rfl

def ARS.id (α : Type) : SetRel α α :=
  { (a, a) | a ∈ Set.univ }  -- A relação identidade contém todos os pares
                             -- (a, a) para a ∈ α

def Reduces.pow {α : Type} (R : ARS α) : Nat → SetRel α α -- Definimos a relação
                                                          -- de redução em n passos,
                                                          -- que é a composição da
                                                          -- relação de redução R.red
                                                          -- consigo mesma n vezes.
  | 0 => ARS.id α
  | n + 1 => (Reduces.pow R n).comp R.red

def ARS.transitiveClosure {α : Type} (R : ARS α) : SetRel α α :=
  ⋃ i : {n : Nat // 0 < n}, (Reduces.pow R i.val)

def ReducesPlus {α : Type} (R : ARS α) (a b : α) : Prop :=
  (a, b) ∈ ARS.transitiveClosure R

def ARS.reflTransClosure {α : Type} (R : ARS α) : SetRel α α := -- A relação de redução
                                                                -- reflexiva e transitiva
  R.transitiveClosure ∪ ARS.id α

def ARS.reflTransClosure' {α : Type} (R : ARS α) : SetRel α α :=
  ⋃ i : Nat, (Reduces.pow R i)

lemma ARS.reflTransClosure_transitive {α : Type} (R : ARS α) (a b c : α)
  (h1 : (a, b) ∈ ARS.reflTransClosure R) (h2 : (b, c) ∈ ARS.reflTransClosure R) :
  (a, c) ∈ ARS.reflTransClosure R := by
  sorry

def ReducesStar {α : Type} (R : ARS α) (a b : α) : Prop :=
  (a, b) ∈ ARS.reflTransClosure R

lemma ReducesStar.trans_reduces {α : Type} (R : ARS α) (a b c : α) :
  ReducesStar R a b → Reduces R b c → ReducesStar R a c := by
  intro hxy hyz
  exact ARS.reflTransClosure_transitive hxy hyz

def ARS.ReflexiveClosure {α : Type} (R : ARS α) : SetRel α α := -- A relação de redução reflexiva
  R.red ∪ ARS.id α

def ReducesReflexive {α : Type} (R : ARS α) (a b : α) : Prop :=
  (a, b) ∈ ARS.ReflexiveClosure R

def ARS.inv {α : Type} (R : ARS α) : SetRel α α := -- A relação inversa de redução
  { (b, a) | (a, b) ∈ R.red }

def ReducesInv {α : Type} (R : ARS α) (a b : α) : Prop :=
  (a, b) ∈ ARS.inv R

def ARS.symmClosure {α : Type} (R : ARS α) : ARS α where -- o fecho simétrico de R
  red := R.red ∪ ARS.inv R

def ReducesSymm {α : Type} (R : ARS α) (a b : α) : Prop :=
  (a, b) ∈ (ARS.symmClosure R).red

def ARS.symmTransClosure {α : Type} (R : ARS α) : SetRel α α :=
  ⋃ i : {n : Nat // 0 < n}, (Reduces.pow R.symmClosure i.val)

def ReducesSymmTrans {α : Type} (R : ARS α) (a b : α) : Prop :=
  (a, b) ∈ ARS.symmTransClosure R

def ARS.reflSymmTransClosure {α : Type} (R : ARS α) : SetRel α α :=
  R.symmTransClosure ∪ ARS.id α

def ReducesReflSymmTrans {α : Type} (R : ARS α) (a b : α) : Prop :=
  (a, b) ∈ ARS.reflSymmTransClosure R

def IsNormal {α : Type} (R : ARS α) (x : α) : Prop :=
  ∀ y, ¬ Reduces R x y

theorem not_reduces_of_is_normal {α : Type} (R : ARS α) (x y : α) (h : IsNormal R x) :
 ¬ Reduces R x y :=
  h y

def WeaklyNormalizing {α : Type} (R : ARS α) : Prop :=
  ∀ x, ∃ y, ReducesStar R x y ∧ IsNormal R y

def StronglyNormalizing' {α : Type} (R : ARS α) : Prop :=
  WellFounded (fun x y => Reduces R x y)

def InfiniteReduction {α : Type} (R : ARS α) : Prop :=
  ∃ f : Nat → α, ∀ n, Reduces R (f n) (f (n + 1))


def StronglyNormalizing {α : Type} (R : ARS α) : Prop :=
  ¬ ∃ f : Nat → α, ∀ n, Reduces R (f n) (f (n + 1))

def HasInfiniteReduction {α : Type} (R : ARS α) : Prop :=
  ∃ f : Nat → α, ∀ n, Reduces R (f n) (f (n + 1))

def StronglyNormalizing'' {α : Type} (R : ARS α) : Prop :=
  ¬ HasInfiniteReduction R

def IsConfluent {α : Type} (R : ARS α) : Prop :=
  ∀ x y z, ReducesStar R x y → ReducesStar R x z → ∃ w, ReducesStar R y w ∧ ReducesStar R z w

def IsChurchRosser {α : Type} (R : ARS α) : Prop :=
  ∀ x y z, Reduces R x y → Reduces R x z → ∃ w, ReducesStar R y w ∧ ReducesStar R z w

def IsReducible {α : Type} (R : ARS α) (x : α) : Prop :=
  ∃ y, Reduces R x y

def IsANormalFormOf {α : Type} (R : ARS α) (x y : α) : Prop :=
  ReducesStar R x y ∧ IsNormal R y

def ThereIsNoReduction {α : Type} (R : ARS α) (x : α) : Prop :=
  ¬ ∃ y, Reduces R x y

lemma IsNormal_if_ThereIsNoReduction {α : Type} (R : ARS α) (x : α)
(h : ThereIsNoReduction R x) : IsNormal R x := by
  rw [IsNormal]
  intro y
  rw [ThereIsNoReduction] at h
  push_neg at h
  exact h y

def IsDirectSuccessorOf {α : Type} (R : ARS α) (x y : α) : Prop :=
  Reduces R x y

def IsSuccessorOf {α : Type} (R : ARS α) (x y : α) : Prop :=
  ReducesStar R x y

def IsJoinable {α : Type} (R : ARS α) (x y : α) : Prop :=
  ∃ z, ReducesStar R x z ∧ ReducesStar R y z

example {α : Type} (R : ARS α) (x y : α) (h : IsJoinable R x y) :
  ∃ z, ReducesStar R x z ∧ ReducesStar R y z :=
  h

lemma not_normal_reduces
    {α : Type} {R : ARS α} {x : α}
    (h : ¬ IsNormal R x) :
    ∃ y, Reduces R x y := by
  rw [IsNormal] at h
  push_neg at h
  exact h

lemma exists_infinite_reduction_of_not_normalizing

    {α : Type} (R : ARS α) (x : α)

    (h : ¬ ∃ y, ReducesStar R x y ∧ IsNormal R y) :

    ∃ f : Nat → α, f 0 = x ∧

      ∀ n, Reduces R (f n) (f (n + 1)) := by

      push Not at h

      have hxx : ReducesStar R x x := by

        rw [ReducesStar]

        rw [ARS.reflTransClosure]

        right

        rw [ARS.id]

        apply Set.mem_setOf_eq.mpr

        simp

      have h1 : ¬ IsNormal R x := h x hxx

      have h2 : ∃ y, Reduces R x y := not_normal_reduces h1

      have hxy : ReducesStar R x (Classical.choose h2) := by

        rw [ReducesStar, ARS.reflTransClosure, ARS.transitiveClosure]

        left

        refine Set.mem_iUnion.mpr ⟨⟨1, Nat.zero_lt_one⟩, ?_⟩

        simpa [Reduces.pow, ARS.id, Reduces] using Classical.choose_spec h2

      let f : Nat → α := fun n =>

        if n = 0 then x else

          Classical.choose h2

      have hf0 : f 0 = x := by simp [f]

      have hf : ∀ n, Reduces R (f n) (f (n + 1)) := by

        intro n

        induction n with

        | zero =>

          simp [f]

          exact Classical.choose_spec h2

        | succ n ih =>

          simp [f]


theorem WeaklyNormalizing_if_StronglyNormalizing {α : Type} (R : ARS α)
(h : StronglyNormalizing R) : WeaklyNormalizing R :=
  by
  sorry
