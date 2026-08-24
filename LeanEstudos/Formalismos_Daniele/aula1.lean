import Mathlib
import Mathlib.Data.Set.Basic
import Mathlib.Data.Rel
import Mathlib.Logic.Relation

-- Definições de sistemas abstratos de redução (ARS) e propriedades relacionadas.
-----------------------------------------
-----------------------------------------


structure ARS (α : Type) where
  red : SetRel α  α -- Definição de sistema abstrato de redução (ARS)
                                  -- Um conjunto de pares ordenados (a, b) onde a reduz a b
                                  -- α é o conjunto e Set (α × α) é a relação.

def Reduces {α : Type} (R : ARS α) (a b : α) : Prop :=
    (a, b) ∈ R.red    -- Definimos a noção de redução:
                      -- a reduz a b se o par (a, b) pertence à relação de
                      -- redução R.red.


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


def ReducesStar {α : Type} (R : ARS α) (a b : α) : Prop :=
  (a, b) ∈ ARS.reflTransClosure R


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

def ARS.reflSymmTransClosure' {α : Type} (R : ARS α) : SetRel α α :=
  R.symmTransClosure ∪ ARS.id α

def ARS.reflSymmTransClosure {α : Type} (R : ARS α) : SetRel α α :=
  { (a, b) | Relation.EqvGen (fun x y => (x, y) ∈ R.red) a b }

def ReducesReflSymmTrans {α : Type} (R : ARS α) (a b : α) : Prop :=
  (a, b) ∈ ARS.reflSymmTransClosure R

def IsNormal {α : Type} (R : ARS α) (x : α) : Prop :=
  ∀ y, ¬ Reduces R x y


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


def IsJoinable {α : Type} (R : ARS α) (x y : α) : Prop :=
  ∃ z, ReducesStar R x z ∧ ReducesStar R y z

def IsConfluent {α : Type} (R : ARS α) : Prop :=
  ∀ x y z, ReducesStar R x y → ReducesStar R x z → ∃ w, ReducesStar R y w ∧ ReducesStar R z w

def IsChurchRosser {α : Type} (R : ARS α) : Prop :=
  ∀ x y, ReducesReflSymmTrans R x y → IsJoinable R x y

def IsReducible {α : Type} (R : ARS α) (x : α) : Prop :=
  ∃ y, Reduces R x y

def IsANormalFormOf {α : Type} (R : ARS α) (x y : α) : Prop :=
  ReducesStar R x y ∧ IsNormal R y

def ThereIsNoReduction {α : Type} (R : ARS α) (x : α) : Prop :=
  ¬ ∃ y, Reduces R x y


def IsDirectSuccessorOf {α : Type} (R : ARS α) (x y : α) : Prop :=
  Reduces R x y

def IsSuccessorOf {α : Type} (R : ARS α) (x y : α) : Prop :=
  ReducesStar R x y


-- Resultados e teoremas sobre sistemas abstratos de redução (ARS) e suas propriedades.
-----------------------------------------
-----------------------------------------


example {α : Type} (R : ARS α) (x y : α) (h : IsJoinable R x y) :
  ∃ z, ReducesStar R x z ∧ ReducesStar R y z :=
  h

lemma Reduces.pow_trans
  {α : Type} (R : ARS α) {a b c : α} (n m : Nat)
  (h1 : (a, b) ∈ Reduces.pow R m) (h2 : (b, c) ∈ Reduces.pow R n) :
  (a, c) ∈ Reduces.pow R (m + n) := by
  induction n generalizing b c with
  | zero =>
    rw [Reduces.pow.eq_def, ARS.id] at h2
    have hbc : b = c := by
      simpa [ARS.id] using h2
    subst c
    simpa using h1
  | succ n ih =>
    rw [Reduces.pow.eq_def] at h2
    rcases h2 with ⟨d, hbd, hdc⟩
    have had : (a, d) ∈ Reduces.pow R (m + n) := by
      exact ih h1 hbd
    rw [Reduces.pow.eq_def]
    exact ⟨d, had, hdc⟩


lemma IsNormal_if_ThereIsNoReduction {α : Type} (R : ARS α) (x : α)
(h : ThereIsNoReduction R x) : IsNormal R x := by
  rw [IsNormal]
  intro y
  rw [ThereIsNoReduction] at h
  push Not at h
  exact h y

lemma ARS.transitiveClosure_transitive {α : Type} (R : ARS α) (a b c : α)
  (h1 : (a, b) ∈ ARS.transitiveClosure R) (h2 : (b, c) ∈ ARS.transitiveClosure R) :
  (a, c) ∈ ARS.transitiveClosure R := by
  rw [ARS.transitiveClosure] at h1 h2
  rcases Set.mem_iUnion.mp h1 with ⟨m, hm⟩
  rcases Set.mem_iUnion.mp h2 with ⟨n, hn⟩
  have hac : (a, c) ∈ Reduces.pow R (m + n) := by
    exact Reduces.pow_trans R (n := n.val) (m := m.val) hm hn
  have hmn : 0 < m.val + n.val := by
    omega
  refine Set.mem_iUnion.mpr ⟨⟨m.val + n.val, hmn⟩, hac⟩


lemma ARS.reflTransClosure_transitive
    {α : Type} (R : ARS α) (a b c : α)
    (h1 : (a, b) ∈ ARS.reflTransClosure R)
    (h2 : (b, c) ∈ ARS.reflTransClosure R) :
    (a, c) ∈ ARS.reflTransClosure R := by
  rw [ARS.reflTransClosure] at h1 h2 ⊢
  rcases h1 with h1 | h1 <;>
    rcases h2 with h2 | h2
  · left
    exact ARS.transitiveClosure_transitive R a b c h1 h2
  · left
    have hbc : b = c := by
      simpa [ARS.id] using h2
    rw [← hbc]
    exact h1
  · left
    have hab : a = b := by
      simpa [ARS.id] using h1
    rw [hab]
    exact h2
  · right
    have hab : a = b := by
      simpa [ARS.id] using h1
    have hbc : b = c := by
      simpa [ARS.id] using h2
    rw [ARS.id]
    simp [hab, hbc]


lemma ReducesStar.trans_reduces {α : Type} (R : ARS α) (a b c : α) :
  ReducesStar R a b → Reduces R b c → ReducesStar R a c := by
  intro hxy hyz
  apply ARS.reflTransClosure_transitive R a b c hxy
  rw [ARS.reflTransClosure, ARS.transitiveClosure]
  left
  refine Set.mem_iUnion.mpr ⟨⟨1, Nat.zero_lt_one⟩, ?_⟩
  simpa [Reduces.pow, ARS.id, Reduces] using hyz

theorem not_reduces_of_is_normal {α : Type} (R : ARS α) (x y : α) (h : IsNormal R x) :
 ¬ Reduces R x y :=
  h y

lemma not_normal_reduces
    {α : Type} {R : ARS α} {x : α}
    (h : ¬ IsNormal R x) :
    ∃ y, Reduces R x y := by
  rw [IsNormal] at h
  push Not at h
  exact h

lemma Reduces.toReducesStar
    {α : Type} {R : ARS α} {a b : α} :
    Reduces R a b → ReducesStar R a b := by
  intro h
  rw [ReducesStar, ARS.reflTransClosure, ARS.transitiveClosure]
  left
  refine Set.mem_iUnion.mpr ⟨⟨1, Nat.zero_lt_one⟩, ?_⟩
  simpa [Reduces.pow, ARS.id, Reduces] using h

lemma ReducesStar.trans
    {α : Type} {R : ARS α} {a b c : α} :
    ReducesStar R a b →
    ReducesStar R b c →
    ReducesStar R a c := by
  intro hxy hyz
  apply ARS.reflTransClosure_transitive R a b c hxy hyz


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
      have hnext : ∀ y, ReducesStar R x y → ∃ z, Reduces R y z := by
        intro y hxy'
        have h1' : ¬ IsNormal R y := h y hxy'
        exact not_normal_reduces h1'
      let next :
          {y : α // ReducesStar R x y} →
          {y : α // ReducesStar R x y} :=
        fun p =>
          let z := Classical.choose (hnext p.1 p.2)
          have hpz : ReducesStar R p.1 z := by
            exact Reduces.toReducesStar
              (Classical.choose_spec (hnext p.1 p.2))
          ⟨z, ReducesStar.trans p.2 hpz⟩
      let F : Nat → {y : α // ReducesStar R x y} :=
        Nat.rec ⟨x, hxx⟩ (fun _ p => next p)
      let f : Nat → α := fun n => (F n).1
      have hf0 : f 0 = x := by
        simp [f, F]
      have hf : ∀ n, Reduces R (f n) (f (n + 1)) := by
        intro n
        simp only [f, F]
        exact Classical.choose_spec (hnext (F n).1 (F n).2)
      exact ⟨f, hf0, hf⟩



theorem WeaklyNormalizing_if_StronglyNormalizing {α : Type} (R : ARS α)
(hsn : StronglyNormalizing R) : WeaklyNormalizing R := by
  intro x
  by_contra h
  push Not at h
  have h1 : ¬ ∃ y, ReducesStar R x y ∧ IsNormal R y := by
    intro hy
    exact h hy.choose hy.choose_spec.1 hy.choose_spec.2
  have h2 : ∃ f : Nat → α, f 0 = x ∧ ∀ n, Reduces R (f n) (f (n + 1)) :=
    exists_infinite_reduction_of_not_normalizing R x h1
  obtain ⟨f, hf0, hf⟩ := h2
  exact hsn ⟨f, hf⟩
