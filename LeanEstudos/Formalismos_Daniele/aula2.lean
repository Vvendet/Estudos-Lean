import LeanEstudos.Formalismos_Daniele.aula1
import Init.WF
import Init.Data.List.Basic
import Init.Data.List.Range
import Mathlib.Order.KonigLemma
import Mathlib.SetTheory.Descriptive.Tree
import Mathlib.Order.Atoms.Finite
import Mathlib.Data.Subtype
---
--def ARS.IsWellFounded {α : Type} (R : ARS α) : Prop :=
--    WellFounded (fun x y => Reduces R x y)

--def ARS.IsWellFounded' {α : Type} (R : ARS α) : Prop :=
--  ∀ x, Acc (fun x y => Reduces R x y) x

def ARS.WFI {α : Type} (R : ARS α) : Prop :=
  ∀ P : α → Prop, (∀ x, (∀ y, Reduces R x y → P y) → P x) → ∀ x, P x

theorem ARS.WFI_iff_StronglyNormalizing {α : Type} (R : ARS α) :
  ARS.WFI R ↔ StronglyNormalizing R := by
  constructor
  · intro hWFI
    rw [StronglyNormalizing]
    intro hInf
    rcases hInf with ⟨f, hf⟩
    let P : α → Prop :=
      fun x =>
        ¬ ∃ g : Nat → α,
          g 0 = x ∧
          ∀ n, Reduces R (g n) (g (n + 1))
    have hP : ∀ x, (∀ y, Reduces R x y → P y) → P x := by
      intro x hx hnot
      rcases hnot with ⟨g, hg0, hg⟩
      have hstep : Reduces R x (g 1) := by
        simpa [hg0] using hg 0
      have hPg1 : P (g 1) := hx (g 1) hstep
      let g' : Nat → α := fun n => g (n + 1)
      have hg'0 : g' 0 = g 1 := by
        simp [g']
      have hg' : ∀ n, Reduces R (g' n) (g' (n + 1)) := by
        intro n
        simpa [g', Nat.add_assoc] using hg (n + 1)
      exact hPg1 ⟨g', hg'0, hg'⟩
    have hPx : P (f 0) := hWFI P hP (f 0)
    apply hPx
    refine ⟨f, ?_, hf⟩
    rfl
  · intro hSN
    rw [StronglyNormalizing] at hSN
    intro P hP x
    by_contra hx
    let S := {z : α // ¬ P z}
    have next : ∀ z : S, ∃ y : S, Reduces R z.1 y.1 := by
      intro z
      by_contra hn
      apply z.2
      apply hP z.1
      intro y hzy
      by_contra hpy
      exact hn ⟨⟨y, hpy⟩, hzy⟩
    let step : S → S := fun z => Classical.choose (next z)
    have hstep : ∀ z : S, Reduces R z.1 (step z).1 := by
      intro z
      exact Classical.choose_spec (next z)
    let fS : Nat → S := fun n => Nat.rec ⟨x, hx⟩ (fun _ z => step z) n
    let f : Nat → α := fun n => (fS n).1
    have hf : ∀ n, Reduces R (f n) (f (n + 1)) := by
      intro n
      simpa [f, fS] using hstep (fS n)
    exact hSN ⟨f, hf⟩

def IsReductionPath {α : Type} (R : ARS α) : List α → Prop
  | [] => False
  | [_] => True
  | x :: y :: xs =>
      Reduces R x y ∧ IsReductionPath R (y :: xs)

lemma IsReductionPath.ne_nill {α : Type} {R : ARS α} {p : List α} (hp : IsReductionPath R p) :
p ≠ [] := by
  cases p with
  | nil =>
    simp [IsReductionPath] at hp
  | cons x xs =>
    simp

lemma IsReductionPath.singleton {α : Type} {R : ARS α} (x : α) :
IsReductionPath R [x] := by
  simp [IsReductionPath]

lemma IsReductionPath.pair_iff
    {α : Type} {R : ARS α} (x y : α) :
    IsReductionPath R [x, y] ↔ Reduces R x y := by
  simp [IsReductionPath]

lemma IsReductionPath.append_singleton_iff
    {α : Type} {R : ARS α}
    {p : List α} (hp : IsReductionPath R p) (c : α) :
    IsReductionPath R (p ++ [c]) ↔
      Reduces R (p.getLast (IsReductionPath.ne_nill hp)) c := by
  induction p with
  | nil =>
      simp [IsReductionPath] at hp
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp [IsReductionPath]
      | cons y ys =>
          have hxy : Reduces R x y := hp.1
          have htail : IsReductionPath R (y :: ys) := hp.2
          have ih' :
              IsReductionPath R ((y :: ys) ++ [c]) ↔
                Reduces R ((y :: ys).getLast htail.ne_nill) c :=
            ih htail
          simpa [IsReductionPath, hxy, ih'] using
            (show
              Reduces R x y ∧
                IsReductionPath R ((y :: ys) ++ [c]) ↔
              Reduces R ((x :: y :: ys).getLast hp.ne_nill) c
             from by
               rw [ih']
               constructor
               · intro h
                 exact h.2
               · intro h
                 exact ⟨hxy, h⟩)

lemma IsReductionPath.of_append_singleton
    {α : Type} {R : ARS α}
    {p : List α} {c : α}
    (hp : IsReductionPath R p)
    (hpc : Reduces R (p.getLast hp.ne_nill) c) :
    IsReductionPath R (p ++ [c]) := by
  exact (IsReductionPath.append_singleton_iff hp c).mpr hpc

def ReductionTree {α : Type} (R : ARS α) (x : α) : Set α :=
  { y | ReducesStar R x y }

def ReductionTree' {α : Type} (R : ARS α) (x : α) : Set α :=
  { y | (x, y) ∈ ARS.reflTransClosure R }

def ARS.ReductionTree {α : Type} (R : ARS α) (a : α) : Set (List α) :=
  { p | p ≠ [] ∧ p.head? = some a ∧ IsReductionPath R p }

def List.label {α : Type} : {p : List α // p ≠ []} → α :=
  fun p => p.1.getLast p.2

def ReductionTree.label
    {α : Type} {R : ARS α} {a : α}
    (p : List α) (hp : p ∈ R.ReductionTree a) : α :=
  p.getLast (by
    simpa [ARS.ReductionTree] using hp.1)

def ARS.Label
    {α : Type} {R : ARS α} {a : α}
    (p : {p : List α // p ∈ R.ReductionTree a}) : α :=
  p.val.getLast (by
    simpa [ARS.ReductionTree] using p.property.1)

def ARS.IsChildOf
    {α : Type} (R : ARS α) (a : α)
    (p q : {p : List α // p ∈ R.ReductionTree a}) : Prop :=
  ∃ c : α,
    q.val = p.val ++ [c] ∧
    Reduces R (ARS.Label p) c

theorem mem_ReductionTree_append_iff
    {α : Type} (R : ARS α) (a : α)
    (p : List α) (hp : p ∈ R.ReductionTree a) (c : α) :
    p ++ [c] ∈ R.ReductionTree a ↔
      Reduces R (p.getLast hp.1) c := by
  have hpath : IsReductionPath R p := hp.2.2
  constructor
  · intro hpc
    have hpath' : IsReductionPath R (p ++ [c]) := hpc.2.2
    exact (IsReductionPath.append_singleton_iff hpath c).mp hpath'
  · intro hpc
    have hpath' : IsReductionPath R (p ++ [c]) := by
      exact (IsReductionPath.append_singleton_iff hpath c).mpr hpc
    constructor
    · simp [hp.1]
    · constructor
      · simp [hp.2.1]
      · exact hpath'

theorem ARS.isChildOf_iff
    {α : Type} (R : ARS α) (a : α)
    (p q : {p : List α // p ∈ R.ReductionTree a}) :
    ARS.IsChildOf R a p q ↔
      ∃ c : α,
        q.val = p.val ++ [c] ∧
        Reduces R (ARS.Label p) c := by
  rfl

lemma ReductionTree_eq_ReductionTree' {α : Type} (R : ARS α) (x : α) :
  ReductionTree R x = ReductionTree' R x := by
  ext y
  constructor
  · intro h
    rw [ReductionTree] at h
    rw [ReductionTree']
    exact h
  · intro h
    rw [ReductionTree'] at h
    rw [ReductionTree]
    exact h

def ARS.finitelyBranching {α : Type} (R : ARS α) : Prop :=
  ∀ x, Set.Finite {y | Reduces R x y}

def ARS.finitelyBranching' {α : Type} (R : ARS α) : Prop :=
  ∀ x, Set.Finite {y | (x, y) ∈ R.red}

lemma ARS.finitelyBranching_iff_finitelyBranching' {α : Type} (R : ARS α) :
  ARS.finitelyBranching R ↔ ARS.finitelyBranching' R := by
  constructor
  · intro h
    rw [ARS.finitelyBranching] at h
    rw [ARS.finitelyBranching']
    simp only [Reduces] at h
    exact h
  · intro h
    rw [ARS.finitelyBranching'] at h
    rw [ARS.finitelyBranching]
    simp only [Reduces]
    exact h

def StronglyNormalizingAt {α : Type} (R : ARS α) (a : α) : Prop :=
  ¬ ∃ f : Nat → α,
    f 0 = a ∧
    ∀ n, Reduces R (f n) (f (n + 1))

lemma ARS.IsChildOf.last_reduces
    {α : Type} {R : ARS α} {a : α}
    {p q : {p : List α // p ∈ R.ReductionTree a}}
    (hq : ARS.IsChildOf R a p q) :
    Reduces R (ARS.Label p)
      (q.val.getLast (by
        simpa [ARS.ReductionTree] using q.property.1)) := by
  rcases hq with ⟨c, hqc, hred⟩
  simpa [hqc] using hred


lemma ARS.IsChildOf.eq_of_last_eq
    {α : Type} {R : ARS α} {a : α}
    {p q₁ q₂ : {p : List α // p ∈ R.ReductionTree a}}
    (h1 : ARS.IsChildOf R a p q₁)
    (h2 : ARS.IsChildOf R a p q₂)
    (hlast :
      q₁.val.getLast (by
        simpa [ARS.ReductionTree] using q₁.property.1) =
      q₂.val.getLast (by
        simpa [ARS.ReductionTree] using q₂.property.1)) :
    q₁ = q₂ := by
  rcases h1 with ⟨c₁, hc₁, hred₁⟩
  rcases h2 with ⟨c₂, hc₂, hred₂⟩
  have hc : c₁ = c₂ := by
    simpa [hc₁, hc₂] using hlast
  subst c₂
  apply Subtype.ext
  simp [hc₁, hc₂]


lemma ARS.finite_children
    {α : Type} (R : ARS α)
    (h : ARS.finitelyBranching R)
    (a : α)
    (p : {p : List α // p ∈ R.ReductionTree a}) :
    Set.Finite {q | ARS.IsChildOf R a p q} := by
  let f :
      {q : {q : List α // q ∈ R.ReductionTree a} //
        ARS.IsChildOf R a p q} → α :=
    fun q =>
      q.1.val.getLast (by
        simpa [ARS.ReductionTree] using q.1.property.1)
  have hmap :
      Set.MapsTo f
        Set.univ
        {c : α | Reduces R (ARS.Label p) c} := by
    intro q hq
    exact ARS.IsChildOf.last_reduces q.property
  have hinj :
      Set.InjOn f
        Set.univ := by
    intro q₁ hq₁ q₂ hq₂ hEq
    apply Subtype.ext
    exact ARS.IsChildOf.eq_of_last_eq
      q₁.property q₂.property hEq
  have hfin :
      Set.Finite (Set.univ : Set {
        q : {q : List α // q ∈ R.ReductionTree a} //
          ARS.IsChildOf R a p q}) :=
    Set.Finite.of_injOn hmap hinj (h (ARS.Label p))
  have himage :
      (fun q : {q : {q : List α // q ∈ R.ReductionTree a} //
          ARS.IsChildOf R a p q} => (q : {q : List α // q ∈ R.ReductionTree a})) ''
        Set.univ =
      {q | ARS.IsChildOf R a p q} := by
    ext q
    constructor
    · rintro ⟨q', -, rfl⟩
      exact q'.property
    · intro hq
      exact ⟨⟨q, hq⟩, by simp, rfl⟩
  rw [← himage]
  exact hfin.image _


lemma infinite_reduction_prefix_mem
    {α : Type} {R : ARS α} {a : α}
    (f : Nat → α)
    (hf0 : f 0 = a)
    (hf : ∀ n, Reduces R (f n) (f (n + 1))) :
    ∀ n,
      (List.range (n + 1)).map f ∈ ARS.ReductionTree R a := by
  intro n
  induction n with
  | zero =>
      simp [ARS.ReductionTree, hf0, IsReductionPath]
  | succ n ih =>
      have hpath :
          IsReductionPath R ((List.range (n + 1)).map f) := by
        exact (ih.2.2)
      have hlast :
          ((List.range (n + 1)).map f).getLast
            hpath.ne_nill = f n := by
        simp [List.range_succ]
      have hstep :
          Reduces R
            (((List.range (n + 1)).map f).getLast hpath.ne_nill)
            (f (n + 1)) := by
        rw [hlast]
        exact hf n
      have hpath' :
          IsReductionPath R
            (((List.range (n + 1)).map f) ++ [f (n + 1)]) := by
        exact IsReductionPath.of_append_singleton hpath hstep
      have hmem :
          ((List.range (n + 1)).map f) ++ [f (n + 1)]
            ∈ ARS.ReductionTree R a := by
        refine ⟨?_, ?_, hpath'⟩
        · simp
        · rw [List.head?_append]
          simp [List.head?_map, List.head?_range, hf0]
      simpa [List.range_succ] using hmem

lemma infinite_reduction_prefix_length
    {α : Type}
    (f : Nat → α)
    (n : Nat) :
    ((List.range (n + 1)).map f).length = n + 1 := by
  simp

lemma infinite_reduction_prefix_injective
    {α : Type}
    (f : Nat → α) :
    Function.Injective
      (fun n => (List.range (n + 1)).map f) := by
  intro n m h
  have hlen := congrArg List.length h
  simp at hlen
  omega

lemma infinite_ReductionTree_of_infinite_reduction
    {α : Type} {R : ARS α} {a : α}
    (f : Nat → α)
    (hf0 : f 0 = a)
    (hf : ∀ n, Reduces R (f n) (f (n + 1))) :
    Set.Infinite (ARS.ReductionTree R a) := by
  let F : Nat → List α :=
    fun n => (List.range (n + 1)).map f
  have hF_inj : Function.Injective F := by
    intro n m hnm
    exact infinite_reduction_prefix_injective f hnm
  have hF_mem : ∀ n, F n ∈ ARS.ReductionTree R a := by
    intro n
    exact infinite_reduction_prefix_mem f hf0 hf n
  exact Set.infinite_of_injective_forall_mem hF_inj hF_mem

def ARS.Descendants
    {α : Type} (R : ARS α) (a : α)
    (p : {p : List α // p ∈ R.ReductionTree a}) :
    Set (List α) :=
  {q | q ∈ R.ReductionTree a ∧ List.IsPrefix p.val q}

def ARS.HasInfiniteDescendants
    {α : Type} (R : ARS α) (a : α)
    (p : {p : List α // p ∈ R.ReductionTree a}) : Prop :=
  Set.Infinite (ARS.Descendants R a p)

def ARS.root
    {α : Type} (R : ARS α) (a : α) :
    {p : List α // p ∈ R.ReductionTree a} :=
  ⟨[a], by
    simp [ARS.ReductionTree, IsReductionPath]⟩

lemma ARS.root_mem_ReductionTree
  {α : Type} (R : ARS α) (a : α) :
  (ARS.root R a).val ∈ ARS.ReductionTree R a := by
  simp [ARS.root, ARS.ReductionTree, IsReductionPath]

lemma infinite_descendants_root
    {α : Type} (R : ARS α) (a : α)
    (hinf : Set.Infinite (ARS.ReductionTree R a)) :
    Set.Infinite (ARS.Descendants R a (ARS.root R a)) := by
  have hEq :
      ARS.Descendants R a (ARS.root R a) =
        ARS.ReductionTree R a := by
    ext q
    constructor
    · intro hq
      exact hq.1
    · intro hq
      refine ⟨hq, ?_⟩
      have hhead : q.head? = some a := by
        simpa [ARS.ReductionTree] using hq.2.1
      cases q with
      | nil =>
          simp at hhead
      | cons x xs =>
          simp only [List.head?_cons] at hhead
          have hxa : x = a := by
            simpa using hhead
          subst x
          refine ⟨xs, ?_⟩
          simp [ARS.root]
  rw [hEq]
  exact hinf

lemma List.IsPrefix.exists_append_singleton_prefix
    {α : Type} {p q : List α}
    (hpq : p <+: q)
    (hne : p ≠ q) :
    ∃ c : α, p ++ [c] <+: q := by
  rcases hpq with ⟨t, rfl⟩
  cases t with
  | nil =>
      exfalso
      exact hne (by simp)
  | cons c t =>
      refine ⟨c, ?_⟩
      refine ⟨t, ?_⟩
      simp [List.append_assoc]


def ARS.IsPrefixOf
    {α : Type} {R : ARS α} {a : α}
    (p q : {p : List α // p ∈ R.ReductionTree a}) : Prop :=
  p.val <+: q.val

theorem StronglyNormalizing_if_finite_ReductionTree_all
    {α : Type} (R : ARS α)
    (hfin : ∀ a : α, Set.Finite (ARS.ReductionTree R a)) :
    StronglyNormalizing R := by
  rw [StronglyNormalizing]
  intro hInf
  rcases hInf with ⟨f, hf⟩
  have htree :
      Set.Infinite (ARS.ReductionTree R (f 0)) := by
    exact infinite_ReductionTree_of_infinite_reduction f rfl hf
  exact htree.not_finite (hfin (f 0))
