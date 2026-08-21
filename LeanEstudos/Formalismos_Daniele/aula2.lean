import LeanEstudos.Formalismos_Daniele.aula1
import Init.WF
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
