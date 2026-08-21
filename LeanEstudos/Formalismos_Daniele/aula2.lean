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

def ReductionTree {α : Type} (R : ARS α) (x : α) : Set α :=
  { y | ReducesStar R x y }

def ReductionTree' {α : Type} (R : ARS α) (x : α) : Set α :=
  { y | (x, y) ∈ ARS.reflTransClosure R }

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

lemma ReductionTree_eq_StronglyNormalizing_if_finitelyBranching
{α : Type} (R : ARS α) (h : ARS.finitelyBranching R) (a : α) :
Set.Finite (ReductionTree R a) ↔ StronglyNormalizing R := by sorry
