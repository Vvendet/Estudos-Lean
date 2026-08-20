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
  sorry
