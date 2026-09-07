import LeanEstudos.Formalismos_Daniele.aula5
import Mathlib.Logic.Relation

/-- Definição 2.4.1: Propriedade do Diamante -/
def DiamondProperty {α : Type} (R : α → α → Prop) : Prop :=
  ∀ a b c, R a b → R a c → ∃ d, R b d ∧ R c d

lemma Diamond_to_StrongConfluence {α : Type} (R : ARS α)
(h : DiamondProperty (Reduces R)) : StronglyConfluent R := by
  intro a b c hab hac
  rcases h a b c hab hac with ⟨d, hbd, hcd⟩
  exists d
  constructor
  · exact Reduces.toReducesStar hbd
  left
  exact hcd

lemma Confluence_iff_DiamondStar {α : Type} (R : ARS α) :
IsConfluent R ↔ DiamondProperty (ReducesStar R) := by
  constructor
  · intro h a b c hab hac
    unfold IsConfluent at h
    have h1 := h a b c hab hac
    rcases h1 with ⟨d, hbd, hcd⟩
    exists d
  · intro h a b c hab hac
    unfold DiamondProperty at h
    have h1 := h a b c hab hac
    rcases h1 with ⟨d, hbd, hcd⟩
    exists d

lemma reflTransGen_mono {α : Type} {R S : α → α → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ a b, Relation.ReflTransGen R a b → Relation.ReflTransGen S a b := by
  intro a b h_gen
  induction h_gen with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h_step ih => exact Relation.ReflTransGen.tail ih (h _ _ h_step)


def Subcommutes {α : Type} (R_alpha R_beta : α → α → Prop) : Prop :=
  ∀ a b, (Relation.Comp (Relation.ReflTransGen R_alpha) (Relation.ReflTransGen R_beta)) a b →
         (Relation.Comp (Relation.ReflTransGen R_beta) (Relation.ReflTransGen R_alpha)) a b

def Commutes {α : Type} (R_alpha R_beta : α → α → Prop) : Prop :=
  ∀ a b, (Relation.Comp (Relation.ReflTransGen R_alpha) (Relation.ReflTransGen R_beta)) a b →
         (Relation.Comp (Relation.ReflTransGen R_beta) (Relation.ReflTransGen R_alpha)) a b
