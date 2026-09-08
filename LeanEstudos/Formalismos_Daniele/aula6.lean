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

lemma IsConfluent_if_DiamondStar {α : Type} (R : ARS α) (S : α → α → Prop)
    (h_diamond : DiamondProperty S)
    (h_sub : ∀ a b, Reduces R a b → S a b)
    (h_sup : ∀ a b, S a b → ReducesStar R a b) :
    IsConfluent R := by
  rw [Confluence_iff_DiamondStar]
  have h_equiv : ∀ a b, ReducesStar R a b ↔ Relation.ReflTransGen S a b := by
    intro a b
    constructor
    · intro h
      have h_rtg := ReducesStar_iff_ReducesStar'.mp h
      clear h
      induction h_rtg with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ h_step ih => exact Relation.ReflTransGen.tail ih (h_sub _ _ h_step)
    · intro h
      apply ReducesStar_iff_ReducesStar'.mpr
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ h_step ih =>
        have h_bc_rtg := ReducesStar_iff_ReducesStar'.mp (h_sup _ _ h_step)
        exact Relation.ReflTransGen.trans ih h_bc_rtg
  have h_strip : ∀ x y, Relation.ReflTransGen S x y → ∀ z, S x z →
      ∃ w, S y w ∧ Relation.ReflTransGen S z w := by
    intro x y hxy
    induction hxy with
    | refl =>
      intro z hxz
      exact ⟨z, hxz, Relation.ReflTransGen.refl⟩
    | tail _ h_step ih =>
      intro z hxz
      rcases ih z hxz with ⟨w1, hw1_b1, hw1_z⟩
      rcases h_diamond _ _ _ hw1_b1 h_step with ⟨w2, hw2_w1, hw2_b2⟩
      exact ⟨w2, hw2_b2, Relation.ReflTransGen.tail hw1_z hw2_w1⟩
  have h_S_diam : ∀ x y, Relation.ReflTransGen S x y → ∀ z, Relation.ReflTransGen S x z →
      ∃ w, Relation.ReflTransGen S y w ∧ Relation.ReflTransGen S z w := by
    intro x y hxy
    induction hxy with
    | refl =>
      intro z hxz
      exact ⟨z, hxz, Relation.ReflTransGen.refl⟩
    | tail _ h_step ih =>
      intro z hxz
      rcases ih z hxz with ⟨w1, hw1_b1, hw1_z⟩
      rcases h_strip _ _ hw1_b1 _ h_step with ⟨w2, hw2_w1, hw2_b2⟩
      exact ⟨w2, hw2_b2, Relation.ReflTransGen.tail hw1_z hw2_w1⟩
  intro a b c hab hac
  simp_rw [h_equiv] at hab hac ⊢
  exact h_S_diam a b hab c hac

/-- lema de Hindley-Rosen
    Seja R um ARS. Se para todo α, β em I -/
