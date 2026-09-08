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


/-- Definição 2.4.3: Subcomutação entre R_alpha e R_beta.
    Matematicamente: ←_α · →_β ⊆ →_β^= · ←_α^=
    Lê-se: Se 'a' diverge para 'b' (1 passo de α) e para 'c' (1 passo de β),
    então 'b' e 'c' convergem para um 'd', onde β dá 'N' passos e α dá no máximo '1' passo. -/
def Subcommutes {α : Type} (R_alpha R_beta : α → α → Prop) : Prop :=
  ∀ a b c, R_alpha a b → R_beta a c →
    ∃ d, (R_alpha b d ∨ b = d) ∧ (R_alpha c d ∨ c = d)

/-- Definição 2.4.3: Comutação entre R_alpha e R_beta.
    Matematicamente: ←_α^* · →_β^* ⊆ →_β^* · ←_α^*
    Lê-se: Se 'a' diverge para 'b' (N passos de α) e para 'c' (N passos de β),
    então eles convergem para um 'd' com N passos de ambos os lados. -/
def Commutes {α : Type} (R_alpha R_beta : α → α → Prop) : Prop :=
  ∀ a b c, Relation.ReflTransGen R_alpha a b → Relation.ReflTransGen R_beta a c →
    ∃ d, Relation.ReflTransGen R_beta b d ∧ Relation.ReflTransGen R_alpha c d

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
    Seja R um ARS. Se para todo α, β em I, ->_α comuta com ->β então IsConfluent R -/

lemma Hindley_Rosen {α : Type} (R : ARS α) (I : Type) (R_i : I → α → α → Prop)
    -- Ajustado de (∀ i) para (∃ i) para modelar corretamente a propriedade de união
    (h_sub : ∀ a b, Reduces R a b → ∃ i, R_i i a b)
    (h_sup : ∀ i a b, R_i i a b → ReducesStar R a b)
    (h_commute : ∀ i j, Commutes (R_i i) (R_i j)) :
    IsConfluent R := by
  let S : α → α → Prop := fun a b => ∃ i, Relation.ReflTransGen (R_i i) a b
  have h_diamond : DiamondProperty S := by
    intro a b c hab hac
    rcases hab with ⟨i, hab_i⟩
    rcases hac with ⟨j, hac_j⟩
    rcases h_commute i j a b c hab_i hac_j with ⟨d, hbd_j, hcd_i⟩
    exact ⟨d, ⟨j, hbd_j⟩, ⟨i, hcd_i⟩⟩
  have h_S_sub : ∀ a b, Reduces R a b → S a b := by
    intro a b hab
    rcases h_sub a b hab with ⟨i, hab_i⟩
    exact ⟨i, Relation.ReflTransGen.single hab_i⟩
  have h_S_sup : ∀ a b, S a b → ReducesStar R a b := by
    intro a b hab
    rcases hab with ⟨i, hab_i⟩
    apply ReducesStar_iff_ReducesStar'.mpr
    induction hab_i with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ h_step ih =>
      have h_step_star := ReducesStar_iff_ReducesStar'.mp (h_sup i _ _ h_step)
      exact Relation.ReflTransGen.trans ih h_step_star
  exact IsConfluent_if_DiamondStar R S h_diamond h_S_sub h_S_sup
