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

/-- Corolário 2.4.5: A união de duas relações confluentes e que comutam é confluente. -/
lemma Corollary_2_4_5 {α : Type} (R : ARS α) (R1 R2 : α → α → Prop)
    -- A redução original R atua como a união de R1 e R2
    (h_sub : ∀ a b, Reduces R a b → R1 a b ∨ R2 a b)
    -- Ambas as relações pertencem ao fecho de R
    (h_sup1 : ∀ a b, R1 a b → ReducesStar R a b)
    (h_sup2 : ∀ a b, R2 a b → ReducesStar R a b)
    -- As relações são confluentes (comutam consigo mesmas) e comutam entre si
    (h_conf1 : Commutes R1 R1)
    (h_conf2 : Commutes R2 R2)
    (h_comm : Commutes R1 R2) :
    IsConfluent R := by
  -- O Corolário 2.4.5 é um caso especial do Lema de Hindley-Rosen onde o conjunto
  -- de índices tem apenas dois elementos.
  -- Usaremos Bool (true / false) como nossa "chave" de índices.
  let R_i : Bool → α → α → Prop := fun b => match b with
    | true => R1
    | false => R2
  apply Hindley_Rosen R Bool R_i
  · -- h_sub: Mapeamos a disjunção lógica para a prova de existência (∃ i)
    intro a b hab
    rcases h_sub a b hab with h1 | h2
    · exact ⟨true, h1⟩
    · exact ⟨false, h2⟩
  · -- h_sup: A aplicação do limite superior divide-se naturalmente nos dois casos
    intro i a b
    match i with
    | true => exact h_sup1 a b
    | false => exact h_sup2 a b
  · -- h_commute: Verificamos a comutação para todos os pares cruzados (i, j)
    intro i j
    match i, j with
    | true, true =>
      -- R1 comuta com R1 (Confluência de R1)
      exact h_conf1
    | false, false =>
      -- R2 comuta com R2 (Confluência de R2)
      exact h_conf2
    | true, false =>
      -- R1 comuta com R2 (Hipótese de comutação)
      exact h_comm
    | false, true =>
      -- R2 comuta com R1 (Simetria da comutação)
      intro a b c h2 h1
      -- Invertemos a ordem das variáveis no diagrama para reaproveitar h_comm
      rcases h_comm a c b h1 h2 with ⟨d, hd2, hd1⟩
      exact ⟨d, hd1, hd2⟩

lemma ReducesEqual_to_ReducesStar {α : Type} (R : ARS α) {a b : α}
(h : Reduces R a b ∨ a = b) : ReducesStar R a b := by
  rcases h with h_red | rfl
  · -- Caso 1: 'a' reduz para 'b' em exatamente um passo.
    -- Aplicamos diretamente o seu lema pré-existente da aula1.lean
    exact Reduces.toReducesStar h_red
  · -- Caso 2: 'a' é igual a 'b' (zero passos).
    -- Expandimos o fecho para utilizar a relação de identidade.
    rw [ReducesStar, ARS.reflTransClosure]
    right -- Entramos no lado direito da união (ARS.id)
    rw [ARS.id]
    -- Provemos que o par (a, a) pertence ao conjunto universo
    exact ⟨a, Set.mem_univ a, rfl⟩

/-- Fatos:
    Toda relação subcomutativa consigo mesma é fortemente confluente
    Toda relação comutativa com si mesma é confluente
-/
lemma Subcommutes_to_StrongConfluence {α : Type} (R : ARS α)
(h_sub : Subcommutes (Reduces R) (Reduces R)) :
StronglyConfluent R := by
  intro a b c hab hac
  unfold Subcommutes at h_sub
  rcases h_sub a b c hab hac with ⟨d, hbd, hcd⟩
  exists d
  constructor
  · have hbd_star : ReducesStar R b d := ReducesEqual_to_ReducesStar R hbd
    exact hbd_star
  · have hcd_dc : Reduces R c d ∨ d = c := by
      cases hcd with
      | inl hcd => exact Or.inl hcd
      | inr h_eq => exact Or.inr h_eq.symm
    exact hcd_dc

lemma Commutes_to_Confluence {α : Type} (R : ARS α)
(h_comm : Commutes (Reduces R) (Reduces R)) :
IsConfluent R := by
  intro a b c hab hac
  unfold Commutes at h_comm
  have hab' : Relation.ReflTransGen (Reduces R) a b := ReducesStar_iff_ReducesStar'.mp hab
  have hac' : Relation.ReflTransGen (Reduces R) a c := ReducesStar_iff_ReducesStar'.mp hac
  rcases h_comm a b c hab' hac' with ⟨d, hbd, hcd⟩
  exists d
  constructor
  · exact ReducesStar_iff_ReducesStar'.mpr hbd
  · exact ReducesStar_iff_ReducesStar'.mpr hcd

def Refines {α : Type} (R1 R2 : α → α → Prop) : Prop :=
  ∀ a b, R1 a b → Relation.ReflTransGen R2 a b

def CompatibleRefinement {α : Type} (R1 R2 : α → α → Prop) : Prop :=
  Refines R1 R2 ∧ Refines R2 R1
