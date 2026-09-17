import LeanEstudos.Formalismos_Daniele.aula8
import Mathlib.Data.Multiset.Basic
import Mathlib.Order.WellFounded

-- ---------------------------------------------------------
-- Proposição 2.5.6 (Ciclo Completo)
-- ---------------------------------------------------------

/-- Coerência Módulo ~ (COH~): ~ · →* ⊆ ↓~ -/
def CoherentModulo {α : Type} (R : ARS_Mod α) : Prop :=
  ∀ a b c, sim R a b → ReducesStar R.toARS b c → IsJoinableModulo R a c

/-- Coerência Forte Módulo ~ (SCOH~): ~ · →* · ~ ⊆ ↓~ -/
def StronglyCoherentModulo {α : Type} (R : ARS_Mod α) : Prop :=
  ∀ a b c d, sim R a b → ReducesStar R.toARS b c → sim R c d → IsJoinableModulo R a d

/-- Lema auxiliar: A equivalência 'sim' é simétrica. -/
lemma sim_symm {α : Type} (R : ARS_Mod α) {x y : α} (h : sim R x y) : sim R y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hxy hstep ih =>
    have hvu : sim R _ _ := Relation.ReflTransGen.single (R.H_symm hstep)
    exact Relation.ReflTransGen.trans hvu ih

/-- Proposição 2.5.6 (Parte 2.1): Diamond(→* · ~) ⇒ CON~
    A confluência é o diamante onde as equivalências da ponta são nulas. -/
lemma DiamondPropertyStarModulo_to_ConfluenceModulo {α : Type} (R : ARS_Mod α)
    (h : DiamondPropertyStarModulo R) : ConfluenceModulo R := by
  intro a b c hab hac
  have hbb : sim R b b := Relation.ReflTransGen.refl
  have hcc : sim R c c := Relation.ReflTransGen.refl
  exact h a b c b c hab hbb hac hcc

/-- Proposição 2.5.6 (Parte 2.2): Diamond(→* · ~) ⇒ SCOH~
    A coerência forte é o diamante onde o lado esquerdo não reduz (b →* b). -/
lemma DiamondPropertyStarModulo_to_StronglyCoherentModulo {α : Type} (R : ARS_Mod α)
    (h : DiamondPropertyStarModulo R) : StronglyCoherentModulo R := by
  intro a b c d hab hbc hcd
  -- Reorganizamos a hipótese a ~ b →* c ~ d para a base do Diamante
  have hbb : ReducesStar R.toARS b b := ReducesStar_iff_ReducesStar'.mpr Relation.ReflTransGen.refl
  have hba : sim R b a := sim_symm R hab
  -- Instanciamos o Diamante partindo de 'b'
  exact h b a d b c hbb hba hbc hcd

/-- Proposição 2.5.6 (Parte 3): CON~ + SCOH~ ⇒ CR~ -/
lemma CON_and_SCOH_to_CR {α : Type} (R : ARS_Mod α)
    (hCON : ConfluenceModulo R)
    (hSCOH : StronglyCoherentModulo R) : ChurchRosserModulo R := by
  intro a b hab
  -- Fazemos indução na cadeia Reflexiva-Transitiva da Conversão (a ≈ b)[cite: 1]
  induction hab with
  | refl =>
    -- Caso base: 0 passos. a e a são juntáveis.
    exists a, a
    constructor
    · exact ReducesStar_iff_ReducesStar'.mpr Relation.ReflTransGen.refl
    · constructor
      · exact Relation.ReflTransGen.refl
      · exact ReducesStar_iff_ReducesStar'.mpr Relation.ReflTransGen.refl
  | @tail a1 b1 h_prefix h_step ih =>
    -- Hipótese indutiva: 'a' e 'a1' são juntáveis (a →* c ~ d *← a1)[cite: 1]
    rcases ih with ⟨c, d, hac, hcd, ha1d⟩
    -- Analisamos o passo individual a1 ↔ b1
    rcases h_step with h_red | h_inv | h_sim
    · -- Caso (ii) do livro: a1 → b1[cite: 1]
      have ha1b1 : ReducesStar R.toARS a1 b1 := Reduces.toReducesStar h_red
      -- Aplicamos CON~ em a1 →* d e a1 →* b1
      rcases hCON a1 d b1 ha1d ha1b1 with ⟨e, f, hde, hef, hb1f⟩
      -- Aplicamos SCOH~ em c ~ d →* e ~ f
      rcases hSCOH c d e f hcd hde hef with ⟨g, h, hcg, hgh, hfh⟩
      exists g, h
      constructor
      · exact ReducesStar.trans hac hcg
      · constructor
        · exact hgh
        · exact ReducesStar.trans hb1f hfh
    · -- Caso (iii) do livro: b1 → a1[cite: 1]
      have hb1a1 : ReducesStar R.toARS b1 a1 := Reduces.toReducesStar h_inv
      -- Colapsamos a redução: b1 → a1 →* d
      have hb1d : ReducesStar R.toARS b1 d := ReducesStar.trans hb1a1 ha1d
      exists c, d
    · -- Caso (i) do livro: a1 ~ b1[cite: 1]
      have hb1a1 : sim R b1 a1 := sim_symm R h_sim
      have hdc : sim R d c := sim_symm R hcd
      -- Aplicamos SCOH~ em b1 ~ a1 →* d ~ c
      rcases hSCOH b1 a1 d c hb1a1 ha1d hdc with ⟨e, f, hb1e, hef, hcf⟩
      -- O resultado é b1 →* e ~ f *← c. Reorganizamos para a junção final.
      exists f, e
      constructor
      · exact ReducesStar.trans hac hcf
      · constructor
        · exact sim_symm R hef
        · exact hb1e
-- ---------------------------------------------------------
-- Lemas Auxiliares para o Lema 2.5.7
-- ---------------------------------------------------------

/-- Lema auxiliar 1: Se 'x' é forma normal e x →* y, então x = y. -/
lemma IsNormal_ReducesStar_eq {α : Type} (R : ARS_Mod α) (x y : α)
    (hnorm : IsNormal R.toARS x) (hxy : ReducesStar R.toARS x y) : x = y := by
  have hxy_rtg := ReducesStar_iff_ReducesStar'.mp hxy
  have cases_head := Relation.ReflTransGen.cases_head hxy_rtg
  rcases cases_head with (rfl | ⟨z, hxz, hzy⟩)
  · rfl
    exfalso
    exact hnorm z hxz

-- ---------------------------------------------------------
-- Lema 2.5.7
-- ---------------------------------------------------------



lemma WeaklyNormalizing_and_CoherentModulo_to_StronglyCoherentModulo {α : Type} (R : ARS_Mod α)
    (hWN : WeaklyNormalizing R.toARS)
    (hCOH : CoherentModulo R) : StronglyCoherentModulo R := by
  intro a b c d hab hbc hcd
  rcases hWN c with ⟨c', hcc', hnorm_c'⟩
  have hbc' : ReducesStar R.toARS b c' := ReducesStar.trans hbc hcc'
  rcases hCOH a b c' hab hbc' with ⟨e, v1, hae, hev1, hc'v1⟩
  have heq1 : c' = v1 := IsNormal_ReducesStar_eq R c' v1 hnorm_c' hc'v1
  rw [← heq1] at hev1
  have hdc : sim R d c := sim_symm R hcd
  rcases hCOH d c c' hdc hcc' with ⟨f, v2, hdf, hfv2, hc'v2⟩
  have heq2 : c' = v2 := IsNormal_ReducesStar_eq R c' v2 hnorm_c' hc'v2
  rw [← heq2] at hfv2
  have hc'f : sim R c' f := sim_symm R hfv2
  have hef : sim R e f := Relation.ReflTransGen.trans hev1 hc'f
  exists e, f

/-- Lema 2.5.7 (Parte 2): WN + CON~ + COH~ ⇒ CR~ -/
lemma WeaklyNormalizing_ConfluenceModulo_CoherentModulo_to_ChurchRosserModulo
 {α : Type} (R : ARS_Mod α)
    (hWN : WeaklyNormalizing R.toARS)
    (hCON : ConfluenceModulo R)
    (hCOH : CoherentModulo R) : ChurchRosserModulo R := by
  -- Conforme o livro: Por (1), o sistema é SCOH~
  have hSCOH : StronglyCoherentModulo R :=
  WeaklyNormalizing_and_CoherentModulo_to_StronglyCoherentModulo R hWN hCOH
  -- Conforme o livro: Assim, ele é CR~ pela Proposição 2.5.6
  exact CON_and_SCOH_to_CR R hCON hSCOH

/-- Lema 2.5.7 (Parte 3): WN + ACR~ ⇒ CR~ -/
lemma Lemma_2_5_7_Part3 {α : Type} (R : ARS_Mod α)
    (hWN : WeaklyNormalizing R.toARS)
    (hACR : AlmostChurchRosserModulo R) : ChurchRosserModulo R := by
  -- Conforme o livro: Consequência direta de (2), pois ACR~ implica CON~ e COH~[cite: 1].
  have hCON : ConfluenceModulo R := AlmostChurchRosserModulo_to_ConfluenceModulo R hACR
  have hCOH : CoherentModulo R := by
    intro a b c hab hbc
    -- COH~ é apenas o caso do ACR~ onde a redução à esquerda é reflexiva (0 passos)
    have haa : ReducesStar R.toARS a a :=
    ReducesStar_iff_ReducesStar'.mpr Relation.ReflTransGen.refl
    exact hACR a a b c haa hab hbc
  exact WeaklyNormalizing_ConfluenceModulo_CoherentModulo_to_ChurchRosserModulo R hWN hCON hCOH

-- ---------------------------------------------------------
-- Definição 2.5.9: Comutação Módulo ~
-- ---------------------------------------------------------

/-- Uma relação de redução qualquer operando módulo ~ (→~ = ~ · → · ~) -/
def ReducesModuloRel {α : Type} (R : ARS_Mod α) (r : α → α → Prop) (a b : α) : Prop :=
  ∃ x y, sim R a x ∧ r x y ∧ sim R y b

/-- Subcomutação Módulo ~ -/
def SubcommutesModulo {α : Type} (R : ARS_Mod α) (ra rb : α → α → Prop) : Prop :=
  ∀ a b c, ra a b → rb a c →
    ∃ d e, rb b d ∧ sim R d e ∧ Relation.ReflTransGen ra c e

  /-- Comutação Módulo ~ -/
  def CommutesModulo {α : Type} (R : ARS_Mod α) (ra rb : α → α → Prop) : Prop :=
    SubcommutesModulo R (ReducesModuloRel R ra) (ReducesModuloRel R rb) ∧
    SubcommutesModulo R (ReducesModuloRel R rb) (ReducesModuloRel R ra)

-- ---------------------------------------------------------
-- Transição para Sistemas de Redução Rotulados (Labeled ARS)
-- ---------------------------------------------------------

/-- Sistema Abstrato de Redução Rotulado operando módulo uma equivalência H.
    A ordem sobre os rótulos (I) deve ser bem-fundada para podermos
    usar a medida lexicográfica. -/
structure LabeledARS_Mod (α : Type) (I : Type) where
  reduces : I → α → α → Prop
  H : α → α → Prop
  H_symm : Symmetric H
  label_order : I → I → Prop
  label_wf : WellFounded label_order
  -- Instâncias de decidibilidade necessárias para os if-then-else da sua aula4
  label_dec : DecidableRel label_order
  label_eq  : DecidableEq I

/-- O fecho de equivalência ~ para o sistema rotulado. -/
def LabeledARS_Mod.sim {α I : Type} (R : LabeledARS_Mod α I) : α → α → Prop :=
  Relation.ReflTransGen R.H

-- ---------------------------------------------------------
-- Definição 2.5.8: Conjunto Inferior (Down Set) e Medida Lexicográfica
-- ---------------------------------------------------------

variable {I : Type} (order : I → I → Prop) [DecidableRel order] [DecidableEq I]

/-- 1. O Down Set (Υ_a) de um rótulo 'a'[cite: 2].
    Conforme a sua aula4, representamos conjuntos puros como multiconjuntos
    que retornam infinito (⊤) se o elemento pertencer, e 0 caso contrário[cite: 1, 2]. -/
def downSet (a : I) : GMultiset I :=
  fun x => if order x a then ⊤ else 0

/-- 2. A Medida Máxima Lexicográfica (|| · ||) para strings (List I)[cite: 2].
    Processamos a lista da esquerda para a direita (foldl).
    Caso base: || ε || = ∅
    Passo: || α a || = [a] ⊕ (|| α || \ Υ_a)[cite: 2]. -/
def lexMaxMeasure (labels : List I) : GMultiset I :=
  labels.foldl (fun acc a =>
    -- [a] ⊕ (acc \ Υ_a)
    GMultiset.sum (GMultiset.finite_singleton a) (GMultiset.diff acc (downSet order a))
  ) GMultiset.empty

-- ---------------------------------------------------------
-- Preparação: Relações Restritas e Coerção
-- ---------------------------------------------------------

/-- Redução restrita a um subconjunto de rótulos (→_v ou →_h)[cite: 1] -/
def reduces_set {α I : Type} (R : LabeledARS_Mod α I) (S : Set I) (x y : α) : Prop :=
  ∃ i ∈ S, R.reduces i x y

/-- Projeta um sistema rotulado de volta para um ARS_Mod global,
    unindo as reduções de todos os rótulos possíveis. -/
def LabeledARS_Mod.toARS_Mod {α I : Type} (R : LabeledARS_Mod α I) : ARS_Mod α where
  red := { p | ∃ i, R.reduces i p.1 p.2 }
  H := R.H
  H_symm := R.H_symm

/-- Redução ao longo de uma cadeia (lista) de rótulos (→_σ ou →_τ). -/
def reduces_seq {α I : Type} (R : LabeledARS_Mod α I) : List I → α → α → Prop
  | [], a, b => a = b
  | (i :: is), a, b => ∃ c, R.reduces i a c ∧ reduces_seq R is c b

/-- Predicado que encapsula a validade dos diagramas da Figura 2.11
    sob a restrição de medida lexicográfica ||β|| ⪰_mul ||τ||. -/
def LocalDecreasingDiagramsHold {α I : Type} (R : LabeledARS_Mod α I) (Iv Ih : Set I)
    [DecidableRel R.label_order] [DecidableEq I] : Prop :=
  -- Para todo a <-_α b ->_β c, com α ∈ Iv e β ∈ Ih[cite: 2]
  ∀ a b c (α_lbl β_lbl : I),
    α_lbl ∈ Iv → β_lbl ∈ Ih →
    R.reduces α_lbl b a → R.reduces β_lbl b c →
    -- Devem existir cadeias σ, τ, σ', τ' pertencentes aos respectivos conjuntos[cite: 2]
    ∃ (σ τ σ' τ' : List I) (d1  e1  d e : α),
      (∀ x ∈ σ, x ∈ Iv) ∧ (∀ x ∈ τ, x ∈ Ih) ∧
      (∀ x ∈ σ', x ∈ Iv) ∧ (∀ x ∈ τ', x ∈ Ih) ∧
      -- E a convergência estrutural do diagrama (i) da Figura 2.11[cite: 2]
      -- Caminho esquerdo: a →_σ d1 →_τ' d
      reduces_seq R σ a d1 ∧ reduces_seq R τ' d1 d ∧
      -- Caminho direito: c →_τ e1 →_σ' e
      reduces_seq R τ c e1 ∧ reduces_seq R σ' e1 e ∧
      -- Fechamento módulo ~ nas pontas do diagrama[cite: 2]
      R.sim d e ∧
      -- Restrição de medida: ||β|| ⪰_mul ||τ|| (usando MultisetExtension da aula 4)[cite: 2, 4]
      (MultisetExtension R.label_order (lexMaxMeasure R.label_order [β_lbl])
      (lexMaxMeasure R.label_order τ) ∨
       lexMaxMeasure R.label_order [β_lbl] = lexMaxMeasure R.label_order τ)

open scoped Classical in
/-- A ordem lexicográfica >_lex descrita na prova do Teorema 2.5.10.
    Compara (||τ||, |σ|) com (||τ'||, |σ'|):
    Primeiro usa a extensão de multiconjunto sobre os rótulos horizontais.
    Se forem iguais, usa a ordem natural (<) sobre o comprimento das cadeias verticais. -/
def lex_order {α I : Type} (R : LabeledARS_Mod α I) [DecidableRel R.label_order] :
    (GMultiset I × Nat) → (GMultiset I × Nat) → Prop :=
  Lexicographic_Order (MultisetExtension R.label_order) (fun a b => a < b)


open scoped Classical in
noncomputable def FiniteMultiset_to_Mathlib {α : Type}
    (M : FiniteMultiset α) : Multiset α :=
  let supp : Finset α := M.property.2.toFinset
  supp.sum (fun a => Multiset.replicate (M.val a).toNat a)


open scoped Classical in
/-- Lema que garante que a conversão preserva a multiplicidade de cada elemento -/
lemma count_toMathlib {α : Type} [DecidableEq α] (M : FiniteMultiset α) (a : α) :
    Multiset.count a (FiniteMultiset_to_Mathlib M) = (M.val a).toNat := by
  unfold FiniteMultiset_to_Mathlib
  have h_hom : Multiset.count a = ⇑(Multiset.countAddMonoidHom a) := rfl
  rw [h_hom, map_sum, ← h_hom]
  simp only [Multiset.count_replicate]
  by_cases h : a ∈ M.property.2.toFinset
  · rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb_neq
      -- Transição direta via análise de casos do 'if'
      split_ifs with heq
      · exact False.elim (hb_neq heq)
      · rfl
    · intro h_not_in
      contradiction
  have h_zero_left : (M.property.2.toFinset.sum fun x =>
   if x = a then (M.val x).toNat else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        split_ifs with heq
        · -- Se x = a, substituímos x por a em hx, o que contradiz a hipótese h principal
          subst heq
          contradiction
        · rfl
  rw [h_zero_left]
  symm
  have h_not_pos : ¬ (M.val a > 0) := by
    intro h_pos
    apply h
    -- Volta do domínio de Finset iterável para a definição abstrata do seu Set.Finite
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact h_pos
  have h_zero : M.val a = 0 := le_antisymm (not_lt.mp h_not_pos) (zero_le _)
  rw [h_zero]
  rfl

/-- Extensão de passo único: o conjunto removido X tem exatamente um elemento 'a' -/
def SingleStepMultisetExtension {α : Type} [DecidableEq α]
(R : α → α → Prop) (M1 M2 : FiniteMultiset α) : Prop :=
  ∃ X_val Y_val : GMultiset α,
    IsFiniteMultiset X_val ∧
    IsFiniteMultiset Y_val ∧
    (∃ a, X_val = GMultiset.finite_singleton a) ∧
    X_val ⊆ M1.val ∧
    M2.val = GMultiset.sum (GMultiset.diff M1.val X_val) Y_val ∧
    ∀ y ∈ Y_val, ∃ x ∈ X_val, R y x  -- ← INVERTIDO AQUI PARA AGRADAR A MATHLIB

lemma SingleStepMultisetExtension_to_CutExpand {α : Type} [DecidableEq α] (R : α → α → Prop)
    (M1 M2 : FiniteMultiset α)
    (h_ext : SingleStepMultisetExtension R M1 M2) :
    Relation.CutExpand R (FiniteMultiset_to_Mathlib M2) (FiniteMultiset_to_Mathlib M1) := by
  unfold SingleStepMultisetExtension at h_ext
  rcases h_ext with ⟨X_val, Y_val, hX_fin, hY_fin, ⟨a, hX_eq⟩, hX_sub_M1, hM2_eq, h_red⟩
  let X : FiniteMultiset α := ⟨X_val, hX_fin⟩
  let Y : FiniteMultiset α := ⟨Y_val, hY_fin⟩
  let X_mathlib := FiniteMultiset_to_Mathlib X
  let Y_mathlib := FiniteMultiset_to_Mathlib Y
  use Y_mathlib, a
  constructor
  · -- SUBMETA 1: Redução Relacional
    intro y hy
    have hy_count : Multiset.count y Y_mathlib > 0 := Multiset.count_pos.mpr hy
    rw [count_toMathlib Y] at hy_count
    have hy_mem : y ∈ Y_val := by
      change Y_val y > 0
      have fin_Y := Y.property.1 y
      change Y_val y ≠ ⊤ at fin_Y
      cases eqY : Y_val y with
      | top => exact False.elim (fin_Y eqY)
      | coe nY =>
        have hY : Y.val y = Y_val y := rfl
        rw [hY] at hy_count
        rw [eqY] at hy_count
        revert hy_count
        simp
    rcases h_red y hy_mem with ⟨x, hx_mem, hRyx⟩
    have hx_eq_a : x = a := by
      change X_val x > 0 at hx_mem
      rw [hX_eq] at hx_mem
      change (if x = a then (1 : ENat) else 0) > 0 at hx_mem
      split_ifs at hx_mem with heq
      · exact heq
      · contradiction
    subst hx_eq_a
    exact hRyx
  · -- SUBMETA 2: Equivalência Algébrica
    apply Multiset.ext.mpr
    intro k
    rw [Multiset.count_add, Multiset.count_add]
    have ha_is_X : Multiset.count k {a} = (X.val k).toNat := by
      change Multiset.count k {a} = (X_val k).toNat
      rw [hX_eq]
      change Multiset.count k {a} = (if k = a then (1:ENat) else 0).toNat
      by_cases hk : k = a
      · subst hk
        simp
      · have h0 : Multiset.count k {a} = 0 := Multiset.count_eq_zero.mpr (by simp [hk])
        rw [h0]
        simp [hk]
    rw [ha_is_X]
    rw [count_toMathlib M2, count_toMathlib M1, count_toMathlib Y]
    change (M2.val k).toNat + (X.val k).toNat = (M1.val k).toNat + (Y.val k).toNat
    have h_eval := congrFun hM2_eq k
    unfold GMultiset.sum GMultiset.diff at h_eval
    have fin_M1 := M1.property.1 k
    have fin_M2 := M2.property.1 k
    have fin_X := X.property.1 k
    have fin_Y := Y.property.1 k
    cases eq1 : M1.val k with
    | top => exact False.elim (fin_M1 eq1)
    | coe n1 =>
      cases eq2 : M2.val k with
      | top => exact False.elim (fin_M2 eq2)
      | coe n2 =>
        cases eqX : X.val k with
        | top => exact False.elim (fin_X eqX)
        | coe nX =>
          cases eqY : Y.val k with
          | top => exact False.elim (fin_Y eqY)
          | coe nY =>
            change M2.val k = M1.val k - X.val k + Y.val k at h_eval
            rw [eq1, eq2, eqX, eqY] at h_eval
            change (↑n2 : ENat) = ↑(n1 - nX + nY) at h_eval
            have h_final : n2 = n1 - nX + nY := congrArg ENat.toNat h_eval
            have hX_le_M1 : nX ≤ n1 := by
              have h_sub := hX_sub_M1 k
              change X_val k ≤ M1.val k at h_sub
              have hX_def : X_val k = X.val k := rfl
              rw [hX_def, eqX, eq1] at h_sub
              exact ENat.coe_le_coe.mp h_sub
            change n2 + nX = n1 + nY
            omega

-- Lema Auxiliar 1: Se um multiconjunto não é vazio, sua cardinalidade na Mathlib é > 0
lemma Multiset_card_pos_of_not_empty {α : Type} [DecidableEq α] (X : FiniteMultiset α)
    (h_nempty : X.val ≠ ∅) : Multiset.card (FiniteMultiset_to_Mathlib X) > 0 := by
  sorry

-- Lema Auxiliar 2: Se a cardinalidade de X é 1, a extensão geral colapsa para a extensão de passo único
lemma SingleStep_of_Card_One {α : Type} [DecidableEq α] (R : α → α → Prop)
    (M1 M2 X Y : FiniteMultiset α)
    (h_card : Multiset.card (FiniteMultiset_to_Mathlib X) = 1)
    (h_ext : FiniteMultisetExtension R M1 M2) :
    SingleStepMultisetExtension R M1 M2 := by
  sorry


lemma FiniteMultisetExtension_implies_TransGen {α : Type} [DecidableEq α] (R : α → α → Prop)
    (M1 M2 : FiniteMultiset α)
    (h_ext : FiniteMultisetExtension R M1 M2) :
    Relation.TransGen (Relation.CutExpand R) (FiniteMultiset_to_Mathlib M2) (FiniteMultiset_to_Mathlib M1) := by

  -- 1. Desdobramos a extensão original para extrair o multiconjunto X removido
  unfold FiniteMultisetExtension at h_ext
  unfold MultisetExtension at h_ext
  rcases h_ext with ⟨X_val, Y_val, hX_fin, hY_fin, hX_nempty, hX_sub_M1, hM2_eq, h_red⟩

  -- 2. A estratégia matemática exigirá indução sobre o tamanho (cardinalidade) de X_val.
  --    Como hX_nempty garante que X_val ≠ ∅, sabemos que o tamanho de X_val é ≥ 1.

  -- BASE DA INDUÇÃO (|X| = 1):
  -- Se X_val for um singleton ({a}), a sua extensão de múltiplos passos colapsa
  -- exatamente na 'SingleStepMultisetExtension'.
  -- Invocamos o lema que acabamos de provar e aplicamos 'Relation.TransGen.single'.

  -- PASSO INDUTIVO (|X| = n + 1):
  -- Se X_val = {a} + X_resto, nós particionamos a operação em dois passos:
  -- Passo A: Removemos 'a' e inserimos os elementos de Y_val relacionados a ele.
  -- Passo B: Invocamos a hipótese indutiva para o X_resto.
  -- Juntamos os passos usando 'Relation.TransGen.head' ou 'Relation.TransGen.tail'.

  sorry

open scoped Classical in
/-- Lema auxiliar: >_lex é bem-fundada. -/
lemma lex_order_wf {α I : Type} (R : LabeledARS_Mod α I) [DecidableRel R.label_order] :
    WellFounded (lex_order R) := by
  -- A aula4 formalizou a direção (<=) do Teorema 2.3.12[cite: 1].
  -- Assumimos a direção (=>) aqui temporariamente para avançarmos com a teoria.
  have hwf_mul : WellFounded (MultisetExtension R.label_order) := sorry

  -- A ordem natural (<) nos naturais não possui cadeias decrescentes infinitas.
  have hwf_nat : WellFounded (fun (a b : Nat) => a < b) := Nat.lt_wfRel.wf

  -- O produto lexicográfico preserva a boa-fundação (aula3_anexo)[cite: 3].
  exact Lexicographic_Order_WellFounded hwf_mul hwf_nat


/-- Diagrama (i) da Figura 2.11:
    Interação entre ra (vertical) e rb (horizontal).
    Se 'a' diverge por ra para 'b' e por rb para 'c',
    eles convergem com rb* a partir de 'b', ra* a partir de 'c', módulo ~. -/
def Diagram_2_11_i {α : Type} (R : ARS_Mod α) (ra rb : α → α → Prop) : Prop :=
  ∀ a b c, ra a b → rb a c →
    ∃ d e, Relation.ReflTransGen rb b d ∧ sim R d e ∧ Relation.ReflTransGen ra c e

/-- Diagrama (ii) da Figura 2.11:
    Interação entre ra (vertical) e a equivalência ~.
    Se 'a' diverge por ra para 'b' e por ~ para 'c',
    'b' e 'c' convergem com ~ a partir de 'b', e ra* a partir de 'c'. -/
def Diagram_2_11_ii {α : Type} (R : ARS_Mod α) (ra : α → α → Prop) : Prop :=
  ∀ a b c, ra a b → sim R a c →
    ∃ d, sim R b d ∧ Relation.ReflTransGen ra c d

/-- Diagrama (iii) da Figura 2.11:
    Interação entre a equivalência ~ e rb (horizontal).
    Se 'a' diverge por ~ para 'b' e por rb para 'c',
    'b' e 'c' convergem com rb* a partir de 'b', e ~ a partir de 'd'. -/
def Diagram_2_11_iii {α : Type} (R : ARS_Mod α) (rb : α → α → Prop) : Prop :=
  ∀ a b c, sim R a b → rb a c →
    ∃ d, Relation.ReflTransGen rb b d ∧ sim R d c

/-- Estende o Diagrama (i) para uma cadeia reflexiva-transitiva de ra. -/
lemma lifting_diagram_i {α : Type} (R : ARS_Mod α) (ra rb : α → α → Prop)
    (h_equiv : Equivalence (sim R))
    (h_close_diagram : ∀ x y d1 e1 c, ra x y → Relation.ReflTransGen rb x d1 →
      sim R d1 e1 → Relation.ReflTransGen ra c e1 →
      ∃ d2 e2, Relation.ReflTransGen rb y d2 ∧ sim R d2 e2 ∧ Relation.ReflTransGen ra c e2) :
    ∀ a b c, Relation.ReflTransGen ra a b → rb a c →
      ∃ d e, Relation.ReflTransGen rb b d ∧ sim R d e ∧ Relation.ReflTransGen ra c e := by
  intro a b c h_rab
  -- Indução sobre a cadeia de passos verticais
  induction h_rab generalizing c with
  | refl =>
    intro h_rb_ac
    use c, c
    constructor
    · exact Relation.ReflTransGen.single h_rb_ac
    · constructor
      · -- Invocamos a reflexividade garantida pela equivalência
        exact h_equiv.refl c
      · exact Relation.ReflTransGen.refl
  | tail h_rax h_rxy ih =>
    intro h_rb_ac
    -- Aplicamos a hipótese indutiva para o trecho até o penúltimo vértice
    rcases ih c h_rb_ac with ⟨d1, e1, h_rb_x_d1, h_sim_d1_e1, h_ra_c_e1⟩
    -- Alimentamos a hipótese de fechamento. Os '_' deixam o Lean inferir
    -- os vértices exatos (b✝, c✝, etc.) a partir das provas!
    exact h_close_diagram _ _ _ _ _ h_rxy h_rb_x_d1 h_sim_d1_e1 h_ra_c_e1


/--
  Teorema 2.5.10 (Parte 1):
  Se as relações locais ra e rb satisfazem os três diagramas localmente
  decrescentes da Figura 2.11, então ra e rb comutam módulo a equivalência de R.
-/
theorem Theorem_2_5_10_Part1 {α : Type}
    (R : ARS_Mod α)
    (ra rb : α → α → Prop)
    (h_diag_i : Diagram_2_11_i R ra rb)
    (h_diag_ii : Diagram_2_11_ii R ra)
    (h_diag_iii : Diagram_2_11_iii R rb) :
    CommutesModulo R ra rb := by

  unfold CommutesModulo
  constructor

  · -- Submeta 1: ra subcomuta com rb módulo ~
    unfold SubcommutesModulo
    intro a b c h_ra_ab h_rb_ac

    -- Revelamos a anatomia do passo isolado envelopado por equivalências
    unfold ReducesModuloRel at h_ra_ab h_rb_ac

    -- Extraímos os pontos intermediários do passo vertical (ra): a ~ a1 →_v b1 ~ b
    rcases h_ra_ab with ⟨a1, b1, h_sim_a_a1, h_ra_a1_b1, h_sim_b1_b⟩

    -- Extraímos os pontos intermediários do passo horizontal (rb): a ~ a2 →_h c1 ~ c
    rcases h_rb_ac with ⟨a2, c1, h_sim_a_a2, h_rb_a2_c1, h_sim_c1_c⟩

    -- Agora temos a topologia completa exposta para conectarmos os diagramas!
    -- 1. Conectamos o platô superior: a1 ~ a e a ~ a2 implica a1 ~ a2
    have h_sim_a1_a : sim R a1 a := by
      -- Como ~ é gerada por H (que é simétrica), a relação inteira é simétrica
      sorry

    have h_sim_a1_a2 : sim R a1 a2 := by
      -- A transitividade do fecho reflexivo-transitivo (ReflTransGen.trans)
      sorry

    -- 2. Primeira Colagem: Aplicamos o Diagrama (ii)
    -- Temos: a1 →_ra b1 e a1 ~ a2
    -- O Diagrama (ii) nos garante um ponto 'w1' tal que b1 ~ w1 e a2 →_ra* w1
    have h_aplic_diag_ii := h_diag_ii a1 b1 a2 h_ra_a1_b1 h_sim_a1_a2
    rcases h_aplic_diag_ii with ⟨w1, h_sim_b1_w1, h_ra_a2_w1⟩

    -- O nosso estado topológico atualizado a partir de 'a2' agora é:
    -- a2 →_rb c1 (h_rb_a2_c1)   [1 passo horizontal]
    -- a2 →_ra* w1 (h_ra_a2_w1)  [N passos verticais]

    sorry

  · -- Submeta 2: rb subcomuta com ra módulo ~
    -- Meta: ∀ a b c, RedModulo(rb) a b → RedModulo(ra) a c → Convergem
    sorry

/-- Teorema 2.5.10 (Parte 2): Se as reduções verticais, horizontais e globais
    coincidem (→_A = →_v = →_h), o sistema inteiro é CR~[cite: 1]. -/
theorem Theorem_2_5_10_Part2 {α I : Type} (R : LabeledARS_Mod α I) (Iv Ih : Set I)
    [DecidableRel R.label_order] [DecidableEq I]
    (h_diagrams : LocalDecreasingDiagramsHold R Iv Ih)
    -- Hipóteses de igualdade relacional: →_A = →_v e →_A = →_h[cite: 1]
    (h_eq_v : ∀ x y, (x, y) ∈ R.toARS_Mod.red ↔ reduces_set R Iv x y)
    (h_eq_h : ∀ x y, (x, y) ∈ R.toARS_Mod.red ↔ reduces_set R Ih x y) :
    ChurchRosserModulo R.toARS_Mod := by
  -- Como demonstrado no livro, a Parte 1 garante que →_A é SCOH~[cite: 1].
  -- Consequentemente, →_A é CON~ e, pela Proposição 2.5.6, o sistema é CR~[cite: 1].
  sorry
