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
  · exact (hnorm z hxz).elim

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
    ∃ d e, Relation.ReflTransGen rb b d ∧ sim R d e ∧ Relation.ReflTransGen ra c e

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
      (MultisetExtension' R.label_order (lexMaxMeasure R.label_order [β_lbl])
      (lexMaxMeasure R.label_order τ) ∨
       lexMaxMeasure R.label_order [β_lbl] = lexMaxMeasure R.label_order τ)

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

open scoped Classical in
/-- A ordem lexicográfica >_lex descrita na prova do Teorema 2.5.10.
    Compara (||τ||, |σ|) com (||τ'||, |σ'|):
    Primeiro usa a extensão de multiconjunto sobre os rótulos horizontais.
    Se forem iguais, usa a ordem natural (<) sobre o comprimento das cadeias verticais. -/
def lex_order {α I : Type} (R : LabeledARS_Mod α I) [DecidableRel R.label_order] :
    (Multiset I × Nat) → (Multiset I × Nat) → Prop :=
  Lexicographic_Order (MultisetExtension R.label_order) (fun a b => a < b)

/-- Lema auxiliar: >_lex é bem-fundada. -/
lemma lex_order_wf {α I : Type} (R : LabeledARS_Mod α I) [DecidableRel R.label_order]
    (h_label_wf : WellFounded R.label_order) :
    WellFounded (lex_order R) := by
  have hwf_multiset := MultisetExtension_wf h_label_wf
  have hwf_nat := Nat.lt_wfRel.wf
  exact Lexicographic_Order_WellFounded hwf_multiset hwf_nat




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

/-- Estende o Diagrama (ii) para uma cadeia reflexiva-transitiva de ra.
    Semelhante ao Diagrama (iii), a relação de equivalência não gera
    divergências em formato de 'Hidra', permitindo uma indução simples. -/
lemma lifting_diagram_ii {α : Type} (R : ARS_Mod α) (ra : α → α → Prop)
    (h_diag_ii : Diagram_2_11_ii R ra) :
    ∀ a b c, Relation.ReflTransGen ra a b → sim R a c →
      ∃ d, sim R b d ∧ Relation.ReflTransGen ra c d := by
  intro a b c h_rab
  -- Indução simples sobre a cadeia reflexiva-transitiva de ra
  induction h_rab generalizing c with
  | refl =>
    intro h_sim_ac
    -- Caso base: 0 passos de ra. O elemento é o próprio c.
    use c
  | tail h_rax h_rxy ih =>
    intro h_sim_ac
    rcases ih c h_sim_ac with ⟨d1, h_sim_x_d1, h_ra_c_d1⟩
    -- Agora aplicamos o diagrama (ii) de 1 passo sobre x →_ra y e x ~ d1.
    rcases h_diag_ii _ _ _ h_rxy h_sim_x_d1 with ⟨d2, h_sim_y_d2, h_ra_d1_d2⟩
    -- Juntamos os caminhos.
    use d2
    constructor
    · exact h_sim_y_d2
    · exact Relation.ReflTransGen.trans h_ra_c_d1 h_ra_d1_d2

/-- Estende o Diagrama (iii) para uma cadeia reflexiva-transitiva de rb. -/
lemma lifting_diagram_iii {α : Type} (R : ARS_Mod α) (rb : α → α → Prop)
    (h_equiv : Equivalence (sim R))
    (h_diag_iii : Diagram_2_11_iii R rb) :
    ∀ a b c, sim R a b → Relation.ReflTransGen rb a c →
      ∃ d, Relation.ReflTransGen rb b d ∧ sim R d c := by
  intro a b c h_sim h_rac
  -- Indução simples sobre o comprimento da cadeia rb
  induction h_rac with
  | refl =>
    -- Caso base: 0 passos de rb. O elemento é o próprio b.
    use b
    constructor
    · exact Relation.ReflTransGen.refl
    · -- symm infere os vértices implicitamente
      exact h_equiv.symm h_sim
  | tail h_rax h_rxy ih =>
    -- Passo indutivo: a cadeia vai até x, e dá mais um passo até y.
    rcases ih with ⟨d1, h_rb_b_d1, h_sim_d1_x⟩
    -- Invertemos a equivalência d1 ~ x para x ~ d1
    have h_sim_x_d1 := h_equiv.symm h_sim_d1_x
    -- Aplicamos o diagrama (iii)
    rcases h_diag_iii _ d1 _ h_sim_x_d1 h_rxy with ⟨d2, h_rb_d1_d2, h_sim_d2_y⟩
    -- Juntamos os caminhos.
    use d2
    constructor
    · exact Relation.ReflTransGen.trans h_rb_b_d1 h_rb_d1_d2
    · exact h_sim_d2_y

/-- Lema de elevação: Converte uma cadeia de passos puros em uma cadeia módulo ~ -/
lemma lift_to_modulo {α : Type} (R : ARS_Mod α) (r : α → α → Prop) (h_equiv : Equivalence (sim R)) :
    ∀ x y, Relation.ReflTransGen r x y → Relation.ReflTransGen (ReducesModuloRel R r) x y := by
  intro x y h
  induction h with
  | refl =>
    exact Relation.ReflTransGen.refl
  | tail _ h_step ih =>
    refine Relation.ReflTransGen.trans ih (Relation.ReflTransGen.single ?_)
    unfold ReducesModuloRel
    -- A equivalência nos permite usar reflexividade nas pontas do passo único
    exact ⟨_, _, h_equiv.refl _, h_step, h_equiv.refl _⟩

/-- Teorema 2.5.10 (Parte 1):
  Se as relações locais ra e rb satisfazem os diagramas locais e a propriedade de
  fechamento decrescente, então ra e rb comutam módulo a equivalência de R.
-/
theorem Theorem_2_5_10_Part1 {α : Type}
    (R : ARS_Mod α)
    (ra rb : α → α → Prop)
    (h_equiv : Equivalence (sim R))
    (h_diag_ii : Diagram_2_11_ii R ra)
    (h_diag_iii : Diagram_2_11_iii R rb)
    (h_close_diagram : ∀ x y d1 e1 c, ra x y → Relation.ReflTransGen rb x d1 →
      sim R d1 e1 → Relation.ReflTransGen ra c e1 →
      ∃ d2 e2, Relation.ReflTransGen rb y d2 ∧ sim R d2 e2 ∧ Relation.ReflTransGen ra c e2) :
    CommutesModulo R ra rb := by
  unfold CommutesModulo
  constructor
  · -- Submeta 1: ra subcomuta com rb módulo ~
    unfold SubcommutesModulo
    intro a b c h_ra_ab h_rb_ac
    unfold ReducesModuloRel at h_ra_ab h_rb_ac
    rcases h_ra_ab with ⟨a1, b1, h_sim_a_a1, h_ra_a1_b1, h_sim_b1_b⟩
    rcases h_rb_ac with ⟨a2, c1, h_sim_a_a2, h_rb_a2_c1, h_sim_c1_c⟩
    -- 1. Alinhamento inicial (platô superior)
    have h_sim_a1_a := h_equiv.symm h_sim_a_a1
    have h_sim_a1_a2 := h_equiv.trans h_sim_a1_a h_sim_a_a2
    -- 2. Aplicação do Diagrama (ii) original
    have h_aplic_diag_ii := h_diag_ii a1 b1 a2 h_ra_a1_b1 h_sim_a1_a2
    rcases h_aplic_diag_ii with ⟨w1, h_sim_b1_w1, h_ra_a2_w1⟩
    -- 3. Cruzamento principal usando o lifting do Diagrama (i)
    have h_aplic_lifting :=
    lifting_diagram_i R ra rb h_equiv h_close_diagram a2 w1 c1 h_ra_a2_w1 h_rb_a2_c1
    rcases h_aplic_lifting with ⟨d, e, h_rb_w1_d, h_sim_d_e, h_ra_c1_e⟩
    -- 4. Empurrar a equivalência de b1 até b pelo caminho esquerdo (rb*)
    have h_sim_w1_b1 := h_equiv.symm h_sim_b1_w1
    have h_aplic_lift_iii_w1 :=
    lifting_diagram_iii R rb h_equiv h_diag_iii w1 b1 d h_sim_w1_b1 h_rb_w1_d
    rcases h_aplic_lift_iii_w1 with ⟨d', h_rb_b1_d', h_sim_d'_d⟩
    -- Correção 1: Usamos h_sim_b1_b diretamente, dispensando o symm
    have h_aplic_lift_iii_b :=
    lifting_diagram_iii R rb h_equiv h_diag_iii b1 b d' h_sim_b1_b h_rb_b1_d'
    rcases h_aplic_lift_iii_b with ⟨d'', h_rb_b_d'', h_sim_d''_d'⟩
    -- 5. Empurrar a equivalência de c1 até c pelo caminho direito (ra*)
    -- Correção 2: Removemos h_equiv da chamada para alinhar com a assinatura do seu lema
    have h_aplic_lift_ii_c := lifting_diagram_ii R ra h_diag_ii c1 e c h_ra_c1_e h_sim_c1_c
    rcases h_aplic_lift_ii_c with ⟨e', h_sim_e_e', h_ra_c_e'⟩
    -- 6. Conectar todas as equivalências no centro (d'' ~ e')
    have h_sim_d''_d := h_equiv.trans h_sim_d''_d' h_sim_d'_d
    have h_sim_d''_e := h_equiv.trans h_sim_d''_d h_sim_d_e
    have h_sim_d''_e' := h_equiv.trans h_sim_d''_e h_sim_e_e'
    -- 7. Fechar o diamante final com a elevação para módulo ~
    use d'', e'
    constructor
    · exact lift_to_modulo R rb h_equiv b d'' h_rb_b_d''
    · constructor
      · exact h_sim_d''_e'
      · exact lift_to_modulo R ra h_equiv c e' h_ra_c_e'
  · -- Submeta 2: rb subcomuta com ra módulo ~
    unfold SubcommutesModulo
    intro a b c h_rb_ab h_ra_ac
    unfold ReducesModuloRel at h_rb_ab h_ra_ac
    rcases h_rb_ab with ⟨a1, b1, h_sim_a_a1, h_rb_a1_b1, h_sim_b1_b⟩
    rcases h_ra_ac with ⟨a2, c1, h_sim_a_a2, h_ra_a2_c1, h_sim_c1_c⟩
    -- 1. Alinhamento inicial (platô superior)
    have h_sim_a1_a := h_equiv.symm h_sim_a_a1
    have h_sim_a1_a2 := h_equiv.trans h_sim_a1_a h_sim_a_a2
    -- 2. Aplicação do Diagrama (iii) (espelhado para rb)
    have h_aplic_diag_iii := h_diag_iii a1 a2 b1 h_sim_a1_a2 h_rb_a1_b1
    rcases h_aplic_diag_iii with ⟨w1, h_rb_a2_w1, h_sim_w1_b1⟩
    -- 3. Cruzamento principal invocando diretamente a hipótese de fechamento
    -- Como rb é uma cadeia e ra é um passo único, invocamos h_close_diagram diretamente.
    -- Alimentamos o platô inferior com reflexividade (w1 ~ w1 e w1 →* w1) para fechar a chamada.
    have h_sim_w1_w1 := h_equiv.refl w1
    have h_ra_w1_w1 : Relation.ReflTransGen ra w1 w1 := Relation.ReflTransGen.refl
    have h_aplic_fechamento :=
    h_close_diagram a2 c1 w1 w1 w1 h_ra_a2_c1 h_rb_a2_w1 h_sim_w1_w1 h_ra_w1_w1
    rcases h_aplic_fechamento with ⟨d, e, h_rb_c1_d, h_sim_d_e, h_ra_w1_e⟩
    -- 4. Empurrar a equivalência de c1 até c pelo caminho esquerdo (rb*)
    have h_aplic_lift_iii_c :=
    lifting_diagram_iii R rb h_equiv h_diag_iii c1 c d h_sim_c1_c h_rb_c1_d
    rcases h_aplic_lift_iii_c with ⟨d', h_rb_c_d', h_sim_d'_d⟩
    -- 5. Empurrar a equivalência de b1 até b pelo caminho direito (ra*)
    have h_sim_w1_b := h_equiv.trans h_sim_w1_b1 h_sim_b1_b
    have h_aplic_lift_ii_b := lifting_diagram_ii R ra h_diag_ii w1 e b h_ra_w1_e h_sim_w1_b
    rcases h_aplic_lift_ii_b with ⟨e', h_sim_e_e', h_ra_b_e'⟩
    -- 6. Conectar todas as equivalências no centro (e' ~ d')
    have h_sim_e'_e := h_equiv.symm h_sim_e_e'
    have h_sim_e_d := h_equiv.symm h_sim_d_e
    have h_sim_d_d' := h_equiv.symm h_sim_d'_d
    have h_sim_e'_d := h_equiv.trans h_sim_e'_e h_sim_e_d
    have h_sim_e'_d' := h_equiv.trans h_sim_e'_d h_sim_d_d'
    -- 7. Fechar o diamante final com a elevação para módulo ~
    use e', d'
    constructor
    · exact lift_to_modulo R ra h_equiv b e' h_ra_b_e'
    · constructor
      · exact h_sim_e'_d'
      · exact lift_to_modulo R rb h_equiv c d' h_rb_c_d'

lemma reduces_seq_nil_inv {α I : Type} (R : LabeledARS_Mod α I) {a b : α}
    (h : reduces_seq R [] a b) : a = b :=
  h

lemma reduces_seq_cons_inv {α I : Type} (R : LabeledARS_Mod α I) {i : I} {is : List I} {a b : α}
    (h : reduces_seq R (i :: is) a b) : ∃ c, R.reduces i a c ∧ reduces_seq R is c b :=
  h

lemma reduces_seq_trans {α I : Type} (R : LabeledARS_Mod α I) {a b c : α}
    (l1 l2 : List I) (h1 : reduces_seq R l1 a b) (h2 : reduces_seq R l2 b c) :
    reduces_seq R (l1 ++ l2) a c := by
  induction l1 generalizing a with
  | nil =>
    -- Caso base: l1 vazio implica a = b. Logo, o caminho é apenas h2.
    cases reduces_seq_nil_inv R h1
    exact h2
  | cons i is ih =>
    -- Passo indutivo: extrai o primeiro passo de l1 e aplica a hipótese no resto.
    rcases reduces_seq_cons_inv R h1 with ⟨x, h_step, h_rest⟩
    exact ⟨x, h_step, ih h_rest⟩

lemma lex_order_desc_left {α I : Type} (R : LabeledARS_Mod α I) [DecidableRel R.label_order]
    (m1 m2 : Multiset I) (n1 n2 : Nat)
    (h_mul : MultisetExtension R.label_order m1 m2) :
    lex_order R (m1, n1) (m2, n2) := by
  -- Expande a definição da ordem lexicográfica
  unfold lex_order
  -- Usa o lado esquerdo da disjunção (∨)
  apply Or.inl
  exact h_mul

lemma lex_order_desc_right {α I : Type} (R : LabeledARS_Mod α I) [DecidableRel R.label_order]
    (m : Multiset I) (n1 n2 : Nat)
    (h_nat : n1 < n2) :
    lex_order R (m, n1) (m, n2) := by
  unfold lex_order
  -- Usa o lado direito da disjunção (∨)
  apply Or.inr
  -- Como o lado direito costuma ser um "E" (m = m ∧ n1 < n2), usamos constructor
  constructor
  · rfl -- Prova que m = m por reflexividade
  · exact h_nat

lemma closure_of_decreasing_diagrams {α I : Type} (R : LabeledARS_Mod α I)
    (Iv Ih : Set I) [DecidableRel R.label_order] [DecidableEq I]
    (h_label_wf : WellFounded R.label_order)
    (h_local_dec : LocalDecreasingDiagramsHold R Iv Ih) :
    ∀ (measure : Multiset I × Nat) (x y d1 e1 c : α)
      (i_a : I) (τ_b σ_a : List I),

      -- VÍNCULO DA MEDIDA (Usamos a lista τ_b diretamente como Multiconjunto)
      measure = (↑τ_b, σ_a.length) →

      i_a ∈ Iv → (∀ i ∈ τ_b, i ∈ Ih) → (∀ i ∈ σ_a, i ∈ Iv) →
      R.reduces i_a x y → reduces_seq R τ_b x d1 →
      sim R.toARS_Mod d1 e1 → reduces_seq R σ_a c e1 →

      ∃ d2 e2 τ_b_new σ_a_new,
        (∀ i ∈ τ_b_new, i ∈ Ih) ∧ (∀ i ∈ σ_a_new, i ∈ Iv) ∧
        reduces_seq R τ_b_new y d2 ∧
        sim R.toARS_Mod d2 e2 ∧
        reduces_seq R σ_a_new c e2 := by

  intro measure
  induction measure using WellFounded.induction (lex_order_wf R h_label_wf) with
  | h m ih =>
    intro x y d1 e1 c i_a τ_b σ_a h_measure_eq h_ia_Iv h_tb_Ih h_sa_Iv
      h_ia_xy h_tb_xd1 h_sim_d1e1 h_sa_ce1

    -- Inspecionamos a cadeia horizontal τ_b
    cases τ_b with
    | nil =>
      -- ==========================================
      -- CASO BASE: τ_b é vazia (x = d1)
      -- ==========================================
      have h_x_eq_d1 := reduces_seq_nil_inv R h_tb_xd1
      subst h_x_eq_d1

      sorry

    | cons j js =>
      -- ==========================================
      -- PASSO INDUTIVO: τ_b tem pelo menos 1 passo (j :: js)
      -- ==========================================
      have h_cons_inv := reduces_seq_cons_inv R h_tb_xd1
      rcases h_cons_inv with ⟨x1, h_j_x_x1, h_js_x1_d1⟩

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
