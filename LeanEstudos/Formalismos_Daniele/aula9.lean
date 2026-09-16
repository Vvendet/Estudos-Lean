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
  -- Analisamos a cabeça da redução: ou é 0 passos, ou dá pelo menos 1 passo
  have cases_head := Relation.ReflTransGen.cases_head hxy_rtg
  rcases cases_head with (rfl | ⟨z, hxz, hzy⟩)
  · rfl
  · -- Se deu um passo (x → z), entra em contradição com o fato de 'x' ser forma normal
    exfalso
    exact hnorm z hxz

-- ---------------------------------------------------------
-- Lema 2.5.7
-- ---------------------------------------------------------



lemma WeaklyNormalizing_and_CoherentModulo_to_StronglyCoherentModulo {α : Type} (R : ARS_Mod α)
    (hWN : WeaklyNormalizing R.toARS)
    (hCOH : CoherentModulo R) : StronglyCoherentModulo R := by
  intro a b c d hab hbc hcd
  -- 1. Pela normalização fraca, 'c' reduz para uma forma normal 'c'
  rcases hWN c with ⟨c', hcc', hnorm_c'⟩
  -- 2. Conectamos b →* c com c →* c' para obter b →* c'
  have hbc' : ReducesStar R.toARS b c' := ReducesStar.trans hbc hcc'
  -- 3. Aplicamos COH~ para a cadeia (a ~ b →* c')
  rcases hCOH a b c' hab hbc' with ⟨e, v1, hae, hev1, hc'v1⟩
  -- Como c' é forma normal, c' →* v1 implica c' = v1
  have heq1 : c' = v1 := IsNormal_ReducesStar_eq R c' v1 hnorm_c' hc'v1
  rw [← heq1] at hev1
  -- 4. Invertemos c ~ d para d ~ c e aplicamos COH~ para a cadeia (d ~ c →* c')
  have hdc : sim R d c := sim_symm R hcd
  rcases hCOH d c c' hdc hcc' with ⟨f, v2, hdf, hfv2, hc'v2⟩
  -- Novamente, c' é forma normal, logo c' = v2
  have heq2 : c' = v2 := IsNormal_ReducesStar_eq R c' v2 hnorm_c' hc'v2
  rw [← heq2] at hfv2
  -- 5. Agora temos a →* e ~ c' e também d →* f ~ c'.
  -- Pela simetria e transitividade de ~, concluímos que e ~ f
  have hc'f : sim R c' f := sim_symm R hfv2
  have hef : sim R e f := Relation.ReflTransGen.trans hev1 hc'f
  -- 6. Instanciamos a junção módulo final para 'a' e 'd' demonstrando que ↓~ ocorre
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

/-- Definição 2.5.9 (Parte 1): Subcomutação Módulo ~
    →_α subcomuta com →_β módulo ~ se: a →_α b →_β c implica que
    existem d, e tais que a →_β d ~ e *←_α c. -/
def SubcommutesModulo {α : Type} (R : ARS_Mod α) (ra rb : α → α → Prop) : Prop :=
  ∀ a b c, ra a b → rb b c →
    ∃ d e, rb a d ∧ sim R d e ∧ Relation.ReflTransGen ra c e

/-- Definição 2.5.9 (Parte 2): Comutação Módulo ~[cite: 1]
    →_α comuta com →_β módulo ~ se →~_α subcomuta com →~_β módulo ~
    e →~_β subcomuta com →~_α módulo ~.[cite: 1] -/
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

/-- 2. O Mapeamento da Relação (Subrelation):
    Prova que se M1 >_mul M2 na definição (FiniteMultisetExtension),
    então M1 se expande para M2 na definição da Mathlib (CutExpand). -/
lemma MultisetExtension_to_CutExpand {α : Type} [DecidableEq α] (R : α → α → Prop)
    (M1 M2 : FiniteMultiset α)
    (h_ext : FiniteMultisetExtension R M1 M2) :
    Relation.CutExpand R (FiniteMultiset_to_Mathlib M2) (FiniteMultiset_to_Mathlib M1) := by
  -- 1. Desdobramos a sua extensão para revelar os conjuntos originais X e Y
  unfold FiniteMultisetExtension at h_ext
  unfold MultisetExtension at h_ext
  rcases h_ext with ⟨X_val, Y_val, hX_fin, hY_fin, hX_nempty, hX_sub_M1, hM2_eq, h_red⟩
  let X : FiniteMultiset α := ⟨X_val, hX_fin⟩
  let Y : FiniteMultiset α := ⟨Y_val, hY_fin⟩
  let X_mathlib := FiniteMultiset_to_Mathlib X
  let Y_mathlib := FiniteMultiset_to_Mathlib Y
  have h_algebraic_equiv : FiniteMultiset_to_Mathlib M2 =
        (FiniteMultiset_to_Mathlib M1 - X_mathlib) + Y_mathlib := by
      apply Multiset.ext.mpr
      intro a

      rw [Multiset.count_add, Multiset.count_sub]
      rw [count_toMathlib M2, count_toMathlib M1, count_toMathlib X, count_toMathlib Y]

      have h_eval := congrFun hM2_eq a
      unfold GMultiset.sum GMultiset.diff at h_eval

      have fin_M1 := M1.property.1 a
      have fin_M2 := M2.property.1 a
      have fin_X := X.property.1 a
      have fin_Y := Y.property.1 a

      cases eq1 : M1.val a with
      | top => exact False.elim (fin_M1 eq1)
      | coe n1 =>
        cases eq2 : M2.val a with
        | top => exact False.elim (fin_M2 eq2)
        | coe n2 =>
          cases eqX : X.val a with
          | top => exact False.elim (fin_X eqX)
          | coe nX =>
            cases eqY : Y.val a with
            | top => exact False.elim (fin_Y eqY)
            | coe nY =>
              -- 1. Reescrevemos a hipótese ignorando as coerções (↑) e os nomes antigos.
              -- Como M1 tem coerção automática para M1.val, e X_val originou X.val,
              -- o Lean aceita essa mudança definicional de bom grado!
              change M2.val a = M1.val a - X.val a + Y.val a at h_eval

              -- 2. Agora o 'rw' consegue aplicar todas as equações do 'cases' perfeitamente
              rw [eq1, eq2, eqX, eqY] at h_eval

              -- 3. Passamos a igualdade do domínio ENat para os Naturais padrão
              have h_final := congrArg ENat.toNat h_eval

              -- 4. O simplificador faz a matemática básica e fecha a álgebra
              revert h_final
              simp
              intro h_final
              exact h_final

  -- 5. A Mathlib requer que para todo y ∈ Y_mathlib, exista um x ∈ X_mathlib tal que R x y.
  -- 5. A Mathlib requer que para todo y ∈ Y_mathlib, exista um x ∈ X_mathlib tal que R x y.
-- 5. A Mathlib requer que para todo y ∈ Y_mathlib, exista um x ∈ X_mathlib tal que R x y.
  have h_reduction_equiv : ∀ y ∈ Y_mathlib, ∃ x ∈ X_mathlib, R x y := by
    intro y hy
    -- Na Mathlib, 'y' pertence a um Multiset se a sua contagem for > 0
    have hy_count : Multiset.count y Y_mathlib > 0 := Multiset.count_pos.mpr hy
    rw [count_toMathlib Y] at hy_count

    -- Traduzimos o 'toNat > 0' de volta para a sua pertinência original (Y_val y > 0)
    have hy_mem : y ∈ Y_val := by
      change Y_val y > 0
      have fin_Y := Y.property.1 y
      change Y_val y ≠ ⊤ at fin_Y
      cases eqY : Y_val y with
      | top => exact False.elim (fin_Y eqY)
      | coe nY =>
        -- Alinhamos a sintaxe definicional para o rw reconhecer Y_val
        change (Y_val y).toNat > 0 at hy_count ⊢
        rw [eqY] at hy_count ⊢
        exact hy_count

    -- Invocamos a sua hipótese estrutural 'h_red' (∀ y ∈ Y_val, ∃ x ∈ X_val, ...)
    rcases h_red y hy_mem with ⟨x, hx_mem, hRxy⟩
    exists x

    -- Provamos a pertinência na Mathlib e fechamos o passo relacional
    constructor
    · apply Multiset.count_pos.mp
      rw [count_toMathlib X]
      have fin_X := X.property.1 x
      change X_val x ≠ ⊤ at fin_X
      cases eqX : X_val x with
      | top => exact False.elim (fin_X eqX)
      | coe nX =>
        -- Alinhamos a sintaxe definicional para o rw reconhecer X_val
        change X_val x > 0 at hx_mem
        change (X_val x).toNat > 0
        rw [eqX] at hx_mem ⊢
        exact hx_mem
    · exact hRxy

  -- 6. Finalmente, aplicamos o construtor de CutExpand da Mathlib com as peças validadas
  -- (O construtor exato aplicaria h_algebraic_equiv e h_reduction_equiv)
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

/-- Teorema 2.5.10 (Parte 1): Se os diagramas locais decrescentes valem,
    então a união vertical (→_v) comuta com a união horizontal (→_h) módulo ~. -/
theorem Theorem_2_5_10_Part1 {α I : Type} (R : LabeledARS_Mod α I) (Iv Ih : Set I)
    [DecidableRel R.label_order] [DecidableEq I]
    (h_diagrams : LocalDecreasingDiagramsHold R Iv Ih) :
    CommutesModulo R.toARS_Mod (reduces_set R Iv) (reduces_set R Ih) := by
  -- A prova exige indução sobre a ordem lexicográfica >_lex, combinando a extensão
  -- de multiconjunto >_mul e o comprimento das cadeias[cite: 1].
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
