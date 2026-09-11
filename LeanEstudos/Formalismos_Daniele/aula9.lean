import LeanEstudos.Formalismos_Daniele.aula8

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
