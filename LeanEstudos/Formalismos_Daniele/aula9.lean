import LeanEstudos.Formalismos_Daniele.aula8

-- ---------------------------------------------------------
-- Proposição 2.5.6 (Ciclo Completo)
-- ---------------------------------------------------------

/-- Lema auxiliar: A equivalência 'sim' é simétrica. -/
lemma sim_symm {α : Type} (R : ARS_Mod α) {x y : α} (h : sim R x y) : sim R y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hxy hstep ih =>
    have hvu : sim R _ _ := Relation.ReflTransGen.single (R.H_symm hstep)
    exact Relation.ReflTransGen.trans hvu ih

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
-- Lema 2.5.7 (Parte 1): WN + COH~ ⇒ SCOH~
-- ---------------------------------------------------------

/-- Coerência Módulo ~ (COH~): ~ · →* ⊆ ↓~ -/
def CoherentModulo {α : Type} (R : ARS_Mod α) : Prop :=
  ∀ a b c, sim R a b → ReducesStar R.toARS b c → IsJoinableModulo R a c

/-- Coerência Forte Módulo ~ (SCOH~): ~ · →* · ~ ⊆ ↓~ -/
def StronglyCoherentModulo {α : Type} (R : ARS_Mod α) : Prop :=
  ∀ a b c d, sim R a b → ReducesStar R.toARS b c → sim R c d → IsJoinableModulo R a d

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
