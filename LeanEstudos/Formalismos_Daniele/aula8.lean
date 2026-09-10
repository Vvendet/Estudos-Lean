import LeanEstudos.Formalismos_Daniele.aula7

-- ---------------------------------------------------------
-- Proposição 2.5.4: A Hierarquia de Coerência
-- ---------------------------------------------------------

/-- 2. COM H ⇒ SCOH H -/
lemma Compatible_to_StronglyCoherent {α : Type} (R : ARS_Mod α)
    (h : CompatibleWithH R) : StronglyCoherentWithH R := by
  intro a b c d hab hbc hcd
  -- Expandimos o diagrama usando a hipótese COM H
  rcases h a b c hab hbc with ⟨x, hax, hxc⟩
  -- Instanciamos os pontos da junção módulo
  exists x, d
  constructor
  · exact hax
  · constructor
    · -- Transitividade da equivalência: x ~ c e c ~ d implica x ~ d
      exact Relation.ReflTransGen.trans hxc hcd
    · exact ReducesStar_iff_ReducesStar'.mpr Relation.ReflTransGen.refl

/-- 3. SCOH H ⇒ COH H -/
lemma StronglyCoherent_to_Coherent {α : Type} (R : ARS_Mod α)
    (h : StronglyCoherentWithH R) : CoherentWithH R := by
  intro a b c hab hbc
  -- COH H é apenas o caso de SCOH H onde o passo final de equivalência é nulo (c ~ c)
  have hcc : sim R c c := Relation.ReflTransGen.refl
  exact h a b c c hab hbc hcc

/-- 4. COH H ⇒ LCOH H -/
lemma Coherent_to_LocallyCoherent {α : Type} (R : ARS_Mod α)
    (h : CoherentWithH R) : LocallyCoherentWithH R := by
  intro a b c hab hbc
  -- LCOH H foca em passos únicos, basta elevar o passo para a relação de múltiplos (→*)
  have hbc_star : ReducesStar R.toARS b c := Reduces.toReducesStar hbc
  exact h a b c hab hbc_star
