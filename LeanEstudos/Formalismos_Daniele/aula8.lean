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

/-- Caminho Lateral: LCMU H ⇒ LCOH H -/
lemma LocallyCommuting_to_LocallyCoherent {α : Type} (R : ARS_Mod α)
    (h : LocallyCommutingWithH R) : LocallyCoherentWithH R := by
  intro a b c hab hbc
  -- Expandimos o diagrama do Commuting (que nos dá um passo a →+ d)
  rcases h a b c hab hbc with ⟨d, had, hdc⟩
  exists d, c
  constructor
  · -- Como 'a' reduz para 'd' em passos positivos (ReducesPlus),
    -- está garantido que reduz no fecho reflexivo-transitivo (ReducesStar)
    rw [ReducesStar, ARS.reflTransClosure]
    exact Or.inl had
  · constructor
    · exact hdc
    · exact ReducesStar_iff_ReducesStar'.mpr Relation.ReflTransGen.refl

/-- Lema Auxiliar: Para provarmos SCOM H => COM H, precisamos mostrar que
    se a relação satisfaz a compatibilidade forte (SCOM H), então podemos
    empurrar um passo de redução (→) através de uma cadeia de equivalências (~). -/
lemma SCOM_sim_red {α : Type} (R : ARS_Mod α) (h : StronglyCompatibleWithH R) :
    ∀ x y, sim R x y → ∀ z, Reduces R.toARS y z → ∃ w, ReducesStar R.toARS x w ∧ sim R w z := by
  intro x y hxy
  -- Fazemos indução sobre a cadeia de equivalência x ~ y
  induction hxy with
  | refl =>
    intro z hyz
    exists z
    constructor
    · exact Reduces.toReducesStar hyz
    · exact Relation.ReflTransGen.refl
  | tail h_prefix h_step ih =>
    intro z hyz
    -- Aplicamos SCOM H no passo: x1 H y1 → z
    rcases h _ _ z h_step hyz with ⟨v, hxv, hvz⟩
    -- A resposta é x1 →= v. Analisamos os dois casos (1 passo ou 0 passos):
    rcases hxv with h_red | h_eq
    · -- Caso x1 → v: Invocamos a hipótese indutiva
      rcases ih v h_red with ⟨w, hxw, hwv⟩
      exists w
      constructor
      · exact hxw
      · exact Relation.ReflTransGen.trans hwv hvz
    · -- Caso x1 = v: Zero passos, basta reconectar a equivalência
      subst h_eq
      exists x
      constructor
      · exact ReducesStar_iff_ReducesStar'.mpr Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.trans h_prefix hvz

/-- 1. SCOM H ⇒ COM H -/
lemma StronglyCompatibleWithH_to_CompatibleWithH {α : Type} (R : ARS_Mod α)
    (h : StronglyCompatibleWithH R) : CompatibleWithH R := by
  intro a b c hab hbc
  have hbc' : ReducesStar' R.toARS b c :=
    ReducesStar_iff_ReducesStar'.mp hbc
  induction hbc' with
  | refl =>
      exists a
      constructor
      · exact ReducesStar_iff_ReducesStar'.mpr Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.single hab
  | tail h_prefix h_step ih =>
      rcases ih (ReducesStar_iff_ReducesStar'.mpr h_prefix) with ⟨d1, had1, hd1x⟩
      have h_sim_red := SCOM_sim_red R h d1 _ hd1x _ h_step
      rcases h_sim_red with ⟨d2, hd1d2, hd2y⟩
      exists d2
      constructor
      · exact ReducesStar.trans had1 hd1d2
      · exact hd2y

/-- Compatibilidade Módulo ~ (COM ~): ~ · →* ⊆ →* · ~
    Leitura: Se a ~ b →* c, deve existir um 'd' tal que a →* d ~ c. -/
def CompatibleModulo {α : Type} (R : ARS_Mod α) : Prop :=
  ∀ a b c, sim R a b → ReducesStar R.toARS b c →
    ∃ d, ReducesStar R.toARS a d ∧ sim R d c

/-- Implicação de Ida: COM H ⇒ COM ~
    Provado por indução no número de passos da equivalência (H^k)[cite: 1]. -/
lemma CompatibleWithH_to_CompatibleModulo {α : Type} (R : ARS_Mod α)
    (h : CompatibleWithH R) : CompatibleModulo R := by
  intro a b c hab hbc
  -- Essencial: 'revert c' generaliza o destino para que a Hipótese Indutiva
  -- possa ser aplicada a outros pontos intermediários (como d1).
  revert c
  induction hab with
  | refl =>
    intro c hac
    exists c
    constructor
    · exact hac
    · exact Relation.ReflTransGen.refl
  | tail h_prefix h_step ih =>
      intro c hb1c
      rcases h _ _ _ h_step hb1c with ⟨d1, ha1d1, hd1c⟩
      rcases ih d1 ha1d1 with ⟨d2, had2, hd2d1⟩
      exact ⟨d2, had2, Relation.ReflTransGen.trans hd2d1 hd1c⟩

/-- Implicação de Volta: COM ~ ⇒ COM H -/
lemma CompatibleModulo_to_CompatibleWithH {α : Type} (R : ARS_Mod α)
    (h : CompatibleModulo R) : CompatibleWithH R := by
  intro a b c hab hbc
  -- Como H é a base geradora de ~, 1 passo de H é um passo válido em ~
  have hab_sim : sim R a b := Relation.ReflTransGen.single hab
  exact h a b c hab_sim hbc
