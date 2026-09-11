import LeanEstudos.Formalismos_Daniele.aula6
import Mathlib.Logic.Relation

/-- Sistema Abstrato de Redução Módulo.
    Contém a relação simétrica base H. A equivalência ~ é derivada dela[cite: 1]. -/
structure ARS_Mod (α : Type) extends ARS α where
  H : α → α → Prop
  H_symm : Symmetric H

/-- ~ denota o fecho reflexivo-transitivo da relação simétrica H[cite: 1]. -/
def sim {α : Type} (R : ARS_Mod α) : α → α → Prop :=
  Relation.ReflTransGen R.H


/-- Noção de juntabilidade com relação a uma relação arbitrária S -/
def IsJoinableS {α : Type} (R : ARS α) (S : α → α → Prop) (a b : α) : Prop :=
  ∃ c d, ReducesStar R a c ∧ S c d ∧ ReducesStar R b d

-- ---------------------------------------------------------
-- Definição 2.5.1: Relações Básicas
-- ---------------------------------------------------------

def StepModulo {α : Type} (R : ARS_Mod α) (a b : α) : Prop :=
  Reduces R.toARS a b ∨ Reduces R.toARS b a ∨ sim R a b

def ConversionModulo {α : Type} (R : ARS_Mod α) : α → α → Prop :=
  Relation.ReflTransGen (StepModulo R)

def IsJoinableModulo {α : Type} (R : ARS_Mod α) (a b : α) : Prop :=
  ∃ c d, ReducesStar R.toARS a c ∧ sim R c d ∧ ReducesStar R.toARS b d

def ReducesModulo {α : Type} (R : ARS_Mod α) (a b : α) : Prop :=
  ∃ c d, sim R a c ∧ Reduces R.toARS c d ∧ sim R d b

-- ---------------------------------------------------------
-- Definição 2.5.2: Propriedades Módulo
-- ---------------------------------------------------------

/-- 1. Diamond Property Modulo ~ -/
def DiamondPropertyStarModulo {α : Type} (R : ARS_Mod α) : Prop :=
  ∀ a b c z1 z2, ReducesStar R.toARS a z1 → sim R z1 b →
                 ReducesStar R.toARS a z2 → sim R z2 c →
                 IsJoinableModulo R b c

/-- 2. Church-Rosser Modulo ~ (CR~) -/
def ChurchRosserModulo {α : Type} (R : ARS_Mod α) : Prop :=
  ∀ a b, ConversionModulo R a b → IsJoinableModulo R a b

/-- 3. Almost Church-Rosser Modulo ~ (ACR~): *← · ~ · →* ⊆ ↓~[cite: 1] -/
def AlmostChurchRosserModulo {α : Type} (R : ARS_Mod α) : Prop :=
  ∀ a b c d, ReducesStar R.toARS a b → sim R a c → ReducesStar R.toARS c d →
    IsJoinableModulo R b d

/-- 4. Confluence Modulo ~ (CON~): *← · →* ⊆ ↓~[cite: 1] -/
def ConfluenceModulo {α : Type} (R : ARS_Mod α) : Prop :=
  ∀ a b c, ReducesStar R.toARS a b → ReducesStar R.toARS a c → IsJoinableModulo R b c

/-- 5. Locally Confluent Modulo ~ (LCON~): ← · → ⊆ ↓~[cite: 1] -/
def LocallyConfluentModulo {α : Type} (R : ARS_Mod α) : Prop :=
  ∀ a b c, Reduces R.toARS a b → Reduces R.toARS a c → IsJoinableModulo R b c



/-- 7. Coherent with H (COHH): H · →* ⊆ ↓~[cite: 1] -/
def CoherentWithH' {α : Type} (R : ARS_Mod α) : Prop :=
  ∀ a b c, R.H a b → ReducesStar R.toARS b c
  → IsJoinableS R.toARS (Relation.ReflTransGen (StepModulo R)) a c

def CoherentWithH {α : Type} (R : ARS_Mod α) : Prop :=
  ∀ a b c, R.H a b → ReducesStar R.toARS b c → IsJoinableModulo R a c

/-- 8. Locally Coherent with H (LCOHH): H · → ⊆ ↓~[cite: 1] -/
def LocallyCoherentWithH {α : Type} (R : ARS_Mod α) : Prop :=
  ∀ a b c, R.H a b → Reduces R.toARS b c → IsJoinableModulo R a c

/-- 9. Strongly Coherent with H (SCOHH): H · →* · ~ ⊆ ↓~
    Leitura: Se a H b →* c ~ d, então a e d são juntáveis módulo ~. -/
def StronglyCoherentWithH {α : Type} (R : ARS_Mod α) : Prop :=
  ∀ a b c d, R.H a b → ReducesStar R.toARS b c → sim R c d →
    IsJoinableModulo R a d

/-- 10. Compatible with H (COMH): H · →* ⊆ →* · ~[cite: 9]
    Leitura: Se a H b →* c, deve existir um 'd' tal que a →* d ~ c. -/
def CompatibleWithH {α : Type} (R : ARS_Mod α) : Prop :=
  ∀ a b c, R.H a b → ReducesStar R.toARS b c →
    ∃ d, ReducesStar R.toARS a d ∧ sim R d c

/-- Relação Auxiliar -/
def ReducesEqual {α : Type} (R : ARS α) (a b : α) : Prop :=
  Reduces R a b ∨ a = b

/-- 11. Strongly Compatible with H (SCOMH): H · → ⊆ →^= · ~[cite: 9]
    Leitura: Se a H b → c, deve existir um 'd' tal que a →^= d ~ c. -/
def StronglyCompatibleWithH {α : Type} (R : ARS_Mod α) : Prop :=
  ∀ a b c, R.H a b → Reduces R.toARS b c →
    ∃ d, ReducesEqual R.toARS a d ∧ sim R d c

/-- 12. Locally Commuting with H (LCMUH): H · → ⊆ →^+ · ~[cite: 9]
    Leitura: Se a H b → c, deve existir um 'd' tal que a →^+ d ~ c. -/
def LocallyCommutingWithH {α : Type} (R : ARS_Mod α) : Prop :=
  ∀ a b c, R.H a b → Reduces R.toARS b c →
    ∃ d, ReducesPlus R.toARS a d ∧ sim R d c

def StronglyLocallyConfluentModulo {α : Type} (R : ARS_Mod α) : Prop :=
  ∀ a b c, Reduces R.toARS a b → Reduces R.toARS a c →
    ∃ d e, ReducesEqual R.toARS b d ∧ sim R d e ∧ ReducesStar R.toARS c e

-- ---------------------------------------------------------
-- Lemas de Hierarquia da confluência módulo ~
-- ---------------------------------------------------------

lemma StronglyLocallyConfluenceModulo_to_LocallyConfluenceModulo {α : Type} (R : ARS_Mod α)
(h : StronglyLocallyConfluentModulo R) : LocallyConfluentModulo R := by
  intro a b c hab hac
  rcases h a b c hab hac with ⟨d, e, hbd, hde, hce⟩
  exists d, e
  constructor
  · have hbdstar : ReducesStar R.toARS b d := by
        unfold ReducesEqual at hbd
        exact ReducesEqual_to_ReducesStar R.toARS hbd
    exact hbdstar
  · constructor
    · exact hde
    · exact hce

lemma ConfluenceModulo_to_LocallyConfluenceModulo {α : Type} (R : ARS_Mod α)
(h : ConfluenceModulo R) : LocallyConfluentModulo R := by
    intro a b c hab hac
    unfold ConfluenceModulo at h
    have h1 := h a b c (Reduces.toReducesStar hab) (Reduces.toReducesStar hac)
    rcases h1 with ⟨d, e, hbd, hde, hce⟩
    exact ⟨d, e, hbd, hde, hce⟩

lemma AlmostChurchRosserModulo_to_ConfluenceModulo {α : Type} (R : ARS_Mod α)
(h : AlmostChurchRosserModulo R) : ConfluenceModulo R := by
    intro a b c hab hac
    unfold AlmostChurchRosserModulo at h
    have h1 := h a b a c hab (Relation.ReflTransGen.refl) hac
    rcases h1 with ⟨d, e, hbd, hde, hce⟩
    exact ⟨d, e, hbd, hde, hce⟩

lemma ChurchRosserModulo_to_AlmostChurchRosserModulo {α : Type} (R : ARS_Mod α)
    (h : ChurchRosserModulo R) : AlmostChurchRosserModulo R := by
  intro a b c d hab hac hcd
  unfold ChurchRosserModulo at h
  -- 1. Convertemos as hipóteses para a versão indutiva
  have hab_rtg := ReducesStar_iff_ReducesStar'.mp hab
  have hcd_rtg := ReducesStar_iff_ReducesStar'.mp hcd
  -- 2. Construir o caminho b ->* a em ConversionModulo
  have hba : ConversionModulo R b a := by
    clear hab
    induction hab_rtg with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ h_step ih =>
      exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single (Or.inr (Or.inl h_step))) ih
  -- 3. Construir o caminho a ~ c em ConversionModulo
  have hac' : ConversionModulo R a c := by
    exact Relation.ReflTransGen.single (Or.inr (Or.inr hac))
  -- 4. Construir o caminho c ->* d em ConversionModulo
  have hcd' : ConversionModulo R c d := by
    clear hcd
    induction hcd_rtg with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ h_step ih =>
      exact Relation.ReflTransGen.trans ih (Relation.ReflTransGen.single (Or.inl h_step))
  -- 5. Concatenar tudo: (b ->* a) trans (a ~ c) trans (c ->* d)
  have hbc : ConversionModulo R b c := Relation.ReflTransGen.trans hba hac'
  have hbd : ConversionModulo R b d := Relation.ReflTransGen.trans hbc hcd'
  -- 6. Finalizar aplicando a hipótese Church-Rosser Módulo (CR~)
  exact h b d hbd

lemma ChurchRosserModulo_to_DiamondPropertyStarModulo {α : Type} (R : ARS_Mod α)
    (h : ChurchRosserModulo R) : DiamondPropertyStarModulo R := by
  intro a b c z1 z2 haz1 hz1b haz2 hz2c
  unfold ChurchRosserModulo at h
  -- 1. Construir b ~ z1 em ConversionModulo (invertendo hz1b)
  have hbz1 : ConversionModulo R b z1 := by
    -- Nenhuma outra hipótese local depende de 'b', a indução é segura.
    induction hz1b with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ h_step ih =>
      -- Invertemos a relação base H usando a prova de simetria embutida na estrutura
      exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single
       (Or.inr (Or.inr (Relation.ReflTransGen.single (R.H_symm h_step))))) ih
  -- 2. Construir z1 *<- a em ConversionModulo (invertendo haz1)
  have hz1a : ConversionModulo R z1 a := by
    have haz1_rtg := ReducesStar_iff_ReducesStar'.mp haz1
    -- Limpamos as hipóteses que dependem de z1 apenas dentro deste escopo para proteger a indução
    clear haz1 hz1b hbz1
    induction haz1_rtg with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ h_step ih =>
      exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single (Or.inr (Or.inl h_step))) ih
  -- 3. Construir a ->* z2 em ConversionModulo
  have haz2' : ConversionModulo R a z2 := by
    have haz2_rtg := ReducesStar_iff_ReducesStar'.mp haz2
    -- Limpamos as hipóteses que dependem de z2 apenas dentro deste escopo
    clear haz2 hz2c
    induction haz2_rtg with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ h_step ih =>
      exact Relation.ReflTransGen.trans ih (Relation.ReflTransGen.single (Or.inl h_step))
  -- 4. Construir z2 ~ c em ConversionModulo
  have hz2c' : ConversionModulo R z2 c := by
    exact Relation.ReflTransGen.single (Or.inr (Or.inr hz2c))
  -- 5. Concatenar todos os fragmentos: (b ~ z1) trans (z1 *<- a) trans (a ->* z2) trans (z2 ~ c)
  have hba : ConversionModulo R b a := Relation.ReflTransGen.trans hbz1 hz1a
  have hac : ConversionModulo R a c := Relation.ReflTransGen.trans haz2' hz2c'
  have hbc : ConversionModulo R b c := Relation.ReflTransGen.trans hba hac
  -- 6. Finalizar aplicando a hipótese Church-Rosser Módulo (CR~)
  exact h b c hbc
