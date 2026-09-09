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
-- Definição 2.5.2: Propriedades Módulo (Tradução Corrigida)
-- ---------------------------------------------------------

/-- 1. Diamond Property Modulo ~ -/
def DiamondPropertyStarModulo {α : Type} (R : ARS_Mod α) : Prop :=
  ∀ a b c, ReducesModulo R a b → ReducesModulo R a c → IsJoinableModulo R b c

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

/-- Relação Auxiliar (já no seu código, está perfeita!) -/
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
