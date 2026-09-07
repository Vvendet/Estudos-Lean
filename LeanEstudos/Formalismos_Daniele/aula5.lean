import LeanEstudos.Formalismos_Daniele.aula4

-- 1. Multiconjunto Geral (General Multiset)
-- Um multiconjunto M sobre A é um mapeamento M : A -> N_∞.
def GMultiset (α : Type) := α → ENat

-- 2. Multiconjunto Finito (Finite Multiset)
-- É um multiconjunto onde a soma de todos os elementos é < ∞.
-- Em termos de tipos dependentes, isso significa que a função nunca
-- retorna ∞ (⊤) e que o suporte (elementos maiores que 0) é finito.
def IsFiniteMultiset {α : Type} (M : GMultiset α) : Prop :=
  (∀ a, M a ≠ ⊤) ∧ Set.Finite {a | M a > 0}

def FiniteMultiset (α : Type) := { M : GMultiset α // IsFiniteMultiset M }

-- 3. Conjunto sobre A (Set over A)
-- É um multiconjunto S tal que para todo a ∈ A, S(a) ∈ {0, ∞}.
def IsSetMultiset {α : Type} (M : GMultiset α) : Prop :=
  ∀ a, M a = 0 ∨ M a = ⊤

def SetMultiset (α : Type) := { M : GMultiset α // IsSetMultiset M }


-- Intersecção (baseada no mínimo)
noncomputable def GMultiset.inter {α : Type} (M1 M2 : GMultiset α) : GMultiset α :=
fun a => min (M1 a) (M2 a)

-- União (baseada no máximo)
noncomputable def GMultiset.union {α : Type} (M1 M2 : GMultiset α) : GMultiset α :=
  fun a => max (M1 a) (M2 a)

-- Soma (baseada na adição)
def GMultiset.sum {α : Type} (M1 M2 : GMultiset α) : GMultiset α :=
  fun a => M1 a + M2 a

-- Diferença (baseada na subtração truncada, onde m - ∞ = 0)
def GMultiset.diff {α : Type} (M1 M2 : GMultiset α) : GMultiset α :=
  fun a => M1 a - M2 a

-- 3. O multiconjunto vazio é a função constante 0
def GMultiset.empty {α : Type} : GMultiset α :=
  fun _ => 0

-- Instancia a notação ∅ (EmptyCollection) para GMultiset
instance {α : Type} : EmptyCollection (GMultiset α) := ⟨GMultiset.empty⟩


-- 4. Pertinência e Inclusão de Multiconjuntos
def GMultiset.Mem {α : Type} (M : GMultiset α) (a : α) : Prop :=
  M a > 0

-- Instancia a notação a ∈ M (Membership)
instance {α : Type} : Membership α (GMultiset α) := ⟨GMultiset.Mem⟩

def GMultiset.Subset {α : Type} (M N : GMultiset α) : Prop :=
  ∀ a, M a ≤ N a

-- Instancia a notação M ⊆ N (HasSubset)
instance {α : Type} : HasSubset (GMultiset α) := ⟨GMultiset.Subset⟩


-- 5. As classes já foram denotadas anteriormente pelas definições:
-- GMultiset, FiniteMultiset e SetMultiset.


-- 6. Compreensão de Multiconjuntos e Conjuntos
-- [a]: multiconjunto finito com exatamente uma ocorrência de a (valor 1)
def GMultiset.finite_singleton {α : Type} [DecidableEq α] (a : α) : GMultiset α :=
  fun x => if x = a then 1 else 0

-- {a}: conjunto com infinitas ocorrências de a (valor ⊤, que representa ∞)
def GMultiset.set_singleton {α : Type} [DecidableEq α] (a : α) : GMultiset α :=
  fun x => if x = a then ⊤ else 0

/-- A extensão finita de multiconjunto de uma relação de ordem R -/
def MultisetExtension {α : Type} (R : α → α → Prop) (M1 M2 : GMultiset α) : Prop :=
  ∃ X Y : GMultiset α,
    IsFiniteMultiset X ∧
    IsFiniteMultiset Y ∧
    X ≠ ∅ ∧
    X ⊆ M1 ∧
    M2 = GMultiset.sum (GMultiset.diff M1 X) Y ∧
    ∀ y, y ∈ Y → ∃ x, x ∈ X ∧ R x y
