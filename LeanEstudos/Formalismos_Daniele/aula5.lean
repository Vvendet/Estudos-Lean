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
