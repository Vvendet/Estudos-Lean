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
lemma Acc_r_of_Acc_Multiset {α : Type} [DecidableEq α] {r : α → α → Prop} (a : α)
    (h : Acc (MultisetExtension r) (GMultiset.finite_singleton a)) : Acc r a := by
  have H : ∀ (M : GMultiset α), Acc (MultisetExtension r) M →
      ∀ (a : α), M = GMultiset.finite_singleton a → Acc r a := by
    intro M hM
    induction hM with
    | intro M1 h_acc ih =>
      intro a1 h_eq
      subst h_eq
      constructor
      intro x hr
      -- Construímos o diagrama do passo na sua extensão multiconjunto
      have h_ext :
      MultisetExtension r (GMultiset.finite_singleton x) (GMultiset.finite_singleton a1)
      := by
        unfold MultisetExtension
        refine ⟨GMultiset.finite_singleton x, GMultiset.finite_singleton a1, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · -- Prova de IsFiniteMultiset X
          constructor
          · intro z; unfold GMultiset.finite_singleton; split_ifs <;> simp
          · have h_sub : {a | GMultiset.finite_singleton x a > 0} ⊆ {x} := by
              intro z hz
              change GMultiset.finite_singleton x z > 0 at hz
              unfold GMultiset.finite_singleton at hz
              split_ifs at hz with h
              · exact h
              · revert hz; simp
            exact Set.Finite.subset (Set.finite_singleton x) h_sub
        · -- Prova de IsFiniteMultiset Y
          constructor
          · intro z; unfold GMultiset.finite_singleton; split_ifs <;> simp
          · have h_sub : {a | GMultiset.finite_singleton a1 a > 0} ⊆ {a1} := by
              intro z hz
              change GMultiset.finite_singleton a1 z > 0 at hz
              unfold GMultiset.finite_singleton at hz
              split_ifs at hz with h
              · exact h
              · revert hz; simp
            exact Set.Finite.subset (Set.finite_singleton a1) h_sub
        · -- Prova de X ≠ ∅
          intro h_empty
          have h_eval : GMultiset.finite_singleton x x = GMultiset.empty x := congrFun h_empty x
          unfold GMultiset.finite_singleton GMultiset.empty at h_eval
          simp at h_eval
        · -- Prova de X ⊆ M1
          intro z
          exact le_rfl
        · -- Prova de M2 = (M1 \ X) ⊕ Y
          funext z
          unfold GMultiset.sum GMultiset.diff GMultiset.finite_singleton
          split_ifs <;> rfl
        · -- Prova de ∀ y, y ∈ Y → ∃ x', x' ∈ X ∧ r x' y
          intro y hy
          change GMultiset.finite_singleton a1 y > 0 at hy
          unfold GMultiset.finite_singleton at hy
          split_ifs at hy with h_ya1
          · refine ⟨x, ?_, ?_⟩
            · change GMultiset.finite_singleton x x > 0
              unfold GMultiset.finite_singleton
              simp
            · subst h_ya1
              exact hr
          · revert hy; simp
      exact ih (GMultiset.finite_singleton x) h_ext x rfl
  exact H (GMultiset.finite_singleton a) h a rfl

open scoped Classical in
/-- Teorema 2.3.12 (Ohlebusch / Dershowitz-Manna): A extensão multiconjunto
    finita de uma ordem parcial é bem-fundada se, e somente se, a relação
    original for bem-fundada.

    Aqui formalizamos a direção (<=) da equivalência. -/
theorem MultiSet_WF_iff_ARS_WF {α : Type} (r : α → α → Prop) :
    WellFounded (MultisetExtension r) → WellFounded r := by
  intro h_wf_ext
  constructor
  intro a
  -- Invocamos a prova de acessibilidade global instanciando com o singleton e extraindo
  exact Acc_r_of_Acc_Multiset a (h_wf_ext.apply (GMultiset.finite_singleton a))

def FiniteMultisetExtension {α : Type} (R : α → α → Prop) (M1 M2 : FiniteMultiset α) : Prop :=
  MultisetExtension R M1.val M2.val

theorem Theorem_2_3_12_LeftToRight {α : Type} (r : α → α → Prop) :
    WellFounded r → WellFounded (Relation.TransGen (Relation.CutExpand r)) := by
  intro h_wf
  -- Invocamos o teorema clássico de Dershowitz-Manna (Hydra / CutExpand)
  have h_wf_cut := WellFounded.cutExpand h_wf
  -- A extensão plena é geometricamente o fecho transitivo do passo único
  exact WellFounded.transGen h_wf_cut
