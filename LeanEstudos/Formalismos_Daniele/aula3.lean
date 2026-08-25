import LeanEstudos.Formalismos_Daniele.aula2
import Mathlib.Logic.Relation

def StronglyConfluent' {α : Type} (R : ARS α) : Prop :=
∀ x y z, Reduces R x y ∧ Reduces R x z → ∃ w, ReducesStar R y w ∧ (Reduces R z w ∨ w = z)

def LocallyConfluent' {α : Type} (R : ARS α) : Prop :=
∀ x y z, Reduces R x y ∧ Reduces R x z → ∃ w, ReducesStar R y w ∧ ReducesStar R z w

def HasSingleNormalFormOf' {α : Type} (R : ARS α) : Prop :=
∀ a b c, (ReducesStar R a b ∧ ReducesStar R a c) ∧ ( IsNormal R b ∧ IsNormal R c) → b = c


def HasSingleNormalForm' {α : Type} (R : ARS α) : Prop :=
∀ a b, ReducesReflSymmTrans R a b ∧ (IsNormal R a ∧ IsNormal R b) → a = b

def HasNormalFormProperty' {α} (R : ARS α) : Prop :=
∀ a b, ReducesReflSymmTrans R a b ∧ IsNormal R b → ReducesStar R a b

def StronglyConfluent {α : Type} (R : ARS α) : Prop :=
  ∀ x y z,
    Reduces R x y →
    Reduces R x z →
    ∃ w,
      ReducesStar R y w ∧
      (Reduces R z w ∨ w = z)


def LocallyConfluent {α : Type} (R : ARS α) : Prop :=
  ∀ x y z,
    Reduces R x y →
    Reduces R x z →
    ∃ w,
      ReducesStar R y w ∧
      ReducesStar R z w


def HasSingleNormalForm_of {α : Type} (R : ARS α) : Prop :=
  ∀ a b c,
    ReducesStar R a b →
    ReducesStar R a c →
    IsNormal R b →
    IsNormal R c →
    b = c

def HasSingleNormalForm {α : Type} (R : ARS α) : Prop :=
  ∀ a b,
    ReducesReflSymmTrans R a b →
    IsNormal R a →
    IsNormal R b →
    a = b


def HasNormalFormProperty {α : Type} (R : ARS α) : Prop :=
  ∀ a b,
    ReducesReflSymmTrans R a b →
    IsNormal R b →
    ReducesStar R a b

lemma Reduces.pow_subset_symmClosure
    {α : Type} (R : ARS α) :
    ∀ n, Reduces.pow R n ⊆ Reduces.pow R.symmClosure n := by
  intro n
  induction n with
  | zero  =>
      intro x hx
      simpa [Reduces.pow, ARS.id] using hx
  | succ n ih =>
      intro x hx
      rw [Reduces.pow] at hx ⊢
      rcases hx with ⟨y, hxy, hyz⟩
      refine ⟨y, ?_, ?_⟩
      · exact ih hxy
      · -- R.red está contida na relação simétrica de R
        rw [ARS.symmClosure]
        exact Or.inl hyz

def ReducesStar' {α : Type} (R : ARS α) (x y : α) : Prop :=
  Relation.ReflTransGen (fun a b => Reduces R a b) x y



lemma ReducesStar_iff_ReducesStar'
    {α : Type} {R : ARS α} {x y : α} :
    ReducesStar R x y ↔
      ReducesStar' R x y := by
  sorry


theorem IsConfluent_iff_IsChurchRosser
    {α : Type} (R : ARS α) :
    IsConfluent R ↔ IsChurchRosser R := by
  constructor
  · intro hconf
    intro x y hxy
    -- Precisamos provar que x e y são joináveis.
    -- Usamos confluência com x →* y e x →* x.
    have hxx : ReducesStar R x x := by
      rw [ReducesStar, ARS.reflTransClosure]
      right
      rw [ARS.id]
      simp

    exact hconf x y x hxy hxx

  · intro hcr
    intro x y z hxy hxz
    -- Pela transitividade, y →* x e z →* x seriam necessários,
    -- mas temos apenas x →* y e x →* z.
    --
    -- Church-Rosser será aplicado a uma sequência x →* y
    -- e, depois, precisamos usar a equivalência entre os caminhos.
    sorry
