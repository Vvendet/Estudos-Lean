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
  | zero =>
      intro x hx
        simp only [ARS.id] using hx
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
  constructor

  · intro h
    rw [ReducesStar, ARS.reflTransClosure] at h

    rcases h with h | h

    ·
      rw [ARS.transitiveClosure] at h
      rcases Set.mem_iUnion.mp h with ⟨n, hn⟩

      induction n.val with
      | zero =>
          have hnpos : 0 < n.val := n.property
          omega
          simp only [hnval, Reduces.pow.eq_def, ARS.id] at hn
          rcases hn with ⟨a, ha, hxy⟩
          have hax : a = x := congrArg Prod.fst hxy
          have hay : a = y := congrArg Prod.snd hxy
          subst x
          subst y
          exact Relation.ReflTransGen.refl

      | succ n ih =>
          rw [Reduces.pow] at hn
          rcases hn with ⟨z, hxz, hzy⟩
          exact Relation.ReflTransGen.tail (ih hxz) hzy

    ·
      rw [ARS.id] at h
      rcases h with ⟨a, ha, hxy⟩
      have hax : a = x := congrArg Prod.fst hxy
      have hay : a = y := congrArg Prod.snd hxy
      subst x
      subst y
      exact Relation.ReflTransGen.refl

  · intro h
    induction h with

    | refl =>
        rw [ReducesStar, ARS.reflTransClosure]
        right
        rw [ARS.id]
        exact ⟨x, Set.mem_univ _, rfl⟩

    | @tail b c d hbc hcd ih =>
        rw [ReducesStar, ARS.reflTransClosure]

        rcases ih with ih | ih

        ·
          right
          rw [ARS.id] at ih
          rcases ih with ⟨a, ha, hac⟩

          have hab : a = b := congrArg Prod.fst hac
          have hbc' : a = c := congrArg Prod.snd hac

          subst b
          subst c

          left
          rw [ARS.transitiveClosure]
          refine Set.mem_iUnion.mpr ⟨⟨1, by omega⟩, ?_⟩

          rw [Reduces.pow, ARS.id]
          exact ⟨x, Set.mem_univ _, rfl⟩

        ·
          left
          rw [ARS.transitiveClosure] at ih
          rcases Set.mem_iUnion.mp ih with ⟨n, hn⟩

          refine Set.mem_iUnion.mpr ⟨⟨n.val + 1, by omega⟩, ?_⟩

          rw [Reduces.pow]
          exact ⟨c, hn, hcd⟩

theorem IsConfluent_iff_IsChurchRosser
    {α : Type} (R : ARS α) :
    IsConfluent R ↔ IsChurchRosser R := by
  constructor
  · intro hconf
    exact Relation.church_rosser hconf

  · intro hcr
    intro x y z hxy hxz
    -- Pela transitividade, y →* x e z →* x seriam necessários,
    -- mas temos apenas x →* y e x →* z.
    --
    -- Church-Rosser será aplicado a uma sequência x →* y
    -- e, depois, precisamos usar a equivalência entre os caminhos.
    rw [IsChurchRosser] at hcr
    unfold IsJoinable at hcr
