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
  constructor
  · intro h
    rw [ReducesStar, ARS.reflTransClosure] at h
    rw [ReducesStar']
    rcases h with h | h
    · -- Caso x →⁺ y
      rw [ARS.transitiveClosure] at h
      rcases Set.mem_iUnion.mp h with ⟨⟨n, hn_pos⟩, hn⟩
      have hpow :
          ∀ m {x y : α},
            (x, y) ∈ Reduces.pow R (m + 1) →
            Relation.ReflTransGen (fun a b => Reduces R a b) x y := by
        intro m
        induction m with
        | zero =>
            intro x y hxy
            rw [Reduces.pow] at hxy
            rcases hxy with ⟨z, hxz, hzy⟩
            rw [Reduces.pow, ARS.id] at hxz
            rcases hxz with ⟨a, ha, haxz⟩
            have hax : a = x := congrArg Prod.fst haxz
            have haz : a = z := congrArg Prod.snd haxz
            subst x
            subst z
            exact Relation.ReflTransGen.single hzy
        | succ m ih =>
            intro x y hxy
            rw [Reduces.pow] at hxy
            rcases hxy with ⟨z, hxz, hzy⟩
            exact Relation.ReflTransGen.tail (ih hxz) hzy
      have hn_eq : n - 1 + 1 = n := by omega
      apply hpow (n - 1)
      rw [hn_eq]
      exact hn
    · --Caso x = y ou x -> y
      rw [ARS.id] at h
      rcases h with ⟨a, ha, hxy⟩
      have hax : a = x := congrArg Prod.fst hxy
      have hay : a = y := congrArg Prod.snd hxy
      subst x
      subst y
      exact Relation.ReflTransGen.refl
  · intro h
    rw [ReducesStar'] at h
    induction h with
    | refl =>
        rw [ReducesStar, ARS.reflTransClosure]
        right
        rw [ARS.id]
        exact ⟨x, Set.mem_univ x, rfl⟩
    | @tail a b c hbc ih =>
        rw [ReducesStar, ARS.reflTransClosure]
        rw [ReducesStar, ARS.reflTransClosure] at ih
        rw [ARS.id] at ih
        rcases ih with ih | ih
        · -- a →⁺ b
          left
          rw [ARS.transitiveClosure] at ih
          rcases Set.mem_iUnion.mp ih with ⟨n, hn⟩
          refine Set.mem_iUnion.mpr ⟨⟨n.val + 1, by omega⟩, ?_⟩
          rw [Reduces.pow]
          exact ⟨a, hn, hbc⟩
        · -- a = b
          have hxa : x = a := by
            simpa [ARS.id] using ih
          subst a
          left
          rw [ARS.transitiveClosure]
          refine Set.mem_iUnion.mpr ⟨⟨1, by omega⟩, ?_⟩
          rw [Reduces.pow]
          refine ⟨x, ?_, hbc⟩
          change (x, x) ∈ Reduces.pow R 0
          rw [Reduces.pow, ARS.id]
          exact ⟨x, Set.mem_univ _, rfl⟩



theorem IsConfluent_iff_IsChurchRosser
    {α : Type} (R : ARS α) :
    IsConfluent R ↔ IsChurchRosser R := by
  constructor
  · intro hconf
    intro x y hxy
    change Relation.EqvGen (fun a b => Reduces R a b) x y at hxy
    refine Relation.EqvGen.rec
      (motive := fun x y _ => IsJoinable R x y)
      ?_ ?_ ?_ ?_ hxy
    · -- Caso x → y
      intro x y h
      refine ⟨y, ?_, ?_⟩

      · rw [ReducesStar_iff_ReducesStar']
        exact Relation.ReflTransGen.single h

      · rw [ReducesStar_iff_ReducesStar']
        exact Relation.ReflTransGen.refl
    · -- Caso x = x
      intro x
      refine ⟨x, ?_, ?_⟩

      · rw [ReducesStar_iff_ReducesStar']
        exact Relation.ReflTransGen.refl

      · rw [ReducesStar_iff_ReducesStar']
        exact Relation.ReflTransGen.refl

    · -- Caso de simetria
      intro x y hxy ih
      rcases ih with ⟨w, hxw, hyw⟩
      exact ⟨w, hyw, hxw⟩

    · -- Caso de transitividade
      intro x y z hxy hyz ihxy ihyz

      rcases ihxy with ⟨u, hxu, hyu⟩
      rcases ihyz with ⟨v, hyv, hzv⟩

      rcases hconf y u v hyu hyv with ⟨w, huw, hvw⟩

      refine ⟨w, ?_, ?_⟩

      · exact ReducesStar.trans hxu huw

      · exact ReducesStar.trans hzv hvw

  · intro hcr
    intro x y z hxy hxz

    change ∃ w, ReducesStar R y w ∧ ReducesStar R z w

    have hxy' :
        Relation.ReflTransGen (fun a b => Reduces R a b) x y := by
      change ReducesStar' R x y
      exact ReducesStar_iff_ReducesStar'.mp hxy

    have hxz' :
        Relation.ReflTransGen (fun a b => Reduces R a b) x z := by
      change ReducesStar' R x z
      exact ReducesStar_iff_ReducesStar'.mp hxz

    have hyx_eqv :
        Relation.EqvGen (fun a b => Reduces R a b) y x := by
      have aux :
          ∀ {u v : α},
            Relation.ReflTransGen (fun a b => Reduces R a b) u v →
            Relation.EqvGen (fun a b => Reduces R a b) v u := by
        intro u v huv
        induction huv with
        | refl =>
            exact Relation.EqvGen.refl u

        | tail huv hvw ih =>
            have hwv :
                Relation.EqvGen (fun a b => Reduces R a b) _ _ :=
              Relation.EqvGen.symm _ _
                (Relation.EqvGen.rel _ _ hvw)
            exact Relation.EqvGen.trans hwv ih

      exact aux hxy'

    have hxz_eqv :
        Relation.EqvGen (fun a b => Reduces R a b) x z := by
      have aux :
          ∀ {u v : α},
            Relation.ReflTransGen (fun a b => Reduces R a b) u v →
            Relation.EqvGen (fun a b => Reduces R a b) u v := by
        intro u v huv
        induction huv with
        | refl =>
            exact Relation.EqvGen.refl u

        | tail hab hbc ih =>
            exact Relation.EqvGen.trans
              ih
              (Relation.EqvGen.rel _ _ hbc)

      exact aux hxz'

    have hyz_eqv :
        Relation.EqvGen (fun a b => Reduces R a b) y z :=
      Relation.EqvGen.trans hyx_eqv hxz_eqv

    exact hcr y z hyz_eqv
