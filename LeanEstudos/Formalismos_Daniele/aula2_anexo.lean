import LeanEstudos.Formalismos_Daniele.aula3
import Mathlib.Tactic.WLOG

def ARS.Acyclic {α : Type} (R : ARS α) : Prop :=
  ∀ x, ¬ Relation.TransGen (Reduces R) x x


def ARS.Acyclic' {α : Type} (R : ARS α) : Prop :=
  ∀ x, ¬ Relation.TransGen (fun a b => Reduces R a b) x x

lemma ARS.Acyclic_iff_ARS.Acyclic' {α : Type} (R : ARS α) :
  ARS.Acyclic R ↔ ARS.Acyclic' R := by
  simp [ARS.Acyclic, ARS.Acyclic']

#check Nat.exists_eq_add_of_lt

lemma infinite_reduction_injective_of_acyclic
    {α : Type} {R : ARS α}
    (hacyclic : ARS.Acyclic R)
    {f : Nat → α}
    (hred : ∀ n, Reduces R (f n) (f (n + 1))) :
    Function.Injective f := by
  intro i j hij
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hij' | hji'
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hij'
    have htrans' : ∀ m, Relation.TransGen (Reduces R) (f i) (f (i + m + 1)) := by
      intro m
      induction m with
      | zero =>
          simpa using Relation.TransGen.single (hred i)
      | succ m ih =>
          have hstep :
              Reduces R (f (i + m + 1)) (f (i + m + 2)) := by
            simpa [Nat.add_assoc] using hred (i + m + 1)
          simpa [Nat.add_assoc] using
            (Relation.TransGen.tail ih hstep)
    have htrans : Relation.TransGen (Reduces R) (f i) (f (i + k + 1)) := htrans' k
    have hEq : f (i + k + 1) = f i := by
      simpa [hk] using hij.symm
    have hcycle :
        Relation.TransGen (Reduces R) (f i) (f i) := by
      simpa [hEq] using htrans
    exact hacyclic (f i) hcycle
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hji'
    have htrans' : ∀ m, Relation.TransGen (Reduces R) (f j) (f (j + m + 1)) := by
      intro m
      induction m with
      | zero =>
          simpa using Relation.TransGen.single (hred j)
      | succ m ih =>
          have hstep :
              Reduces R (f (j + m + 1)) (f (j + m + 2)) := by
            simpa [Nat.add_assoc] using hred (j + m + 1)
          simpa [Nat.add_assoc] using
            (Relation.TransGen.tail ih hstep)
    have htrans : Relation.TransGen (Reduces R) (f j) (f (j + k + 1)) := htrans' k
    have hEq : f (j + k + 1) = f j := by
      simpa [hk] using hij
    have hcycle :
        Relation.TransGen (Reduces R) (f j) (f j) := by
      simpa [hEq] using htrans
    exact hacyclic (f j) hcycle

theorem finite_ReductionTree_of_acyclic_finitelyBranching_to_StronglyNormalizing
    {α : Type} (R : ARS α)
    (hacyclic : ARS.Acyclic R)
    (htrees : ∀ a, Set.Finite (ARS.ReductionTree R a)) :
    StronglyNormalizing R := by
  intro hnot
  rcases hnot with ⟨f, hf⟩
  have hinj :
      Function.Injective f :=
    infinite_reduction_injective_of_acyclic hacyclic hf
  have htree :
      Set.Infinite (ARS.ReductionTree R (f 0)) := by
    exact infinite_ReductionTree_of_infinite_reduction
      f rfl hf
  exact (htrees (f 0)).not_infinite htree
