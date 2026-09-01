import LeanEstudos.Formalismos_Daniele.aula2_anexo

-- definitions of irreflexive relation, transitive relation, partial orders, total orders,
-- reflexive relation, quasi-orders, anti-symmetric relations and reflexive partial order

def Relation.Irreflexive {α : Type} (R : α → α → Prop) : Prop :=
  ∀ x, ¬ R x x

def Relation.Reflexive {α : Type} (R : α → α → Prop) : Prop :=
  ∀ x, R x x

def Relation.Transitive {α : Type} (R : α → α → Prop) : Prop :=
  ∀ x y z, R x y → R y z → R x z

def Partial_Order {α : Type} (R : α → α → Prop) : Prop :=
  Relation.Irreflexive R ∧ Relation.Transitive R

def Total_Order {α : Type} (R : α → α → Prop) : Prop :=
  Partial_Order R ∧ ∀ x y, (R x y ∨ R y x)

def Quasi_Order {α : Type} (R : α → α → Prop) : Prop :=
  Relation.Reflexive R ∧ Relation.Transitive R

def Anti_Symmetric {α : Type} (R : α → α → Prop) : Prop :=
  ∀ x y, R x y → R y x → x = y

def Reflexive_Partial_Order {α : Type} (R : α → α → Prop) : Prop :=
  Quasi_Order R ∧ Anti_Symmetric R

-- Definition of acyclic relation

def Relation.Acyclic {α : Type} (R : α → α → Prop) : Prop :=
  ∀ x, ¬ Relation.TransGen R x x

-- section of fast lemmas:
-- all of partial orders is anti-symmetric, all of total orders is a partial order,
-- all of total orders is a quasi-order, all of reflexive partial orders is a quasi-order
-- transitive closure of a relation is a partial order iff the relation is acyclic.

lemma Partial_Order.anti_symmetric {α : Type} {R : α → α → Prop} (h : Partial_Order R) :
  Anti_Symmetric R := by
  intro x y hxy hyx
  by_contra hne
  have hcycle : R x x := by
    have htrans := h.2 x y x hxy hyx
    exact htrans
  exact h.1 x hcycle

lemma Total_Order.partial_order {α : Type} {R : α → α → Prop} (h : Total_Order R) :
  Partial_Order R := h.1

lemma Total_Order.quasi_order {α : Type} {R : α → α → Prop} (h : Total_Order R) :
  Quasi_Order R := by
  constructor
  · intro x
    have htotal := h.2 x x
    cases htotal with
    | inl hxx => exact hxx
    | inr hxx => exact hxx
  · exact h.partial_order.2

lemma Reflexive_Partial_Order.quasi_order {α : Type} {R : α → α → Prop}
 (h : Reflexive_Partial_Order R) :
  Quasi_Order R := h.1


lemma Relation.TransGen.partial_order_iff_acyclic {α : Type} {R : α → α → Prop} :
  Partial_Order (Relation.TransGen R) ↔ Relation.Acyclic R := by
  constructor
  · contrapose
    intro hacyclic
    unfold Relation.Acyclic at hacyclic
    push Not at hacyclic
    unfold Partial_Order
    have hnoirreflexive : ¬Relation.Irreflexive (Relation.TransGen R) := by
      intro hIrref
      obtain ⟨x, hcycle⟩ := hacyclic
      exact hIrref x hcycle
    intro ⟨h1, h2⟩
    exact hnoirreflexive h1
  · intro hacyclic
    unfold Partial_Order
    constructor
    · have hirreflexive : Relation.Irreflexive (Relation.TransGen R) := by
        intro x hcycle
        have htrans := hacyclic x
        exact htrans hcycle
      exact hirreflexive
    · have htransitive : Relation.Transitive (Relation.TransGen R) := by
        intro x y z hxy hyz
        exact Relation.TransGen.trans hxy hyz
      exact htransitive
