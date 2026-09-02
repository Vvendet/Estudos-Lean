import LeanEstudos.Formalismos_Daniele.aula3_anexo


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
  Partial_Order R ∧ ∀ x y, (R x y ∨ x = y ∨  R y x)

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

-- Todas as ordens parciais são assimétricas
lemma Partial_Order.asymmetric {α : Type} {R : α → α → Prop} (h : Partial_Order R) :
  ∀ x y, R x y → ¬ R y x := by
  intro x y hxy hyx
  have hcycle : R x x := by
    have htrans := h.2 x y x hxy hyx
    exact htrans
  exact h.1 x hcycle

lemma Total_Order.partial_order {α : Type} {R : α → α → Prop} (h : Total_Order R) :
  Partial_Order R := h.1



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

-- a) De Ordem Parcial Estrita para Ordem Parcial Reflexiva
def StrictToReflexive {α : Type} (R : α → α → Prop) : α → α → Prop :=
  fun a b => R a b ∨ a = b

lemma PartialOrder_to_ReflexivePartialOrder {α : Type} (R : α → α → Prop) (h : Partial_Order R) :
  Reflexive_Partial_Order (StrictToReflexive R) := by
  constructor
  · -- Quasi_Order (Reflexiva e Transitiva)
    constructor
    · -- Reflexiva
      intro x
      right
      exact rfl
    · -- Transitiva
      intro x y z hxy hyz
      rcases hxy with hxy | rfl
      · rcases hyz with hyz | rfl
        · left
          exact h.2 x y z hxy hyz
        · left
          exact hxy
      · exact hyz
  · -- Anti_Symmetric
    intro x y hxy hyx
    rcases hxy with hxy | rfl
    · rcases hyx with hyx | rfl
      · -- Se R x y e R y x, a transitividade gera R x x (contradizendo a irreflexividade)
        exfalso
        have hxx : R x x := h.2 x y x hxy hyx
        exact h.1 x hxx
      · rfl
    · rfl


-- b) De Ordem Parcial Reflexiva para Ordem Parcial Estrita
def ReflexiveToStrict {α : Type} (R : α → α → Prop) : α → α → Prop :=
  fun a b => R a b ∧ a ≠ b

lemma ReflexivePartialOrder_to_PartialOrder {α : Type} (R : α → α → Prop)
(h : Reflexive_Partial_Order R) :
  Partial_Order (ReflexiveToStrict R) := by
  constructor
  · -- Irreflexiva
    intro x hxx
    exact hxx.2 rfl
  · -- Transitiva
    intro x y z hxy hyz
    constructor
    · exact h.1.2 x y z hxy.1 hyz.1
    · intro hxz
      -- Se x = z, reescrevemos x por z nas hipóteses
      rw [hxz] at hxy
      -- Pela antissimetria, R z y e R y z implica z = y
      have heq : z = y := h.2 z y hxy.1 hyz.1
      -- Contradição com a restrição z ≠ y
      exact hxy.2 heq


-- c) De Quase-Ordem para Ordem Parcial Estrita (Corrigido via assimetria)
def QuasiToStrict {α : Type} (R : α → α → Prop) : α → α → Prop :=
  fun a b => R a b ∧ ¬(R b a)

lemma QuasiOrder_to_PartialOrder {α : Type} (R : α → α → Prop) (h : Quasi_Order R) :
  Partial_Order (QuasiToStrict R) := by
  constructor
  · -- Irreflexiva
    intro x hxx
    exact hxx.2 hxx.1
  · -- Transitiva
    intro x y z hxy hyz
    constructor
    · exact h.2 x y z hxy.1 hyz.1
    · intro hzx
      -- Se R z x, usando R x y e a transitividade, teríamos R z y
      have hzy : R z y := h.2 z x y hzx hxy.1
      -- Contradição com a restrição ¬R z y que vem de hyz
      exact hyz.2 hzy

-- ---------------------------------------------------------
-- PRODUTO LEXICOGRÁFICO
-- ---------------------------------------------------------

/-- Definição de Ordem Lexicográfica sobre um produto de tipos -/
def Lexicographic_Order {α β : Type} (Ra : α → α → Prop) (Rb : β → β → Prop) :
(α × β) → (α × β) → Prop :=
  fun p1 p2 => Ra p1.1 p2.1 ∨ (p1.1 = p2.1 ∧ Rb p1.2 p2.2)

/-- Lema: O produto lexicográfico de ordens parciais é uma ordem parcial -/
lemma Lexicographic_Order_PartialOrder {α β : Type} {Ra : α → α → Prop} {Rb : β → β → Prop}
  (ha : Partial_Order Ra) (hb : Partial_Order Rb) : Partial_Order (Lexicographic_Order Ra Rb) := by
  constructor
  · -- Irreflexividade
    intro p hp
    unfold Lexicographic_Order at hp
    rcases hp with h1 | ⟨heq, h2⟩
    · exact ha.1 p.1 h1
    · exact hb.1 p.2 h2
  · -- Transitividade
    intro p1 p2 p3 h12 h23
    unfold Lexicographic_Order at h12 h23 ⊢
    rcases h12 with ha12 | ⟨heq12, hb12⟩
    · rcases h23 with ha23 | ⟨heq23, _⟩
      · left; exact ha.2 p1.1 p2.1 p3.1 ha12 ha23
      · left; rw [heq23] at ha12; exact ha12
    · rcases h23 with ha23 | ⟨heq23, hb23⟩
      · left; rw [← heq12] at ha23; exact ha23
      · right
        constructor
        · exact Eq.trans heq12 heq23
        · exact hb.2 p1.2 p2.2 p3.2 hb12 hb23

lemma Lexicographic_Order_TotalOrder {α β : Type} {Ra : α → α → Prop} {Rb : β → β → Prop}
  (ha : Total_Order Ra) (hb : Total_Order Rb) : Total_Order (Lexicographic_Order Ra Rb) := by
  constructor
  · exact Lexicographic_Order_PartialOrder ha.1 hb.1
  · intro p1 p2
    -- Analisamos a tricotomia na primeira componente
    rcases ha.2 p1.1 p2.1 with h1 | h1_eq | h1_rev
    · left
      left
      exact h1
    · -- Se as primeiras componentes são iguais, analisamos a segunda
      rcases hb.2 p1.2 p2.2 with h2 | h2_eq | h2_rev
      · left
        right
        exact ⟨h1_eq, h2⟩
      · right
        left
        -- Usa Prod.ext para provar a igualdade no tipo produto
        apply Prod.ext
        · exact h1_eq
        · exact h2_eq
      · right
        right
        right
        exact ⟨h1_eq.symm, h2_rev⟩
    · right
      right
      left
      exact h1_rev

lemma Lexicographic_Order_WellFounded {α β : Type} {Ra : α → α → Prop} {Rb : β → β → Prop}
  (hwa : WellFounded Ra) (hwb : WellFounded Rb) : WellFounded (Lexicographic_Order Ra Rb) := by
  constructor
  -- Um elemento do produto é acessível se todas as suas reduções forem acessíveis
  intro ⟨a, b⟩
  revert b
  -- Indução na primeira componente baseada na boa-fundação de Ra
  induction a using hwa.induction with
  | h a iha =>
    intro b
    -- Indução na segunda componente baseada na boa-fundação de Rb
    induction b using hwb.induction with
    | h b ihb =>
      apply Acc.intro
      intro ⟨a', b'⟩ hp
      unfold Lexicographic_Order at hp
      rcases hp with h_ra | ⟨h_eq, h_rb⟩
      · -- Caso Ra a' a: usamos a hipótese de indução iha
        exact iha a' h_ra b'
      · -- Caso a' = a e Rb b' b: substituímos a igualdade e usamos ihb
        subst h_eq
        exact ihb b' h_rb

-- Uma regra de reescrita é um par de palavras
abbrev Rule (α : Type) := List α × List α

-- Um Sistema de Reescrita de Palavras (Semi-Thue System) é um conjunto de regras
abbrev SRS (α : Type) := Set (Rule α)

-- Agora a notação de pertinência (∈) funcionará perfeitamente:
def WordReduces {α : Type} (R : SRS α) (u v : List α) : Prop :=
  ∃ (l r x y : List α),
    (l, r) ∈ R ∧
    u = x ++ l ++ y ∧
    v = x ++ r ++ y

-- Conectando a infraestrutura concreta de palavras com a teoria abstrata de ARS:
-- Podemos instanciar um Sistema Abstrato de Redução cujos elementos são List α
def SRS_to_ARS {α : Type} (R : SRS α) : ARS (List α) where
  red := { p | WordReduces R p.1 p.2 }

lemma WordReduces_context
    {α : Type} (R : SRS α) (u v prefix_word suffix_word : List α)
    (h : WordReduces R u v) :
    WordReduces R (prefix_word ++ u ++ suffix_word) (prefix_word ++ v ++ suffix_word) := by
  -- Desestruturamos a hipótese h para extrair a regra e os contextos originais (x e y)
  rcases h with ⟨l, r, x, y, h_rule, hu, hv⟩
  -- Propomos a mesma regra (l, r), mas com os novos contextos expandidos
  refine ⟨l, r, prefix_word ++ x, y ++ suffix_word, h_rule, ?_, ?_⟩
  · -- Substituímos u pela sua definição original
    rw [hu]
    -- A tática simp aplica automaticamente a associatividade do List.append
    simp
  · -- Substituímos v pela sua definição original
    rw [hv]
    -- A tática simp normaliza os agrupamentos da concatenação
    simp
