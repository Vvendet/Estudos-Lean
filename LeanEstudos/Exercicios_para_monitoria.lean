theorem ex01 {P Q R : Prop} : (P → Q) → (Q → R) → (P → R) := by
  intro hPQ hQR P
  have Q: Q := by
    apply hPQ
    exact P
  apply hQR
  exact Q

theorem ex02 {P Q: Prop} : (P → Q) → (P → Q) := by
  intro hPQ
  exact hPQ

theorem ex03 {P Q R: Prop} :
    (P → Q → R) → (P → Q) → (P → R) := by
  intro hPQR hPQ P
  have Q: Q := by
    apply hPQ
    exact P
  apply hPQR
  exact P
  exact Q

theorem ex05 {P Q: Prop} : (P ∧ Q) → P := by
  intro h
  exact h.left

theorem ex06 {P Q: Prop} : (P ∧ Q) → Q := by
  intro h
  exact h.right

theorem ex07 {P Q: Prop} : P → Q → (P ∧ Q) := by
  intro P Q
  constructor
  · exact P
  · exact Q

theorem ex08 {P Q R: Prop} :
    (P → Q) → (P → R) → (P → Q ∧ R) := by
  intro hPQ hPR P
  have Q: Q:= by
    apply hPQ
    exact P
  have R: R:= by
    apply hPR
    exact P
  constructor
  · exact Q
  · exact R

theorem ex09 {P Q: Prop} : P → P ∨ Q := by
  intro P
  constructor
  exact P

theorem ex10 {Q P: Prop} : Q → P ∨ Q := by
  intro Q
  exact Or.inr Q


-----------------------------
theorem ex11 {P R Q: Prop} :
    (P → R) → (Q → R) → (P ∨ Q → R) := by
  intro hPR hQR P_or_Q
  exact Or.elim P_or_Q hPR hQR

theorem ex12 {P Q R: Prop} :
    ((P ∧ Q) ∨ R) → ((P ∨ R) ∧ (Q ∨ R)) := by
  intro P_and_Q_or_R
  exact and_or_right.mp P_and_Q_or_R
-------------------------------

theorem ex13 {P:Prop} : P → ¬¬P := by
  intro P hNP
  exact hNP P

theorem ex14 {P Q: Prop} : (P → Q) → (¬Q → ¬P) := by
  intro hPQ hNQ P
  apply hNQ
  apply hPQ
  exact P

theorem ex15 {P Q: Prop} : ¬(P ∨ Q) → (¬P ∧ ¬Q) := by
  intro h
  constructor
  · intro P
    exact h (Or.inl P)

  · intro Q
    exact h (Or.inr Q)

theorem ex16 {P Q: Prop} : (P → Q) → (¬P ∨ Q) := by
  intro hPQ
  by_cases P: P
  · right
    apply hPQ
    exact P
  · left
    exact P
