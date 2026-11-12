/-
  ══════════════════════════════════════════════════════════════════
   LÓGICA MATEMÁTICA E COMPUTACIONAL — Laboratório 1
   Dedução Natural para Lógica Proposicional em Lean 4
  ══════════════════════════════════════════════════════════════════

  COMO USAR
  ---------
  1. Abra https://live.lean-lang.org e cole este arquivo inteiro no editor.
  2. O painel da direita ("Lean Infoview") mostra o ESTADO DA PROVA:
     as hipóteses disponíveis (acima de ⊢) e o OBJETIVO (depois de ⊢).
  3. Clique dentro de uma prova e mova o cursor linha a linha para ver
     como cada comando transforma o objetivo.
  4. Cada exercício termina em `sorry` ("desculpe, ainda não provei").
     Substitua o `sorry` pela sua prova. Quando a prova estiver completa,
     o sublinhado amarelo some e não há mensagens de erro.

  DIGITANDO SÍMBOLOS (digite a barra invertida e depois o nome + espaço)
  -----------------------------------------------------------------------
     →   \to  ou  \r          ∧   \and          ∨   \or
     ¬   \not ou  \neg        ↔   \iff          ⟨ ⟩  \<  e  \>
     ⊢   \|-                  ⊥   (em Lean escrevemos `False`)

  TABELA DE REFERÊNCIA: REGRA DE DEDUÇÃO NATURAL  ↦  COMANDO EM LEAN
  -------------------------------------------------------------------
   Regra         | Tática (modo `by`)            | Termo (prova direta)
   --------------|-------------------------------|------------------------
   hipótese      | exact h   /  assumption       | h
   →I            | intro h                       | fun h => ...
   →E  (MP)      | apply h   /  exact h hp       | h hp
   ∧I            | constructor                   | ⟨hp, hq⟩  /  And.intro hp hq
   ∧E₁ , ∧E₂     | exact h.1  ,  exact h.2       | h.left  ,  h.right
                 | obtain ⟨hp, hq⟩ := h          |
   ∨I₁ , ∨I₂     | left  ,  right                | Or.inl hp  ,  Or.inr hq
   ∨E            | cases h with                  | Or.elim h (fun hp => ..) (fun hq => ..)
                 |  | inl hp => ...              |
                 |  | inr hq => ...              |
   ¬I            | intro h   (¬p  é  p → False)  | fun hp => ...
   ¬E            | exact hnp hp                  | hnp hp       (produz False)
   ⊥E            | exfalso   /  contradiction    | False.elim h  /  absurd hp hnp
   ↔I            | constructor                   | ⟨fun .. => .., fun .. => ..⟩
   ↔E            | exact h.mp hp / h.mpr hq      | h.mp  ,  h.mpr
   RAA (clássica)| apply Classical.byContradiction; intro h
   TND (clássica)| exact Classical.em p          | Classical.em p   : p ∨ ¬p

  OBSERVAÇÃO IMPORTANTE
  ---------------------
  Em Lean, `¬p` é apenas uma ABREVIAÇÃO de `p → False`.
  Por isso a introdução da negação (¬I) é feita com `intro`, e a
  eliminação da negação (¬E) é só uma aplicação de função (→E).
-/

-- Nossas variáveis proposicionais (letras sentenciais).
variable (p q r s : Prop)


/-
  ════════════════════════════════════════════
   PARTE 0 — Exemplos resolvidos (leia e explore)
  ════════════════════════════════════════════
-/

-- Exemplo 0.1  (→I e hipótese)
--   [p]¹
--   ───── →I¹
--   p → p
example : p → p := by
  intro hp      -- →I : supomos p e o chamamos de hp
  exact hp      -- o objetivo é exatamente uma hipótese

-- Exemplo 0.2  (→E, modus ponens)
example (hpq : p → q) (hp : p) : q := by
  apply hpq     -- "para obter q, basta obter p" (raciocínio de trás para frente)
  exact hp

-- O mesmo exemplo em uma linha, como TERMO (prova = programa!):
example (hpq : p → q) (hp : p) : q := hpq hp

-- Exemplo 0.3  (∧I e ∧E)
example (h : p ∧ q) : q ∧ p := by
  constructor   -- ∧I : gera dois objetivos, q e p
  · exact h.2   -- ∧E₂
  · exact h.1   -- ∧E₁

-- Exemplo 0.4  (∨I e ∨E)
example (h : p ∨ q) : q ∨ p := by
  cases h with
  | inl hp =>   -- caso 1: temos p
    right       -- ∨I₂ : vamos provar o lado direito de q ∨ p
    exact hp
  | inr hq =>   -- caso 2: temos q
    left        -- ∨I₁
    exact hq

-- Exemplo 0.5  (¬I e ¬E)
example (hp : p) : ¬¬p := by
  intro hnp     -- ¬I : ¬¬p é (¬p → False); supomos ¬p
  exact hnp hp  -- ¬E : de ¬p e p obtemos False


/-
  ════════════════════════════════════════════
   PARTE 1 — Implicação  (intro, exact, apply)
  ════════════════════════════════════════════
-/

-- Exercício 1.1
example : p → q → p := by
  intro P Q
  exact P

-- Exercício 1.2  (silogismo hipotético)
example : (p → q) → (q → r) → p → r := by
  intro hPQ hQR P
  apply hQR
  apply hPQ
  exact P

-- Exercício 1.3
example : (p → q → r) → (p → q) → p → r := by
  intro hPQR hPQ P
  apply hPQR
  have Q: q:= by
    apply hPQ
    exact P
  exact P
  apply hPQ
  exact P


-- Exercício 1.4  (troca de premissas)
example : (p → q → r) → (q → p → r) := by
  intro hPQR Q P
  apply hPQR
  exact P
  exact Q


/-
  ════════════════════════════════════════════
   PARTE 2 — Conjunção  (constructor, .1, .2, obtain)
  ════════════════════════════════════════════
-/

-- Exercício 2.1
example : p ∧ q → q ∧ p := by
  intro h
  constructor
  · exact h.2
  · exact h.1

-- Exercício 2.2  (associatividade)
example : p ∧ (q ∧ r) → (p ∧ q) ∧ r := by
  intro h
  constructor
  · constructor
    · exact h.1
    · exact h.2.1
  · exact h.2.2

-- Exercício 2.3
example : (p → q) ∧ (p → r) → p → q ∧ r := by
  intro h1 p
  constructor
  · apply h1.1
    exact p
  · apply h1.2
    exact p

-- Exercício 2.4  ("currying")
example : (p ∧ q → r) → p → q → r := by
  intro h1 p q
  apply h1
  constructor
  · exact p
  · exact q

-- Exercício 2.5  ("uncurrying")
example : (p → q → r) → p ∧ q → r := by
  intro h1 h2
  apply h1
  exact h2.1
  exact h2.2

/-
  ════════════════════════════════════════════
   PARTE 3 — Disjunção  (left, right, cases)
  ════════════════════════════════════════════
-/

-- Exercício 3.1
example : p → p ∨ q := by
  intro p
  exact Or.inl p

-- Exercício 3.2
example : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp =>
    exact Or.inr hp
  | inr hq =>
    exact Or.inl hq

-- Exercício 3.3  (prova por casos)
example : (p → r) → (q → r) → p ∨ q → r := by
  intro h1 h2 h3
  cases h3 with
  | inl p =>
    apply h1
    exact p
  | inr q =>
    apply h2
    exact q

-- Exercício 3.4  (distributividade)
example : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro h1
  cases h1.2 with
  |inl q =>
    left
    constructor
    · exact h1.1
    · exact q
  |inr r =>
    right
    constructor
    · exact h1.1
    · exact r

-- Exercício 3.5  (dilema construtivo)
example : (p → q) → (r → s) → p ∨ r → q ∨ s := by
  intro h1 h2 h3
  cases h3 with
  | inl p =>
    left
    apply h1
    exact p
  |inr r =>
    right
    apply h2
    exact r


/-
  ════════════════════════════════════════════
   PARTE 4 — Negação e Absurdo  (intro, exfalso, contradiction)
  ════════════════════════════════════════════
-/

-- Exercício 4.1  (ex falso quodlibet, ⊥E)
example : False → p := by
  intro h
  exfalso
  exact h

-- Exercício 4.2  (modus tollens)
example : (p → q) → ¬q → ¬p := by
  intro h1 nq p
  have q: q := by
    apply h1
    exact p
  exact nq q

-- Exercício 4.3  (não-contradição)
example : ¬(p ∧ ¬p) := by
  intro p
  exact p.2 p.1

-- Exercício 4.4  (silogismo disjuntivo)
example : p ∨ q → ¬p → q := by
  intro h np
  cases h with
  |inl p =>
    have False: False := by exact np p
    contradiction
  |inr q =>
    exact q

-- Exercício 4.5  (De Morgan — a direção intuicionista)
example : ¬(p ∨ q) → ¬p ∧ ¬q := by
  intro h
  constructor
  · intro hp
    have h1: p ∨ q:=by
      exact Or.inl hp
    exact h h1
  · intro hq
    have h1: p ∨ q := by exact Or.inr hq
    exact h h1


-- Exercício 4.6  (De Morgan — outra direção intuicionista)
example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intro h1 h2
  cases h1 with
  | inl np =>
    exact np h2.1
  | inr nq =>
    exact nq h2.2

-- Exercício 4.7
example : ¬¬¬p → ¬p := by
  intro nnnp hp
  have nnp: ¬¬p := by
    intro np
    exact np hp
  exact nnnp nnp



/-
  ════════════════════════════════════════════
   PARTE 5 — Bicondicional  (constructor, .mp, .mpr)
  ════════════════════════════════════════════
-/

-- Exercício 5.1
example : p ∧ q ↔ q ∧ p := by
  constructor
  · intro h1
    constructor
    · exact h1.2
    · exact h1.1
  · intro h1
    constructor
    · exact h1.2
    · exact h1.1

-- Exercício 5.2
example : (p → q ∧ r) ↔ (p → q) ∧ (p → r) := by
  constructor
  · intro h
    constructor
    · intro hp
      exact (h hp).1
    · intro hp
      exact (h hp).2
  · intro h1 hp
    constructor
    · exact h1.1 hp
    · exact h1.2 hp

-- Exercício 5.3
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  constructor
  ·
    intro h
    constructor
    · intro hp
      have h1: p ∨ q:= by exact Or.inl hp
      exact h h1
    · intro hq
      have h1: p ∨ q:= by exact Or.inr hq
      exact h h1
  · intro h
    intro h1
    cases h1 with
    | inl hp =>
      exact h.1 hp
    | inr hq =>
      exact h.2 hq

/-
  ════════════════════════════════════════════
   PARTE 6 — Lógica Clássica  (RAA e Terceiro Excluído)
  ════════════════════════════════════════════

  Tudo o que fizemos até aqui é válido na lógica INTUICIONISTA.
  As provas abaixo precisam de um princípio clássico:

    • Redução ao absurdo (RAA):
        apply Classical.byContradiction
        intro h          -- h : ¬(objetivo)
        ...              -- agora prove False

    • Terceiro excluído (TND):
        cases Classical.em p with
        | inl hp  => ...
        | inr hnp => ...
-/

-- Exercício 6.1  (eliminação da dupla negação)
example : ¬¬p → p := by
  intro nnp
  by_cases hp: p
  exact hp
  have False: False := by exact nnp hp
  contradiction

-- Exercício 6.2  (prove o TND usando apenas RAA, sem Classical.em!)
example : p ∨ ¬p := by
  apply Classical.byContradiction
  intro h
  apply h
  right
  intro hp
  have h1: p ∨ ¬p := by exact Or.inl hp
  exact h h1


-- Exercício 6.3  (contraposição, direção clássica)
example : (¬q → ¬p) → p → q := by
  intro h hp
  by_cases hq: q
  exact hq
  have np: ¬p := by
    apply h
    exact hq
  have False: False:= by exact np hp
  contradiction

-- Exercício 6.4  (De Morgan — a direção clássica)
example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro h
  by_cases hp : p
  · right
    intro hq
    apply h
    exact ⟨hp, hq⟩
  · left
    exact hp

-- ★ Desafio 6.5  (Lei de Peirce)
example : ((p → q) → p) → p := by
  intro h
  by_cases hp: p
  exact hp
  apply h
  intro hp_
  have False : False := by
    exact hp hp_
  contradiction




/-
  ════════════════════════════════════════════
   PARTE 7 (opcional) — Provas como termos
  ════════════════════════════════════════════

  Reescreva SEM `by`, apenas com fun, ⟨_, _⟩, .1, .2, Or.inl, Or.inr,
  Or.elim, aplicação de função e False.elim.
-/

example : p → q → p := sorry

example : p ∧ q → q ∧ p := sorry

example : (p → q) → ¬q → ¬p := sorry

example : p ∨ q → q ∨ p := sorry
