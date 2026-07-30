import Mathlib

/-!
# A computable definition of the numbers `d_q(n)`

This file formalizes the definition from the supplied paper.  Everything is represented by
finite data, so `NFA.vcDimension q n` is executable and propositions about concrete values
can be proved by computation.
-/

namespace BinaryNFA

/-- A binary word of length `n`.  The letter in position `i` is `w i`. -/
abbrev Word (n : ℕ) := Fin n → Bool

/-- A `q`-state nondeterministic finite automaton over the binary alphabet, with one
specified initial state and one specified accepting state.
The Boolean value `transition s b t` says whether there is a transition from `s` to `t`
labelled by `b`.
-/
structure Automaton (q : ℕ) where
  transition : Fin q → Bool → Fin q → Bool
  initial : Fin q
  accepting : Fin q
deriving DecidableEq, Fintype

/-- The set of states reachable in one step. -/
def step {q : ℕ} (A : Automaton q) (states : Finset (Fin q)) (b : Bool) : Finset (Fin q) :=
    Finset.univ.filter fun t => ∃ s ∈ states, A.transition s b t = true

/-- The states reachable after reading `w`, starting at the unique initial state. -/
def reachable {q n : ℕ} (A : Automaton q) (w : Word n) : Finset (Fin q) :=
    (List.ofFn w).foldl (step A) {A.initial}

/-- Whether an automaton accepts a word. -/
def accepts {q n : ℕ} (A : Automaton q) (w : Word n) : Bool :=
    A.accepting ∈ reachable A w

/-- The trace on `S` of the language accepted by `A`. -/
def trace {q n : ℕ} (A : Automaton q) (S : Finset (Word n)) : Finset (Word n) :=
    S.filter fun w => accepts A w

/-- A finite set of length-`n` words is shattered by the languages of `q`-state NFAs. -/
def Shattered (q n : ℕ) (S : Finset (Word n)) : Prop :=
    ∀ T : Finset (Word n), T ⊆ S → ∃ A : Automaton q, trace A S = T

instance shatteredDecidable (q n : ℕ) (S : Finset (Word n)) : Decidable (Shattered q n S) := by
  unfold Shattered
  infer_instance

/-- `d_q(n)`: the VC dimension of the family of length-`n` slices of languages accepted
by `q`-state NFAs with one initial and one accepting state.
This is a finite supremum rather than a noncomputable mathematical maximum.  Consequently
Lean can evaluate it for small concrete inputs.
-/
def vcDimension (q n : ℕ) : ℕ := (Finset.univ.filter (Shattered q n)).sup Finset.card

/-- A small test requested in the question.  `decide` evaluates the finite search
with compiled code, by the ordinary kernel evaluator. -/
example : vcDimension 2 2 = 4 := by
  set_option maxRecDepth 100000 in
  decide

-- #eval [vcDimension 1 0, vcDimension 1 1, vcDimension 1 2, vcDimension 1 3]
-- #eval [vcDimension 2 0, vcDimension 2 1, vcDimension 2 2, vcDimension 2 3]
-- #eval vcDimension 3 0
-- #eval vcDimension 3 1
-- #eval vcDimension 3 2
-- #eval vcDimension 3 3
-- #eval vcDimension 3 4
-- #eval vcDimension 3 5
end BinaryNFA
