import Aesop
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.tactic

set_option linter.unusedVariables false

variable {n : ℕ}

lemma directed_iff (he : Even n) : 2 ∣ n := by exact even_iff_two_dvd.mp he

def prim (p : ℕ) := p > 1 ∧ ∀ m, m ∣ p → m = 1 ∨ m = p
/-
Remarks
- Would be nice to run exact on the premises of a hyp.
  For example here we need `m ∣ p`, so we run exact? to find that
  it follows from `Even p`.
- Should saturate split conjunctions?
- Is there a good way for it to unfolds defs?
- Can we add entire sheets of theorems at all once?
- Something that prevents hyps to be added twice?
-/
example {p : ℕ} (hp : p > 1 ∧ ∀ m, m ∣ p → m = 1 ∨ m = p)
    (h : p > 2) (he : Even p) : False := by
  aesop (add forward safe even_iff_two_dvd)
  --aesop shouldn't aesop work?
  saturate 1 [*]
  simp_all

/-
Remarks
- Need to be able to handle ↔
-/
set_option aesop.dev.statefulForward true in
--set_option trace.profiler true in
example (n : ℕ) (hn : n > 1) : ∃ p, Nat.Prime p ∧ n < p := by
  have : ∃ p, Nat.Prime p ∧ p ∣ Nat.factorial n + 1 := by
    aesop (add safe Nat.exists_prime_and_dvd, safe forward Nat.factorial_ne_zero)
  obtain ⟨p, hp, hd⟩ := this
  have : ¬ (p ≤ n) := by
    intro hle
    have : p ∣ Nat.factorial n := by
      saturate [Nat.Prime.dvd_factorial]
      simp_all
    saturate 1 [Nat.dvd_sub']
    aesop
  aesop



def Prop1 (_ : Nat) := True
def Prop2 (_ : Nat) := True
def Prop3 (_ : Nat) := True


set_option aesop.dev.statefulForward true in
--set_option trace.profiler true in
example (h1 : Prop1 1) (h2 : Prop1 2) (h3 : Prop1 3)
    (p12 : ∀ n, Prop1 n → Prop2 (n + 1))
    (p23 :∀ n, Prop2 n → Prop3 (n + 1))
    : Prop3 4 := by
  saturate [*]
  simp_all only [Nat.reduceAdd]


set_option aesop.dev.statefulForward false in
--set_option trace.profiler true in
example (h1 : Prop1 1) (h2 : Prop1 2) (h3 : Prop1 3)
    (p12 : ∀ n, Prop1 n → Prop2 (n + 1))
    (p23 :∀ n, Prop2 n → Prop3 (n + 1))
    : Prop3 4 := by
  saturate [*]
  simp_all only [Nat.reduceAdd]


example (p q : Prop) (h : p) (hpq : p → q) : q := by
  saturate [hpq, h]; assumption


/- Interestingly, aesop does not close this goal without a saturate. -/
example {P Q P' Q': Nat → Prop} (t : Nat) (hP : P' t)
  (h : ∀ (s : Nat), P s → ∃ t : Nat, Q t)
  (hP'P : ∀ t, P' t → P t)
  (hQQ' : ∀ t, Q t → Q' t):
  ∃ w : Nat, Q' w := by
  saturate [*]
  aesop

--set_option maxRecDepth 100
set_option aesop.dev.statefulForward true in
--set_option trace.profiler true in
example {P Q : Nat → Prop} (hP : P 0) (hPn : ∀ n, P n → P (n + 1))
   (hQ : Q 0) (hQn : Q 0 → Q 1):
    Q 1 := by
  saturate 5 [*]
  assumption

set_option aesop.dev.statefulForward false in
--set_option trace.profiler true in
example {P Q: Nat → Prop}  (hP : P 0) (hPn : ∀ n, P n → P (n + 1))
     (hQ : Q 0) (hQn : Q 0 → Q 1) :
    Q 1 := by
  saturate 5 [*]
  assumption

set_option aesop.dev.statefulForward false in
--set_option trace.profiler true in
example {P : Nat → Prop} (hP : P 0)
    (hPn1 : P 0 → P 1)
    (hPn2 : P 1 → P 2)
    (hPn3 : P 2 → P 3)
    (hPn4 : P 3 → P 4)
    (hPn5 : P 4 → P 5)
    (hPn6 : P 5 → P 6)
    (_ : P 6 → P 7)
    --(hPn8 : P 7 → P 7)
    (_ : P 6 → P 7)
    (hPn10 : P 6 → P 7)
    (hPn11 : P 6 → P 7)
    (hPn12 : P 6 → P 7)
    (hPn13 : P 6 → P 7) :
    P 6 := by
  saturate 30 [*]
  simp_all only [imp_self]

set_option aesop.dev.statefulForward true in
--set_option trace.profiler true in
example {P : Nat → Prop} (hP : P 0)
    (hPn1 : P 0 → P 1)
    (hPn2 : P 1 → P 2)
    (hPn3 : P 2 → P 3)
    (hPn4 : P 3 → P 4)
    (hPn5 : P 4 → P 5)
    (hPn6 : P 5 → P 6)
    (hPn7 : P 6 → P 7)
    --(hPn8 : P 7 → P 7)
    (hPn9 : P 6 → P 7)
    (hPn10 : P 6 → P 7)
    (hPn11 : P 6 → P 7)
    (hPn12 : P 6 → P 7)
    (hPn13 : P 6 → P 7) :
    P 6 := by
  saturate 30 [*]
  simp_all only [imp_self]


--set_option trace.profiler true in
example {P : Nat → Prop} (hP : P 0) (hP1 : P 1)
    (hP2 : P 2) (hP3 : P 3)
    (hP4 : P 4) (hP5 : P 5)
    (hP6 : P 6) (hP7 : P 7)
    (hP8 : P 8) (hP9 : P 9)
    (hPn1 : P 0 → P 1 → P 2 → P 3 → P 4 → P 5
      → P 6 → P 7 → P 8 → P 9 → P 10) :
    P 10 := by
  let zero := 0
  saturate [*]
  assumption



--set_option trace.profiler true in
example (h1 : Prop1 1) (h2 : Prop1 2) (h3 : Prop1 3)
    (p12 : ∀ n, Prop1 n → Prop2 (n + 1))
    (p23 :∀ n, Prop2 n → Prop3 (n + 1))
    : Prop3 4 := by
  saturate [*]
  simp_all only [Nat.reduceAdd]


lemma r1 {P : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Prop}
  {Q : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Prop}
  (a b c d e f x : ℕ)
  (hP : P a b c d e f) :
  Q f e d c b a := sorry

/- True is slower-/
--set_option trace.profiler true in
set_option aesop.dev.statefulForward false in
example {P : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Prop}
    {Q : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Prop}
    (a b c d e f g h i j k : ℕ)
    (h1 : P i h d c g a) :
   Q a g c d h i := by
  saturate 1 [r1]
  assumption

lemma r2 {P : ℕ → Prop}
  {Q : ℕ → Prop}
  (a x y z : ℕ)
  (hP : P a) :
  Q a := sorry

--set_option trace.profiler true in
set_option aesop.dev.statefulForward false in
example {P : ℕ → Prop}
    {Q : ℕ → Prop}
    (a : ℕ)
    (h1 : P a) :
   Q a := by
  saturate 1 [r2]
  assumption

  -----
section r3
namespace r3

def P₁ : ℕ → ℕ → Prop := sorry
def P₃ : ℕ → ℕ → Prop := sorry
def P₂ : ℕ → Prop := sorry
def P₄ : ℕ → Prop := sorry

lemma r3
    (x y z c : ℕ)
    (h : P₁ x y) (h : P₂ z) (h : P₃ z x) (h : P₄ y) :
    False := sorry

--set_option trace.profiler true in
set_option aesop.dev.statefulForward true in
example
    (x y z a b c : ℕ)
    (a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ : ℕ)
     (h : P₂ z) (h : P₃ z a₁) (h : P₄ b)
    (h : P₁ a₂ y) (h : P₂ z) (h : P₃ z a₂) (h : P₄ b)
    (h : P₁ a₃ y) (h : P₂ z) (h : P₃ z a₃) (h : P₄ b)
    (h : P₁ a₄ y) (h : P₂ z) (h : P₃ z a₄) (h : P₄ b)
    (h : P₁ a₅ y) (h : P₂ z) (h : P₃ z a₉) (h : P₄ b)
    (h : P₁ a₆ y) (h : P₂ z) (h : P₃ z a₁₀) (h : P₄ b)
    (h : P₁ b y) (h : P₂ a) (h : P₃ x x) (h : P₄ a)
    (h : P₁ x c) (h : P₂ z) (h : P₃ a z) (h : P₄ x)
    (h : P₁ x c) (h : P₂ z) (h : P₃ z x) (h : P₄ c)
    --(hP₁ : P₁ x y) (hP₂ : P₂ z) (hP₃ : P₃ z x) (hP₄ : P₄ y)
    : False := by
  aesop
  saturate? 4 [r3]
  assumption

end r3

section s

def P₁ : ℕ → ℕ → ℕ → Prop := sorry
def P₃ : ℕ → Prop := sorry
def P₂ : ℕ → Prop := sorry
def P₄ : ℕ → Prop := sorry

def lem1 : Prop := sorry
def lem2 : Prop := sorry

lemma s (a b c d : ℕ)
    (h : P₁ a b d) (h : P₂ b) (h : P₃ c) (h : P₄ d) :
    lem1 := sorry

lemma s' (c : ℕ)
    (h : P₃ c) :
    lem2 := sorry

set_option trace.profiler true in
set_option aesop.dev.statefulForward true in
example
    (x y z a b c : ℕ)
    (a₁ a₂ a₃ a₄ a₅ a₆ a₇: ℕ)
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ℕ)
    (c₁ c₂ c₃ c₄ c₅ c₆ c₇ : ℕ)
    (d₁ d₂ d₃ d₄ d₅ d₆ d₇ : ℕ)
    (h : P₁ a b c) (h : P₂ b) (h : P₃ c)
    (h : P₁ a₁ b c) (h : P₂ a₆) (h : P₃ c)
    (h : P₁ a₁ b c) (h : P₂ a₁)
    (h : P₁ a₂ b c) (h : P₂ a₂)
    (h : P₁ a₃ b c) (h : P₂ a₃)
    (h : P₁ a₄ b c) (h : P₂ a₄)
    (h : P₁ a₅ b c) (h : P₂ a₅)
    (h : P₁ a₆ b c) (h : P₂ a₆)
    (h : P₁ a₇ b c) (h : P₂ a₇)
    (h : P₁ b₁ b c) (h : P₂ b₁)
    (h : P₁ b₂ b c) (h : P₂ b₂)
    (h : P₁ b₃ b c) (h : P₂ b₃)
    (h : P₁ b₄ b c) (h : P₂ b₄)
    (h : P₁ b₅ b c) (h : P₂ b₅)
    (h : P₁ b₆ b c) (h : P₂ b₆)
    (h : P₁ b₇ b c) (h : P₂ b₇)
    (h : P₁ c₁ b c) (h : P₂ c₁)
    (h : P₁ c₂ b c) (h : P₂ c₂)
    (h : P₁ c₃ b c) (h : P₂ c₃)
    (h : P₁ c₄ b c) (h : P₂ c₄)
    (h : P₁ c₅ b c) (h : P₂ c₅)
    (h : P₁ c₆ b c) (h : P₂ c₆)
    (h : P₁ c₇ b c) (h : P₂ c₇)
    (h : P₁ d₁ b c) (h : P₂ d₁)
    (h : P₁ d₂ b c) (h : P₂ d₂)
    (h : P₁ d₃ b c) (h : P₂ d₃)
    (h : P₁ d₄ b c) (h : P₂ d₄)
    (h : P₁ d₅ b c) (h : P₂ d₅)
    (h : P₁ d₆ b c) (h : P₂ d₆)
    (h : P₁ d₇ b c) (h : P₂ d₇)
    : False := by
  saturate 1 [s]
  assumption



end r3
