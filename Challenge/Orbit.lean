/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib

/-!
# Challenge, part 1: the orbit, the word, and the constant

Part of the trusted statement of record; see `Challenge.lean` for what comparator does with
it.  Mirrors `ForMathlib/Data/{Real,Rat}/NearestInt.lean`,
`ForMathlib/Combinatorics/SubwordComplexity.lean` and `RB/Basic.lean`.

**Why the challenge is split across modules at all.**  Lean abstracts the proof obligations
inside a definition (here: `Nat.AtLeastTwo` for the numerals `2` and `3`) into auxiliary
constants named after the enclosing declaration — `RB.K._proof_1` and so on — and *reuses*
an existing auxiliary when an identical one is already present **in the same module**.  The
development spreads `RB.K`, `CZ.svalR` and `RB.algViolators` across three modules, so each
owns its auxiliaries; collapsing them into a single challenge module would make the latter
two point at `RB.K`'s, and comparator would report a mismatch that is real at the level of
constants even though the statements are identical.  The module split below reproduces the
development's boundaries, so the auxiliary names line up on their own.
-/

/-! ## Distance to the nearest integer (`ForMathlib`) -/

/-- The distance from a real number to the nearest integer. -/
noncomputable def distToNearestInt (x : ℝ) : ℝ := |x - round x|

namespace Rat

/-- The distance from a rational number to the nearest integer. -/
def distToNearestInt (x : ℚ) : ℚ := |x - round x|

end Rat

/-! ## Factors of an infinite word (`ForMathlib`) -/

namespace ForMathlib.SubwordComplexity

variable {α : Type*}

/-- The length-`k` **factor** of the word `u : ℕ → α` starting at position `i`:
the tuple `(u i, u (i+1), …, u (i+k-1))`, indexed by `Fin k`. -/
def factor (u : ℕ → α) (k i : ℕ) : Fin k → α := fun s => u (i + s)

end ForMathlib.SubwordComplexity

/-! ## The orbit, the word, the constant (`RB/Basic.lean`, `RB/Rigidity.lean`) -/

namespace RB

/-- The orbit `xₙ = ⌈3xₙ₋₁/2⌉` from `x 0 = x₀`.  In `ℕ`-division `⌈3a/2⌉ = (3a+1)/2`.
For `x₀ = 1` this is OEIS A061419. -/
def x (x₀ : ℕ) : ℕ → ℕ
  | 0 => x₀
  | n + 1 => (3 * x x₀ n + 1) / 2

/-- The **minimal word** `wₙ = 2xₙ₊₁ − 3xₙ = xₙ mod 2` — the word `g_{3/2}` of the rational
base `3/2` number system. -/
def wmin (x₀ : ℕ) (n : ℕ) : ℕ := x x₀ n % 2

/-- The constant `K = lim xₙ/(3/2)ⁿ`, *defined* by the series.
`K 1 = ω_{3/2} = 1.6222705028…` (OEIS A083286). -/
noncomputable def K (x₀ : ℕ) : ℝ := x₀ + (1 / 3) * ∑' j, (2 / 3 : ℝ) ^ j * wmin x₀ j

/-- A length-`k` factor of the minimal word occurring at positions `a` and `c`:
`w (a+i) = w (c+i)` for all `i < k`.  Occurrences may overlap. -/
def IsRepetition (x₀ a c k : ℕ) : Prop := ∀ i < k, wmin x₀ (a + i) = wmin x₀ (c + i)

end RB
