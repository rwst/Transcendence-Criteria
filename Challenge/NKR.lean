/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Challenge.Cited

/-!
# Challenge, part 3: the Nair–Kumar–Rout refutation

Mirrors `CITED/NairKumarRout.lean`.  Kept in its own module, as in the development, so that
`NKR.uval` owns the `Nat.AtLeastTwo` auxiliaries for the rational numerals `2` and `3`
rather than inheriting `RB.scaledViolators`'s (see `Challenge/Orbit.lean` for why that
matters).
-/

namespace NKR

/-- The value `u = 2^x·3^y` of the Main-Theorem tuples under the exponent encoding of
`Γ = ⟨2, 3⟩`. -/
def uval (x y : ℤ) : ℚ := (2 : ℚ) ^ x * (3 : ℚ) ^ y

/-- **The unrepaired [NKR25] Theorem 1.3(i) is false** (machine-checked refutation): the
∀-closure of Theorem 1.3(i) of the preprint, ℚ-specialized, is **disprovable** in plain
Lean + Mathlib.  The witness family is `(u₁, u₂) = (3^m/2, 3^{2m}/2)`, `m ≥ 1`: the sum is
an *exact* integer by parity, so the distance to `ℤ` is `0`, which the preprint's inequality
(1) does not exclude — yet no entry is ever an integer.

Nothing is taken on the authority of [NKR25], an unrefereed preprint: only the repaired
(strict-positivity) form is used in the development, and that form is *derived* from the
Subspace Theorem rather than assumed.

Certified by `comparator/rigidity.json` under std3 alone. -/
theorem thm13i_unrepaired_false :
    ¬ (∀ (α₁ α₂ : ℚ), α₁ ≠ 0 → α₂ ≠ 0 → ∀ (ε₁ : ℝ), 0 < ε₁ →
      ∀ (𝒩 : Set ((ℤ × ℤ) × (ℤ × ℤ))), 𝒩.Infinite →
      (∀ q ∈ 𝒩, 1 ≤ |uval q.1.1 q.1.2| ∧ 1 ≤ |uval q.2.1 q.2.2|) →
      (∀ q ∈ 𝒩, uval q.1.1 q.1.2 ≠ -uval q.2.1 q.2.2) →
      (∀ q ∈ 𝒩, ∀ q' ∈ 𝒩, q ≠ q' →
        uval q.1.1 q.1.2 / uval q.2.1 q.2.2 ≠ uval q'.1.1 q'.1.2 / uval q'.2.1 q'.2.2 ∧
        uval q.2.1 q.2.2 / uval q.1.1 q.1.2 ≠ uval q'.2.1 q'.2.2 / uval q'.1.1 q'.1.2) →
      (∀ q ∈ 𝒩,
        ((α₁ * uval q.1.1 q.1.2 + α₂ * uval q.2.1 q.2.2).distToNearestInt : ℝ)
          < ((CZ.height23 q.1.1 q.1.2 * CZ.height23 q.2.1 q.2.2 : ℕ) : ℝ) ^ (-ε₁)) →
      ∃ q ∈ 𝒩, (∃ n : ℤ, uval q.1.1 q.1.2 = n) ∧ (∃ n : ℤ, uval q.2.1 q.2.2 = n)) := sorry

end NKR
