/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import RB.MahlerSystem
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Localization.Rat
import Mathlib.Tactic.NormNum

/-!
# The regularity lemma: `2/3` is a regular point (plan-B1E2, WP10, T2)

**If `σ(·,0)` is a permutation of the kernel, then `2/3` and every `(2/3)^{k^m}` is a *regular*
point of the Mahler system** — `det M` does not vanish there (`regular_two_thirds`).

Unconditional, elementary, and of independent interest: [AF17] stress that *no* condition in the
literature rules out the exceptional branch of their Cor 1.8, and this is a checkable sufficient
condition at rational points.

## The lever

The whole proof is three lines of mathematics, and it turns on our point being **rational**:

1. `M(0) = P₀` (`RB.mahlerMatrix_map_eval_zero`), so if `σ(·,0)` is a permutation then `M(0)` is
   a permutation matrix and **`det M(0) = ±1`** (`det_eval_zero_eq_pm_one`).
2. `det M ∈ ℤ[z]`, so `det M(0) = ±1` *is* its constant coefficient.
3. **Rational-root theorem**: a rational root of an integer polynomial has numerator dividing the
   constant coefficient. Dividing `±1` forces numerator `±1`. But `(2/3)^N = 2^N/3^N` has
   numerator `2^N ≥ 2` for `N ≥ 1`. ∎ (`not_root_of_coeff_zero_pm_one`)

Since `k^m ≥ 1` for every `m ≥ 0` whenever `k ≥ 1`, **all** the iterates `(2/3)^{k^m}` are covered
at once — including `m = 0`, i.e. `2/3` itself.

## Where the lever stops — and why that is coherent

The rational-root theorem says **nothing** at algebraic irrationals, and [AF17] §8.1's
counterexample to any regularity-free transcendence claim lives exactly there: its singular points
are `φ = (1−√5)/2` and its `3ˡ`-th roots. That the lever works precisely where the counterexample
does not is a good sign — but note the corollary: **plan-B1E2's E.2 cases, whose evaluation point
`1/σβ` is an algebraic irrational, do not inherit it** ([B1E2] §5). Case 2 of E.2 needs a genuine
regularity argument at algebraic points, which nobody has.

## Status of the debt this discharges

Rev. 1 of [B1E2] filed regularity as "known technical debt … one hard sub-lemma". Gate 0 showed
it was the *whole* difference between Track I working and not. It is now a theorem in the main
case, and an exhaustive search (all systems with `k ∈ {2,3}`, `d ∈ {2,3,4}`, `m < 4`) found
**zero** genuine singularities at `(2/3)^{k^m}`: 39130 systems have `det M((2/3)^{k^m}) = 0`, but
every one of them has `det M ≡ 0` — degenerate, every point singular, `2/3` not special — and
none has `det P₀ ≠ 0`, confirming the lever. **So Track I is blocked on exactly one input: the
`p`-adic port (WP5), which does not exist in the literature.** Regularity is *not* the blocker.

## Contents

* **`RB.not_root_of_coeff_zero_pm_one`** — the arithmetic core: an integer polynomial with
  constant coefficient `±1` has no root `(2/3)^N`, `N ≥ 1`.
* **`RB.det_eval_zero_eq_pm_one`** — `σ(·,0)` a permutation ⇒ `det M(0) = ±1`.
* **`RB.regular_two_thirds`** — the regularity lemma (T2).

## References

* [AF17] Adamczewski, Faverjon. *Méthode de Mahler …* Proc. LMS **115** (2017), 55–90.  (Thm 1.4
  = the regular-point transcendence theorem this feeds; §8.1 = the counterexample, at algebraic
  *irrationals*.)
* [B1E2] `plans/plan-B1E2.html` (rev. 2, 2026-07): §0.2 (this lemma, worked out), §5 (why E.2
  does not inherit it), WP10.
-/

namespace RB

open Polynomial

/-! ## The arithmetic core -/

/-- **The rational-root lever** ([B1E2] §0.2(4)): an integer polynomial whose constant
coefficient is `±1` has no root of the form `(2/3)^N` with `N ≥ 1`.

The numerator of `(2/3)^N` is `2^N`, which would have to divide `±1`. -/
theorem not_root_of_coeff_zero_pm_one {P : Polynomial ℤ} (hP : P.coeff 0 = 1 ∨ P.coeff 0 = -1)
    {N : ℕ} (hN : 0 < N) : ¬ (Polynomial.aeval ((2 / 3 : ℚ) ^ N) P = 0) := by
  intro hroot
  have h1 : IsFractionRing.num ℤ ((2 / 3 : ℚ) ^ N) ∣ P.coeff 0 := num_dvd_of_is_root hroot
  have h2 : Associated (IsFractionRing.num ℤ ((2 / 3 : ℚ) ^ N) : ℤ) (((2 / 3 : ℚ) ^ N).num) :=
    Rat.isFractionRingNum _
  have h3 : ((2 / 3 : ℚ) ^ N).num ∣ P.coeff 0 := (h2.dvd_iff_dvd_left).mp h1
  have hnum : ((2 / 3 : ℚ) ^ N).num = 2 ^ N := by
    rw [Rat.num_pow]
    norm_num [Rat.num]
  rw [hnum] at h3
  have h2N : (2 : ℤ) ^ N ∣ 1 := by
    rcases hP with h | h
    · rwa [h] at h3
    · rw [h] at h3; exact dvd_neg.mp h3
  have hle := Int.le_of_dvd one_pos h2N
  have h2le : (2 : ℤ) ≤ 2 ^ N := by
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hN
  omega

/-! ## `det M(0) = ±1` -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The lever's hypothesis, discharged** ([B1E2] §0.2(2)+(4)): if `σ(·,0)` is a permutation of
the index set, then `M(0)` is its permutation matrix, so `det M(0) = sign = ±1`.

(The plan reaches this via the permutation expansion of `det M` — §0.2(3), "the all-zeros tuple
contributes `z⁰` with coefficient `±1`".  Going through `M(0) = P₀` is the same fact and is
shorter in Lean, so the expansion is not formalized separately.) -/
lemma det_eval_zero_eq_pm_one (k : ℕ) (hk : 0 < k) (σ : ι → Fin k → ι)
    (e : Equiv.Perm ι) (he : ∀ i, e i = σ i ⟨0, hk⟩) :
    (mahlerMatrix k σ).det.eval 0 = 1 ∨ (mahlerMatrix k σ).det.eval 0 = -1 := by
  have hmap : (Polynomial.evalRingHom 0).mapMatrix (mahlerMatrix k σ) = e.permMatrix ℤ := by
    have h1 : (Polynomial.evalRingHom (0 : ℤ)).mapMatrix (mahlerMatrix k σ)
        = (mahlerMatrix k σ).map (Polynomial.eval 0) := rfl
    rw [h1, mahlerMatrix_map_eval_zero k hk σ]
    ext i j
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, he i]
  have hdet : (mahlerMatrix k σ).det.eval 0 = (e.permMatrix ℤ).det := by
    have h := RingHom.map_det (Polynomial.evalRingHom (0 : ℤ)) (mahlerMatrix k σ)
    rw [hmap] at h
    exact h
  rw [hdet, Matrix.det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign e) with h | h <;> simp [h]

/-! ## The regularity lemma -/

/-- **T2 — the regularity lemma** ([B1E2] §0.2): if `σ(·,0)` is a permutation of the index set,
then **`2/3` is a regular point**: `det M` vanishes at none of the iterates `(2/3)^{k^m}`.

All iterates are covered at once, `m = 0` (i.e. `2/3` itself) included, because `k^m ≥ 1`.

Unconditional and elementary. It works *because* the point is rational; see the module doc for
where it stops. -/
theorem regular_two_thirds (k : ℕ) (hk : 0 < k) (σ : ι → Fin k → ι)
    (e : Equiv.Perm ι) (he : ∀ i, e i = σ i ⟨0, hk⟩) (m : ℕ) :
    Polynomial.aeval ((2 / 3 : ℚ) ^ (k ^ m)) (mahlerMatrix k σ).det ≠ 0 := by
  refine not_root_of_coeff_zero_pm_one ?_ (pow_pos hk m)
  simpa [Polynomial.coeff_zero_eq_eval_zero] using det_eval_zero_eq_pm_one k hk σ e he

end RB
