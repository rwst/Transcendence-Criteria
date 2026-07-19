/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Set.Finite.Basic
import CITED.SubspaceTheorem

/-!
# Ridout's theorem, as the two-variable case of the Subspace Theorem

**Ridout's theorem** ([Rid57]) — the `p`-adic (`S`-arithmetic) generalization of
Roth's theorem — is exactly the `n = 2` case of the Subspace Theorem
(`Subspace.evertseSchlickewei`).  This file *derives* it from that single cited
axiom rather than adding a second axiom, executing the first step of the
one-axiom refactor of `report-formalize-subspace.html` §6.

The engine over `ℚ`: for a finite set `S` of places and, at each place, two
linearly independent linear forms in `(x₀, x₁)`, the nonzero rational points
whose Subspace product falls below `H(x)^{-2-ε}` lie on **finitely many lines**
through the origin — equivalently, the ratios `x₁/x₀` of the good solutions form
a **finite set**.  That is `Ridout.finite_ratios` below, Ridout's theorem in
projective (ratio) form.

## From ratios to `|δ − p/q|`

The classical statement — *only finitely many `p/q` approximate a fixed
algebraic `δ` with `∏_{v∈S} \|δ − p/q\|_v < H(p/q)^{-2-ε}`* — is the special
case in which the archimedean forms are `x₀ − δ·x₁` and `x₁` and the finite
places `ℓ ∈ S` contribute the coordinate forms `x₀, x₁` (so `|x₀|_ℓ`, `|x₁|_ℓ`
measure the `ℓ`-adic size of numerator and denominator).  A rational point
`x = (p, q)` on one of the finitely many output lines has a fixed ratio
`p/q`, i.e. one approximant.  This is precisely the configuration Corvaja–Zannier
invoke over `ℚ` (`report-formalize-subspace.html` §3): with `δ ∈ ℚ` and
`S = {∞, 2, 3}` it is the sole deep input surviving in their Main Theorem, the
denominators ranging over the `S`-units `2^a 3^b`.

Choosing those forms and verifying the archimedean/`ℓ`-adic bound
`approxProduct ≤ H(x)^{-2-ε}` for a good approximant is the analytic step that
turns `finite_ratios` into the Corvaja–Zannier Main Theorem — carried out in
`CITED/CorvajaZannierProof.lean` (`CZ.pseudoPisot_approx_of_subspace`,
sorry-free, 2026-07-14).  What is established *here*, axiom-cleanly modulo
`Subspace.evertseSchlickewei`, is the projective finiteness that every such
instantiation consumes.

## Contents

* `Ridout.finite_ratios` — **Ridout's theorem** (projective form): the ratios
  `x₁/x₀` of the good rational solutions of the `n = 2` Subspace inequality form
  a finite set.  Derived from `Subspace.evertseSchlickewei` at `n = 2`.

## References

* [Rid57] D. Ridout, *The p-adic generalization of the Thue–Siegel–Roth
  theorem*, Mathematika **4** (1957), 125–131.
* [S] W. M. Schmidt, *Diophantine Approximation and Diophantine Equations*, LNM
  **1467**, Springer 1991 (Theorem 1D′; Ridout is its `n = 2` case).
* [CZ04] Corvaja–Zannier, Acta Math. **193** (2004) — the consumer over `ℚ`
  (derived in `CITED/CorvajaZannierProof.lean`).
* `report-formalize-subspace.html` (this repository, 2026-07): §3 (CZ → Ridout),
  §6 (the one-axiom refactor this file begins).
-/

namespace Ridout

open Subspace

/-- On a proper subspace `W` of `ℚ²` the ratio `x₁/x₀` is the same for every
member with nonzero `0`-coordinate: a line has a single slope.  This is the
linear-algebra core that turns "finitely many proper subspaces" into "finitely
many ratios". -/
private lemma ratio_determined {W : Submodule ℚ (Fin 2 → ℚ)} (hW : W ≠ ⊤)
    {x y : Fin 2 → ℚ} (hx : x ∈ W) (hy : y ∈ W) (hx0 : x 0 ≠ 0) (hy0 : y 0 ≠ 0) :
    x 1 / x 0 = y 1 / y 0 := by
  have hxne : x ≠ 0 := by intro h; apply hx0; rw [h]; rfl
  have hdim : Module.finrank ℚ (Fin 2 → ℚ) = 2 := by rw [Module.finrank_pi]; simp
  have hWlt : Module.finrank ℚ W < 2 := by
    have := Submodule.finrank_lt (K := ℚ) (V := Fin 2 → ℚ) hW; omega
  have hle : (ℚ ∙ x) ≤ W := (Submodule.span_singleton_le_iff_mem x W).mpr hx
  have hspan1 : Module.finrank ℚ (ℚ ∙ x) = 1 := finrank_span_singleton hxne
  have hWge : 1 ≤ Module.finrank ℚ W := by have := Submodule.finrank_mono hle; omega
  have hWeq : Module.finrank ℚ W = 1 := by omega
  have heq : (ℚ ∙ x) = W := Submodule.eq_of_le_of_finrank_le hle (by rw [hspan1, hWeq])
  have hyx : y ∈ (ℚ ∙ x) := heq ▸ hy
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hyx
  have hy0' : y 0 = c * x 0 := by rw [← hc]; rfl
  have hy1' : y 1 = c * x 1 := by rw [← hc]; rfl
  have hcne : c ≠ 0 := by rintro rfl; apply hy0; rw [hy0']; ring
  rw [hy0', hy1', mul_div_mul_left _ _ hcne]

/-- **Ridout's theorem**, projective form ([Rid57]; the `n = 2` case of the
Subspace Theorem [S, Thm 1D′]).  For a finite place set `S` and per-place
linearly independent linear forms `L` on `ℚ²`, the ratios `x₁/x₀` of the nonzero
rational solutions of
`approxProduct S L x ≤ H(x)^{-2-ε}` form a **finite set**.

Derived from `Subspace.evertseSchlickewei` at `n = 2`: the theorem confines the
solutions to finitely many proper subspaces (lines) of `ℚ²`, and on each line
the ratio is constant (`ratio_determined`).  Axiom footprint: the Subspace
axiom only.  See the module doc for how the classical `|δ − p/q|` statement is
the instantiation with `L` the forms `x₀ − δ·x₁`, `x₁` and coordinate forms. -/
theorem finite_ratios
    (S : Finset (AbsoluteValue ℚ ℝ))
    (L : AbsoluteValue ℚ ℝ → Fin 2 → ((Fin 2 → ℚ) →ₗ[ℚ] ℚ))
    (hL : ∀ v ∈ S, LinearIndependent ℚ (L v))
    (ε : ℝ) (hε : 0 < ε) :
    {r : ℚ | ∃ x : Fin 2 → ℚ, x ≠ 0 ∧ x 0 ≠ 0 ∧ r = x 1 / x 0 ∧
      approxProduct S L x ≤ Height.mulHeight x ^ (-(2 : ℝ) - ε)}.Finite := by
  classical
  obtain ⟨T, hTproper, hTcover⟩ :=
    evertseSchlickewei_rat (n := 2) (by norm_num) S L hL ε hε
  -- slope of a line: the ratio of any representative with nonzero 0-coordinate
  refine Set.Finite.subset (Set.Finite.image
    (fun W : Submodule ℚ (Fin 2 → ℚ) =>
      if h : ∃ z : Fin 2 → ℚ, z ∈ W ∧ z 0 ≠ 0
      then (Classical.choose h) 1 / (Classical.choose h) 0 else 0)
    T.finite_toSet) ?_
  rintro r ⟨x, hxne, hx0, rfl, hineq⟩
  obtain ⟨W, hWT, hxW⟩ := hTcover x hxne (by exact_mod_cast hineq)
  refine ⟨W, Finset.mem_coe.mpr hWT, ?_⟩
  have hex : ∃ z : Fin 2 → ℚ, z ∈ W ∧ z 0 ≠ 0 := ⟨x, hxW, hx0⟩
  have hcs := Classical.choose_spec hex
  simp only [dif_pos hex]
  exact ratio_determined (hTproper W hWT) hcs.1 hxW hcs.2 hx0

end Ridout
