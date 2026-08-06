/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Challenge.Orbit

/-!
# Challenge, the Mahler-method inputs (1/5): the substitution `z ↦ z^q`

Part of the trusted statement of record; see `Challenge.lean` for what comparator does with it,
and `Challenge/AF.lean` for why the AF block is split into five modules and what the instance
erasures below are for.  Mirrors `CITED/AdamczewskiFaverjonRelationIdeal.lean` and
`CITED/AdamczewskiFaverjonRelationMatrix.lean`.
-/

attribute [-instance] IsDomain.of_isSimpleRing CommCStarAlgebra.toNormedCommRing
  IsLocalRing.toNontrivial IsSimpleRing.instNontrivial NonUnitalCStarAlgebra.toNormedSpace
  CompleteLattice.toCompletePartialOrder

namespace AF

open scoped Polynomial RatFunc nonZeroDivisors

/-! Universe parameters are named explicitly wherever a definition binds its own carrier type
inside a section that already has `Type*` variables: `Type*` numbers the auto-bound universes per
declaration in order of appearance, so the development's `AF.substPow` — declared under
`variable {K : Type*} … {ι : Type*} …` — carries `u_3`, not `u_1`, and the export records the
name.  Nothing else about these declarations depends on it. -/

/-- The substitution `z ↦ z^q` on polynomials. -/
noncomputable def substPow.{u_3} (K : Type u_3) [Field K] (q : ℕ) : K[X] →+* K[X] :=
  (Polynomial.aeval ((Polynomial.X : K[X]) ^ q)).toRingHom

section Subst

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem substPow_eq_expand (q : ℕ) (p : K[X]) : substPow K q p = Polynomial.expand K q p := rfl

theorem substPow_ne_zero {q : ℕ} (hq : 0 < q) {p : K[X]} (hp : p ≠ 0) : substPow K q p ≠ 0 := by
  rw [substPow_eq_expand]
  exact (Polynomial.expand_ne_zero hq).2 hp

variable (K ι) in
/-- The matrix of indeterminates `Y = (y_{i,j})`, as a matrix over `K(z)[Y]`.

Nothing below mentions it.  It is here because `RatFunc K` forces an auxiliary proof constant
(the `IsDomain K[X]` obligation of the localization), and Lean names such a constant after the
declaration that first created it and *reuses* it within the module: in the development that
declaration is `AF.matX`, which sits above `AF.substPowRat` in
`CITED/AdamczewskiFaverjonRelationMatrix.lean`.  Omit this and the challenge would create the
same proof under the name `AF.substPowRat._proof_1`, shifting the development's `_proof_1` to
`_proof_2` — a mismatch that is real at the level of constants although the statements agree.
`Challenge/Orbit.lean` documents the mechanism. -/
noncomputable def matX : Matrix ι ι (MvPolynomial (ι × ι) (RatFunc K)) :=
  Matrix.of fun i j => MvPolynomial.X (i, j)

/-- The substitution `z ↦ z^n` on rational functions, `n ≥ 1`. -/
noncomputable def substPowRat.{u_3} (K : Type u_3) [Field K] {n : ℕ} (hn : 0 < n) :
    RatFunc K →+* RatFunc K :=
  IsLocalization.lift (M := (K[X])⁰) (S := RatFunc K)
    (g := (algebraMap K[X] (RatFunc K)).comp (substPow K n))
    (fun y => isUnit_iff_ne_zero.2 fun h =>
      substPow_ne_zero hn (nonZeroDivisors.ne_zero y.2)
        (RatFunc.algebraMap_injective K (h.trans (map_zero _).symm)))

end Subst

end AF
