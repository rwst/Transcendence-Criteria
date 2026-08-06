/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Challenge.AF.Analytic

/-!
# Challenge, part 3: the Mahler-method inputs

Part of the trusted statement of record; see `Challenge.lean` for what comparator does with it.
This file states the two cited axioms; `Challenge/AF/*.lean` carry the definitions their
statements need.

## What is taken on faith here, and why it is not what it used to be

[AF17] Corollaire 1.8 — *the value at a rational `α`, `0 < |α| < 1`, of the generating series of a
bounded automatic sequence is transcendental or rational* — used to be the cited axiom of this
lane.  It is now a **theorem** of the development
(`AF.transcendental_or_rat_of_automatic`, `CITED/AdamczewskiFaverjonTheoreme17.lean`), proved
along [AF22]'s new proof of Nishioka's theorem.  What is taken on faith moved one layer down, to
the two lemmas of that proof which the development does not reprove: [AF17] Lemme 2.2 and [AF22]
Lemme 2.8.  The lane got deeper, not wider.

## Why the block is five modules plus this one

Two mechanisms force it, both of them already documented in `Challenge/Orbit.lean` and
`Challenge/Cited.lean` and neither of them affecting what any statement *means*.

**Auxiliary proof constants.**  Lean abstracts a proof obligation appearing inside a definition
into a constant named after the enclosing declaration, and reuses an existing one only *within a
module*.  The development spreads these definitions over
`CITED/AdamczewskiFaverjon{RelationMatrix,Primitive,Assembly,MahlerAmbient,ReverseTransport}.lean`,
so it has five owners — `AF.matX._proof_1`, `AF.solField._proof_1`, `AF.toAmbient._proof_1`,
`AF.Twisted._proof_1`, `AF.IsAnalyticRealization._proof_1` and friends.  A single challenge module
would collapse them onto one owner and comparator would report a mismatch that is real at the
level of constants although the statements are identical.  Hence one challenge module per
development module that owns one, in `Challenge/AF/`.

**Instance erasures.**  `Challenge/Orbit.lean` does `import Mathlib`, and several instances then
resolve along a route the development's fine-grained imports never see.  The terms are defeq but
not structurally identical, so each module in `Challenge/AF/` opens by erasing the extra routes:

| instance | under `import Mathlib` | in the development |
| --- | --- | --- |
| `IsDomain K` (for `RatFunc K`) | `IsDomain.of_isSimpleRing` | `instIsDomain` |
| `NormedCommRing ℂ` | `CommCStarAlgebra.toNormedCommRing` | `NormedField.toNormedCommRing` |
| `Nontrivial K` | `IsLocalRing.toNontrivial`, `IsSimpleRing.instNontrivial` | `EuclideanDomain.toNontrivial` |
| `NormedSpace ℂ ℂ` | `NonUnitalCStarAlgebra.toNormedSpace` | `InnerProductSpace.toNormedSpace` |
| `PartialOrder (IntermediateField …)` | `CompleteLattice.toCompletePartialOrder` | `SemilatticeSup.toPartialOrder` |
-/

attribute [-instance] IsDomain.of_isSimpleRing CommCStarAlgebra.toNormedCommRing
  IsLocalRing.toNontrivial IsSimpleRing.instNontrivial NonUnitalCStarAlgebra.toNormedSpace
  CompleteLattice.toCompletePartialOrder

namespace AF

open Filter Topology

open scoped Polynomial LaurentSeries RatFunc

section Series

variable {K : Type*} [Field K]

/-- `f(z^q)`, on power series. -/
noncomputable def substPowSeries (q : ℕ) (f : PowerSeries K) : PowerSeries K :=
  PowerSeries.mk fun n => if q ∣ n then PowerSeries.coeff (n / q) f else 0

variable {ι : Type*} [Fintype ι]

/-- A linear `q`-Mahler system, formally: `f(z) = A(z)·f(z^q)` read in `K⟦z⟧`. -/
def IsFormalMahlerSolution (q : ℕ) (A : Matrix ι ι K[X]) (F : ι → PowerSeries K) : Prop :=
  ∀ i, F i = ∑ j, (A i j : PowerSeries K) * substPowSeries q (F j)

end Series

/-! ## [AF17] Lemme 2.2 -/

/-- **[AF17] Lemme 2.2.**  *«Soient `f₁,…,f_n` des solutions d'un système mahlérien de type
(1.2).  Alors l'extension `ℚ̄(z)(f₁,…,f_n)/ℚ̄(z)` est régulière.»*

In characteristic zero «regular» is «`K(z)` is relatively algebraically closed», i.e.
`AF.IsRegularSolField`.  The hypotheses are those of [AF17]'s (1.2) and nothing more:
characteristic zero (essential — in characteristic `p` the statement fails by Christol's
theorem), `q ≥ 2`, and a matrix invertible over `K(z)`.

**Cited axiom [AF17].**  No analysis appears and no convergence is assumed of the `fᵢ`: the
statement is about a single field extension.  The one step of its literature proof chain that
Mathlib cannot yet supply is [Lan02] Chap. VIII Ex. 4. -/
axiom lemme_2_2 {K : Type*} [Field K] [CharZero K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : ℕ} (hq : 2 ≤ q)
    {A : Matrix ι ι K[X]} (hA : A.det ≠ 0) {F : ι → PowerSeries K}
    (hF : IsFormalMahlerSolution q A F) :
    IsRegularSolField K fun i => ((F i : PowerSeries K) : LaurentSeries K)

/-! ## [AF22] Lemme 2.8 -/

/-- **[AF22] Lemma 2.8 — the branch-existence axiom, with the four clauses the assembly needs.**
*«Let `φ(z) ∈ GLₘ(A)` be a relation matrix.  Then for `k ≫ 1`: (a) `α^{q^k}` belongs to the disc
of convergence of each `f_i`; (b) each coordinate of `φ(z)` defines an analytic function on some
neighborhood of `α^{q^k}`; (c) the matrix `φ(α^{q^k})` is invertible.»*

The abstract ambient field has no functions in it, so «defines an analytic function near `ξ`»
becomes: the subring generated by `K[z]`, the entries and the solutions admits a homomorphism
into the germs of complex functions along `𝓟 U`, realizing polynomials by polynomial functions,
the entries by an analytic `Ψ` and the solutions by their sums.  The two hypotheses that are easy
to get wrong are `[IsAlgClosed K]` and the algebraicity being required of the *entries* rather
than of `Ω`.

**Cited axiom [AF22].**  The last clause is stated for an arbitrary `s` implementing the
substitution `z ↦ z^{q^{k₀}}` on `K(z)`, so that the axiom assumes nothing about `s`. -/
axiom lemma_2_8 {K : Type*} [Field K] [IsAlgClosed K] {Ω : Type*} [Field Ω]
    [Algebra (LaurentSeries K) Ω] [Algebra (RatFunc K) Ω]
    [IsScalarTower (RatFunc K) (LaurentSeries K) Ω]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (φ : K →+* ℂ) {α : K}
    (hα0 : α ≠ 0) (hα1 : ‖φ α‖ < 1) {q : ℕ} (hq : 2 ≤ q) {Φalg : Matrix ι ι Ω}
    (halg : ∀ i j, IsIntegral (RatFunc K) (Φalg i j)) (hdet : Φalg.det ≠ 0)
    {r : ℝ} (hr0 : 0 < r) {f : ι → PowerSeries K} {fs : ι → ℂ → ℂ}
    (hsum : ∀ i, IsSeriesSumOn r φ (f i) (fs i)) :
    ∀ᶠ k₀ in atTop, ∃ (U : Set ℂ) (R : Subring Ω) (real : R →+* Germ (𝓟 U) ℂ)
      (Ψ : ℂ → Matrix ι ι ℂ) (Φ₀ : Matrix ι ι K),
      IsAnalyticBranch φ Φalg (φ α ^ q ^ k₀) U R real Ψ Φ₀ ∧ IsPreconnected U ∧
      IsSolutionRealization (𝓟 U) (fun i => toAmbientSeries K Ω (f i)) R real fs ∧
      IsAnalyticRealization U R real ∧ Function.Injective real ∧
      ∀ s : Ω →+* Ω, (∀ (hn : 0 < q ^ k₀) (c : RatFunc K),
          s (algebraMap (RatFunc K) Ω c) = algebraMap (RatFunc K) Ω (substPowRat K hn c)) →
        ∃ (V : Set ℂ) (R' : Subring Ω) (real' : R' →+* Germ (𝓟 V) ℂ) (Ψ' : ℂ → Matrix ι ι ℂ),
          IsAnalyticBranch φ (Matrix.of fun l j => s (Φalg l j)) (φ α) V R' real' Ψ' Φ₀

end AF
