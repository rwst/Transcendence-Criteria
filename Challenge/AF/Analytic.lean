/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Challenge.AF.Ambient

/-!
# Challenge, the Mahler-method inputs (5/5): analytic branches

Mirrors `CITED/AdamczewskiFaverjon{AnalyticUB,Germ,BranchExistence,ReverseTransport}.lean`, the
last of which owns the auxiliary proof constant `AF.IsAnalyticRealization._proof_1`.  See
`Challenge/AF.lean`.
-/

attribute [-instance] IsDomain.of_isSimpleRing CommCStarAlgebra.toNormedCommRing
  IsLocalRing.toNontrivial IsSimpleRing.instNontrivial NonUnitalCStarAlgebra.toNormedSpace
  CompleteLattice.toCompletePartialOrder

namespace AF

open Filter Topology

open scoped Polynomial RatFunc

section SeriesSum

variable {K : Type*} [Field K]

/-- `H` is the sum of the series `g` on the disc of radius `r`, coefficients transported by `φ`. -/
def IsSeriesSumOn (r : ℝ) (φ : K →+* ℂ) (g : PowerSeries K) (H : ℂ → ℂ) : Prop :=
  ∀ u : ℂ, ‖u‖ < r → HasSum (fun n => φ (PowerSeries.coeff n g) * u ^ n) (H u)

end SeriesSum

section BranchRealization

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra (RatFunc K) Ω]
variable {ι : Type*}

/-- The ambient subring `R` is realized by germs of complex functions along `l`, polynomials by
polynomial functions and the entries of `Φalg` by the entries of `Ψ`. -/
structure IsBranchRealization (φ : K →+* ℂ) (l : Filter ℂ) (Φalg : Matrix ι ι Ω) (R : Subring Ω)
    (real : R →+* Germ l ℂ) (Ψ : ℂ → Matrix ι ι ℂ) : Prop where
  /-- Every polynomial in `z`, read in the ambient field, lies in the subring. -/
  poly_mem : ∀ w : K[X], toAmbient K Ω w ∈ R
  /-- …and is realized by the polynomial function with coefficients transported by `φ`. -/
  real_poly : ∀ w : K[X],
    real ⟨toAmbient K Ω w, poly_mem w⟩ = ((fun z : ℂ => (w.map φ).eval z : ℂ → ℂ) : Germ l ℂ)
  /-- Every entry of the relation matrix lies in the subring. -/
  mat_mem : ∀ i j, Φalg i j ∈ R
  /-- …and is realized by the corresponding entry of the analytic matrix `Ψ`. -/
  real_mat : ∀ i j,
    real ⟨Φalg i j, mat_mem i j⟩ = ((fun z : ℂ => Ψ z i j : ℂ → ℂ) : Germ l ℂ)

end BranchRealization

section AnalyticBranch

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra (RatFunc K) Ω]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An analytic branch of the relation matrix at `ξ`, with value `Φ₀` defined over `K`. -/
structure IsAnalyticBranch (φ : K →+* ℂ) (Φalg : Matrix ι ι Ω) (ξ : ℂ) (U : Set ℂ)
    (R : Subring Ω) (real : R →+* Germ (𝓟 U) ℂ) (Ψ : ℂ → Matrix ι ι ℂ)
    (Φ₀ : Matrix ι ι K) : Prop where
  /-- The branch is defined on an open set … -/
  isOpen_dom : IsOpen U
  /-- … containing the point. -/
  mem_dom : ξ ∈ U
  /-- **Lemma 2.8(b)**: every entry of the branch is analytic there. -/
  analytic : ∀ i j, AnalyticOnNhd ℂ (fun z => Ψ z i j) U
  /-- The branch realizes the ambient data: `AF.IsBranchRealization`. -/
  isBranch : IsBranchRealization φ (𝓟 U) Φalg R real Ψ
  /-- **Lemma 2.8(c), first half**: the value at `ξ` is defined over `K`. -/
  map_value : Φ₀.map φ = Ψ ξ
  /-- **Lemma 2.8(c), second half**: and invertible. -/
  det_ne_zero : Φ₀.det ≠ 0

end AnalyticBranch

section Realization

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra (RatFunc K) Ω] {ι : Type*}

/-- The solutions lie in the realization subring and are realized by the analytic solutions. -/
structure IsSolutionRealization (l : Filter ℂ) (f : ι → Ω) (R : Subring Ω)
    (real : R →+* Germ l ℂ) (fs : ι → ℂ → ℂ) : Prop where
  /-- Every solution lies in the realization subring. -/
  sol_mem : ∀ i, f i ∈ R
  /-- …and is realized by the corresponding analytic solution. -/
  real_sol : ∀ i, real ⟨f i, sol_mem i⟩ = ((fs i : ℂ → ℂ) : Germ l ℂ)

/-- Every element of the realization subring is realized by a function analytic on `U`. -/
def IsAnalyticRealization (U : Set ℂ) (R : Subring Ω) (real : R →+* Germ (𝓟 U) ℂ) : Prop :=
  ∀ x : R, ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧ real x = ((g : ℂ → ℂ) : Germ (𝓟 U) ℂ)

end Realization

end AF
