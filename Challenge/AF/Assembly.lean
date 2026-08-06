/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Challenge.AF.Primitive

/-!
# Challenge, the Mahler-method inputs (3/5): polynomials in the ambient field

Mirrors `CITED/AdamczewskiFaverjonAssembly.lean`, which owns the auxiliary proof constant
`AF.toAmbient._proof_1`.  See `Challenge/AF.lean`.
-/

attribute [-instance] IsDomain.of_isSimpleRing CommCStarAlgebra.toNormedCommRing
  IsLocalRing.toNontrivial IsSimpleRing.instNontrivial NonUnitalCStarAlgebra.toNormedSpace
  CompleteLattice.toCompletePartialOrder

namespace AF

open scoped Polynomial RatFunc

/-- Polynomials in `z`, read in the ambient field. -/
noncomputable def toAmbient.{u_4, u_5} (K : Type u_4) [Field K] (Ω : Type u_5) [Field Ω]
    [Algebra (RatFunc K) Ω] :
    K[X] →+* Ω :=
  (algebraMap (RatFunc K) Ω).comp (algebraMap K[X] (RatFunc K))

end AF
