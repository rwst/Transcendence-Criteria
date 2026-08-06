/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Challenge.AF.Subst

/-!
# Challenge, the Mahler-method inputs (2/5): the solution field

Mirrors `CITED/AdamczewskiFaverjonPrimitive.lean`, which owns the auxiliary proof constants
`AF.solField._proof_1` and `AF.IsRegularSolField._proof_1`.  See `Challenge/AF.lean`.
-/

attribute [-instance] IsDomain.of_isSimpleRing CommCStarAlgebra.toNormedCommRing
  IsLocalRing.toNontrivial IsSimpleRing.instNontrivial NonUnitalCStarAlgebra.toNormedSpace
  CompleteLattice.toCompletePartialOrder

namespace AF

open scoped Polynomial RatFunc

section SolField

variable (K : Type*) [Field K] {Ω : Type*} [Field Ω] [Algebra (RatFunc K) Ω]

/-- **The solution field `K(z)(f₁,…,f_n)`** of a Mahler system, inside an ambient field `Ω`. -/
noncomputable def solField {ι : Type*} (f : ι → Ω) : IntermediateField (RatFunc K) Ω :=
  IntermediateField.adjoin (RatFunc K) (Set.range f)

/-- `K(z)` is relatively algebraically closed in the solution field — in characteristic zero,
exactly the regularity of `K(z)(f)/K(z)`. -/
def IsRegularSolField {ι : Type*} (f : ι → Ω) : Prop :=
  algebraicClosure (RatFunc K) ↥(solField K f) = ⊥

end SolField

end AF
