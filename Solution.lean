/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import RB.Rigidity
import RB.Residues
import RB.ClosedForm
import RB.NotAutomatic
import RB.ScaledKernel
import RB.RationalK
import RB.AlgebraicKernel
import CITED.NairKumarRout
import CITED.SubspaceTheorem
import CITED.AdamczewskiFaverjon
import CITED.CorvajaZannierAlgebraic

/-!
# The comparator solution: the real development

The counterpart of `Challenge.lean`.  Where the challenge *states* the certified theorems
(against Mathlib alone, with `sorry` proofs), this file simply **imports the actual
proofs**, so that the constants

* `RB.isRepetition_iff_dvd`, `RB.not_eventually_periodic`   (`RB.Rigidity`)
* `RB.complexity_eq_ncard_residues`   (`RB.Residues`)
* `RB.closed_form`   (`RB.ClosedForm`)
* `NKR.thm13i_unrepaired_false`   (`CITED.NairKumarRout`)
* `RB.not_automatic_of_K_algebraic_irrational`,
  `RB.transcendental_of_automatic_of_irrational`   (`RB.NotAutomatic`)
* `RB.scaledViolators_finite`   (`RB.ScaledKernel`)
* `RB.superlinear_of_K_rat`, `RB.superlinear_or_K_irrational`,
  `RB.not_automatic_of_K_algebraic`, `RB.transcendental_of_automatic`   (`RB.RationalK`)
* `RB.algGapBounded_slice_finite`, `RB.superlinear_of_K_algebraic_of_pairBranch`,
  `RB.closeRepetitions_finite_of_K_algebraic`   (`RB.AlgebraicKernel`)
* the three cited axioms `Subspace.evertseSchlickewei`,
  `AF.transcendental_or_rat_of_automatic`, `CZ.pseudoPisot_approx_alg`   (`CITED/`)

are present in this module's environment with their genuine proofs and their genuine
definitional dependencies.  Comparator exports both environments and compares them; see
`Challenge.lean` for what that buys you, and `lake test` to run it.

There is deliberately no content here.  Anything proved *in this file* would be outside the
scope of what comparator checks against the challenge, so the file must stay a pure
re-export of the development.
-/
