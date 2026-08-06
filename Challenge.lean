/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Challenge.Orbit
import Challenge.Cited
import Challenge.AF
import Challenge.NKR
import Challenge.Kernel

/-!
# The comparator challenge: what this repository claims, stated against Mathlib alone

This file and the four modules it imports are the **trusted statement of record** for
`leanprover/comparator` (see `comparator/*.json` and `lake test`).

They import *nothing but Mathlib*, and they re-declare — verbatim — every definition that
occurs in the certified theorems, followed by those theorems with `sorry` proofs.
`Solution.lean` merely imports the real development.  Comparator then checks that

1. every constant in the transitive closure of these statements is **identical** in the
   challenge and the solution environments (so the definitions really are the ones the
   repository proves things about — a divergent `RB.x`, `AS.complexity` or
   `RB.scaledViolators` would be caught here),
2. the solution's proofs use **no axioms beyond those permitted** by the config, and
3. the solution's environment is **re-accepted by the Lean kernel** from a fresh export.

Consequently, auditing this repository's headline claims reduces to reading *these files*:
if the definitions say what you think they say, comparator has verified the rest.

## The parts

| Module | Contents | Mirrors |
| --- | --- | --- |
| `Challenge.Orbit` | `distToNearestInt`, `factor`, `RB.x`, `RB.wmin`, `RB.K`, `RB.IsRepetition` | `ForMathlib/`, `RB/Basic.lean` |
| `Challenge.Cited` | `AS.*`, `Subspace.*`, and the axioms [Sch91], [CZ04] | `CITED/` |
| `Challenge.AF` | the Mahler-method definitions and the axioms [AF17], [AF22] | `CITED/AdamczewskiFaverjon*.lean` |
| `Challenge.NKR` | `NKR.uval` and the refutation of the unrepaired NKR Thm 1.3(i) | `CITED/NairKumarRout.lean` |
| `Challenge.Kernel` | the violator sets and all fifteen certified theorems | `RB/` |

The split is not cosmetic: Lean shares a declaration's auxiliary proof constants
(`RB.K._proof_1` and friends) only *within* a module, so collapsing the development's
module boundaries would rename them and comparator would report a mismatch.
`Challenge/Orbit.lean` documents this in full.

## The six configurations, and why there are six

The paper's Appendix (§Formalization) records a per-theorem axiom footprint.  The configs
in `comparator/` pin that stratification down mechanically, one config per lane, so that a
theorem can never quietly acquire an axiom it is claimed not to use.  "std3" abbreviates
`propext`, `Quot.sound`, `Classical.choice`.

| Config | Lane | Permitted axioms |
| --- | --- | --- |
| `rigidity.json` | 2-adic rigidity, aperiodicity, closed form, the NKR refutation | std3 |
| `af.json` | the algebraic *irrational* half | std3 + `AF.lemme_2_2` + `AF.lemma_2_8` |
| `kernel.json` | the Diophantine kernel and the dichotomy (Theorem B) | std3 + `Subspace.evertseSchlickewei` |
| `criteria.json` | **Theorem A**, the transcendence criterion | std3 + AF + Subspace |
| `algslice.json` | the algebraic-multiplier bounded-gap kernel | std3 + `CZ.pseudoPisot_approx_alg` |
| `algebraic.json` | the algebraic-multiplier upgrade and close repetitions | std3 + CZ + Subspace |

Note that permitting an axiom by name is *not* a loophole: comparator compares the types of
permitted axioms across the two environments too, so the solution cannot smuggle in an
`AF.lemme_2_2 : False`.  The four cited axioms are therefore declared verbatim — [Sch91] and
[CZ04] in `Challenge/Cited.lean`, [AF17] Lemme 2.2 and [AF22] Lemme 2.8 in
`Challenge/AF.lean` — so that a reader sees exactly what is taken on faith.

The AF lane's boundary moved once: [AF17] Corollaire 1.8 used to be the axiom, and is now a
*theorem* of the development, proved along [AF22]'s new proof of Nishioka's theorem from the
two lemmas of that proof which the development does not reprove.  The lane got deeper, not
wider — `AF.transcendental_or_rat_of_automatic` is still where the `RB/` results enter it.

The stratification is enforced, not decorative: swapping `kernel.json` to std3 alone makes
comparator report `Illegal axiom detected: 'Subspace.evertseSchlickewei'`.

Nothing here is proved; the `sorry`s are the point.
-/
