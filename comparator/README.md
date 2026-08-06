# Certifying this repository with `comparator`

[`leanprover/comparator`](https://github.com/leanprover/comparator) is a trustworthy judge
for Lean proofs. Here it is used as a **self-audit**: it checks that the development really
proves the statements this repository claims, using only the axioms this repository admits.

Given `Challenge.lean` (the statements, importing *Mathlib only*, proofs `sorry`) and
`Solution.lean` (a bare re-export of the development), comparator independently verifies:

1. **Statement match** — every constant in the transitive closure of the certified
   statements is *identical* in both environments. An `RB.x`, `RB.K`, `AS.complexity` or
   `RB.scaledViolators` that drifted from the one in `Challenge.lean` is caught here.
2. **Axiom discipline** — the proofs reach for no axiom outside the config's
   `permitted_axioms`, and a permitted axiom's *type* is compared across both
   environments too (so a cited axiom cannot be quietly restated as `False`).
3. **Kernel replay** — the exported solution environment is re-accepted from scratch by
   the Lean kernel, via `lean4export` + `Lean4Checker`, without loading any `.olean`.

Auditing the headline claims therefore reduces to **reading `Challenge.lean`** and the four
modules it imports:

| Module | Contents | Mirrors |
| --- | --- | --- |
| `Challenge/Orbit.lean` | `distToNearestInt`, `factor`, `RB.x`, `RB.wmin`, `RB.K`, `RB.IsRepetition` | `ForMathlib/`, `RB/Basic.lean` |
| `Challenge/Cited.lean` | `AS.*`, `Subspace.*`, and the axioms [Sch91], [CZ04] | `CITED/` |
| `Challenge/AF.lean` (+ `Challenge/AF/`) | the Mahler-method definitions and the axioms [AF17], [AF22] | `CITED/AdamczewskiFaverjon*.lean` |
| `Challenge/NKR.lean` | `NKR.uval` and the refutation of the unrepaired NKR Thm 1.3(i) | `CITED/NairKumarRout.lean` |
| `Challenge/Kernel.lean` | the violator sets and all fifteen certified theorems | `RB/` |

The split mirrors the development's module boundaries on purpose. Lean shares a
declaration's auxiliary proof constants (`RB.K._proof_1` and friends) only *within* a
module, so a single-module challenge would make `CZ.svalR` and `RB.algViolators` point at
`RB.K`'s auxiliaries and comparator would report a mismatch — real at the level of
constants, though the statements are identical. `Challenge/Orbit.lean` documents this.

## The six configs

The paper's formalization appendix records a per-theorem axiom footprint. These configs pin
that stratification down mechanically, one config per lane, and CI fails if it ever
regresses. "std3" abbreviates `propext`, `Quot.sound`, `Classical.choice`.

| Config | Theorems | Permitted axioms |
| --- | --- | --- |
| `rigidity.json` | `RB.isRepetition_iff_dvd`, `RB.complexity_eq_ncard_residues`, `RB.not_eventually_periodic`, `RB.closed_form`, `NKR.thm13i_unrepaired_false` | std3 |
| `af.json` | `RB.not_automatic_of_K_algebraic_irrational`, `RB.transcendental_of_automatic_of_irrational` | std3 + `AF.lemme_2_2` + `AF.lemma_2_8` |
| `kernel.json` | `RB.scaledViolators_finite`, `RB.superlinear_of_K_rat`, `RB.superlinear_or_K_irrational` (**Theorem B**) | std3 + `Subspace.evertseSchlickewei` |
| `criteria.json` | `RB.not_automatic_of_K_algebraic`, `RB.transcendental_of_automatic` (**Theorem A**) | std3 + AF + Subspace |
| `algslice.json` | `RB.algGapBounded_slice_finite` | std3 + `CZ.pseudoPisot_approx_alg` |
| `algebraic.json` | `RB.superlinear_of_K_algebraic_of_pairBranch`, `RB.closeRepetitions_finite_of_K_algebraic` | std3 + CZ + Subspace |

So `criteria.json` certifies the paper's target — *if the minimal word of `xₙ₊₁ = ⌈3xₙ/2⌉`
is automatic then `K(x₀)` is transcendental* — resting on the Subspace Theorem and the two
Mahler-method lemmas and *nothing else*: no `sorry`, no further axiom, no open hypothesis.

"AF" in the table above means `AF.lemme_2_2` + `AF.lemma_2_8`, the two lemmas of [AF22]'s
proof of Nishioka's theorem that the development does not reprove. It used to mean the single
axiom `AF.transcendental_or_rat_of_automatic` ([AF17] Corollaire 1.8); that is now a *theorem*
of the development, so the lane's boundary sits one layer deeper — deeper, not wider.

The other five keep the finer claims honest, in particular:

* `rigidity.json` certifies that 2-adic rigidity, aperiodicity, the Odlyzko–Wilf closed
  form and the machine-checked refutation of the unrepaired NKR Theorem 1.3(i) lean on no
  cited literature at all;
* `kernel.json` certifies that the dichotomy (Theorem B) stays out of the Mahler lane
  entirely — it uses no AF;
* `algslice.json` / `algebraic.json` isolate the fourth lane: the Corvaja–Zannier
  algebraic-multiplier axiom carries the §algmult results and nothing outside them.

The stratification is enforced, not decorative: swapping `kernel.json` to std3 alone makes
comparator report `Illegal axiom detected: 'Subspace.evertseSchlickewei'`.

Note that the two `Subspace`-derived approximation theorems — the Corvaja–Zannier Main
Theorem at `δ ∈ ℚ` and the repaired Nair–Kumar–Rout pair theorem — are *derived* in the
development rather than assumed, which is exactly why they do not appear in any
`permitted_axioms` list.

## Install

Comparator is a Lake dependency (`lakefile.lean`), so Lake builds it and `lean4export` at
the toolchain this project pins — nothing to install by hand:

```sh
lake build comparator lean4export
```

`landrun` is the one exception: it has no pinned release, so build it from source. It uses
**Landlock**, so this is **Linux-only** (check with `grep LANDLOCK /boot/config-$(uname -r)`);
building it needs [Go](https://go.dev/dl/).

```sh
git clone https://github.com/Zouuup/landrun && cd landrun
go build -o ~/.local/bin/landrun cmd/landrun/main.go   # ensure ~/.local/bin is on PATH
```

## Run

```sh
lake build Challenge Solution   # prebuild: the sandbox has no network
lake test                       # runs comparator on all six configs
```

A successful run prints `Your solution is okay!` once per config. To run a single config:

```sh
lake test -- comparator/criteria.json
```

Each binary can be overridden by environment variable — `COMPARATOR_BIN`,
`COMPARATOR_LEAN4EXPORT`, `COMPARATOR_LANDRUN` — which is also how to substitute
comparator's `scripts/fake-landrun.sh` shim on a machine without Landlock. That shim does
**not** sandbox anything; it still exercises the statement match, the axiom check and the
kernel replay, which are the three properties that matter for a self-audit.

## A note on the sandbox

Comparator's threat model targets an *adversarial* solution: it sandboxes every build with
`landrun` and, for full hardening against a known landrun escape (fixed in Linux 7.1), asks
to be wrapped in

```sh
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty -E PATH="$PATH" \
  --working-directory "$(pwd)" -- bash -c 'lake test'
```

Here the solution is our own code, so the sandbox is belt-and-braces; the load-bearing
guarantees are the statement match, the axiom check, and the independent kernel replay.
That is also why CI prebuilds `Challenge` and `Solution` outside the sandbox (which has no
network, and `Challenge` imports all of Mathlib).

CI: `.github/workflows/comparator.yml`.
