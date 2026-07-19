/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Challenge.NKR

/-!
# Challenge, part 4: the violator sets and the certified theorems

Mirrors `RB/ScaledKernel.lean`, `RB/AlgebraicKernel.lean` and the capstone files
`RB/{Rigidity,Residues,ClosedForm,NotAutomatic,RationalK}.lean`.

The lane headings below name the config that certifies each group; see `comparator/README.md`
for the table and `Challenge.lean` for what comparator checks.
-/


namespace RB

/-- The **`δ`-scaled (K)-violating pairs** at scale `θ`, for a rational multiplier:
`2 ≤ a < c` with `‖δ·((3/2)^c − (3/2)^a)‖ ≤ θ^c`. -/
def scaledViolators (δ θ : ℚ) : Set (ℕ × ℕ) :=
  {p | 2 ≤ p.1 ∧ p.1 < p.2 ∧
    (δ * ((3 / 2 : ℚ) ^ p.2 - (3 / 2 : ℚ) ^ p.1)).distToNearestInt ≤ θ ^ p.2}

/-- The **`δ`-scaled (K)-violating pairs** at scale `θ`, for a *real* multiplier — the
distance now taken in `ℝ`.  The intended instances are algebraic `δ`, in particular
`δ = K(x₀)`. -/
def algViolators (δ : ℝ) (θ : ℚ) : Set (ℕ × ℕ) :=
  {p | 2 ≤ p.1 ∧ p.1 < p.2 ∧
    distToNearestInt (δ * ((3 / 2 : ℝ) ^ p.2 - (3 / 2 : ℝ) ^ p.1)) ≤ (θ : ℝ) ^ p.2}

/-- **Close repetitions**: pairs `2 ≤ a < c` with gap `c − a ≤ S` whose windows of length
`⌊c/L⌋ + 1` coincide — long repeats at bounded distance, window a fixed fraction of
position. -/
def closeRepetitions (x₀ S L : ℕ) : Set (ℕ × ℕ) :=
  {p | 2 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ p.1 + S ∧ IsRepetition x₀ p.1 p.2 (p.2 / L + 1)}

/-! ### Lane 1 — rigidity, aperiodicity, closed form (std3) -/

/-- **Window rigidity**: length-`m` windows of `w` at `a` and `b` agree iff the orbit values
agree modulo `2^m`.  The one-line reformulation that organizes the whole paper.

Certified by `comparator/rigidity.json` under std3 alone. -/
theorem isRepetition_iff_dvd {x₀ a b m : ℕ} :
    IsRepetition x₀ a b m ↔ (2 : ℤ) ^ m ∣ (x x₀ b : ℤ) - x x₀ a := sorry

/-- **Complexity is residue counting**: `p_w(m) = #{xₙ mod 2^m : n ≥ 0}`.  Immediate from
window rigidity.

Certified by `comparator/rigidity.json` under std3 alone. -/
theorem complexity_eq_ncard_residues (x₀ m : ℕ) :
    AS.complexity (wmin x₀) m = (Set.range fun n => (x x₀ n : ZMod (2 ^ m))).ncard := sorry

/-- **The minimal word is not eventually periodic** (Akiyama–Frougny–Sakarovitch; Dubickas).
A fixed-gap repetition of every length would beat the repetition ceiling.

Certified by `comparator/rigidity.json` under std3 alone. -/
theorem not_eventually_periodic {x₀ : ℕ} (hx₀ : 0 < x₀) :
    ¬ ∃ N p, 0 < p ∧ ∀ n, N ≤ n → wmin x₀ (n + p) = wmin x₀ n := sorry

/-- **The Odlyzko–Wilf closed form**: `xₙ = ⌊K·(3/2)ⁿ⌋`, unconditionally — no hypothesis on
`K`, and in particular none on its rationality.

Certified by `comparator/rigidity.json` under std3 alone. -/
theorem closed_form {x₀ : ℕ} (hx₀ : 0 < x₀) (n : ℕ) :
    ⌊K x₀ * (3 / 2) ^ n⌋ = (x x₀ n : ℤ) := sorry

/-! ### Lane 2 — the algebraic irrational half (std3 + [AF17]) -/

/-- **The algebraic irrational half**: if `K(x₀)` is an algebraic irrational, then the
minimal word is **not automatic**.  Both branches of the Mahler-method alternative die at
once: `3(K − x₀)` cannot be transcendental (`K` is algebraic) and cannot be rational (`K` is
irrational).

Certified by `comparator/af.json` under std3 plus `AF.transcendental_or_rat_of_automatic`
— no Subspace input. -/
theorem not_automatic_of_K_algebraic_irrational {x₀ : ℕ}
    (halg : IsAlgebraic ℚ (K x₀)) (hirr : Irrational (K x₀)) :
    ¬ AS.IsAutomatic (wmin x₀) := sorry

/-- **The conditional transcendence criterion**: if the minimal word is automatic and `K` is
irrational, then `K` is transcendental.  `K = ω_{3/2}` is not known to be irrational
(open since Wang–Washburn 1977), so the hypothesis is genuine.

Certified by `comparator/af.json` under std3 plus `AF.transcendental_or_rat_of_automatic`. -/
theorem transcendental_of_automatic_of_irrational {x₀ : ℕ}
    (hauto : AS.IsAutomatic (wmin x₀)) (hirr : Irrational (K x₀)) :
    Transcendental ℚ (K x₀) := sorry

/-! ### Lane 3 — the Diophantine kernel and the dichotomy (std3 + [Sub]) -/

/-- **The Diophantine kernel**: for every nonzero rational multiplier `δ` and every scale
`θ ∈ (0,1)`, only finitely many `δ`-scaled (K)-violating pairs exist.

Certified by `comparator/kernel.json` under std3 plus `Subspace.evertseSchlickewei` — the
Corvaja–Zannier and Nair–Kumar–Rout inputs are *derived* from it, not assumed. -/
theorem scaledViolators_finite (δ : ℚ) (hδ : δ ≠ 0) (θ : ℚ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (scaledViolators δ θ).Finite := sorry

/-- **The rational half**: if `K(x₀)` is the rational `δ`, the minimal word's subword
complexity beats **every** linear bound.

Certified by `comparator/kernel.json` under std3 plus `Subspace.evertseSchlickewei`. -/
theorem superlinear_of_K_rat {x₀ : ℕ} (hx₀ : 0 < x₀) {δ : ℚ} (hδK : (δ : ℝ) = K x₀) (C : ℕ) :
    ∃ m, 1 ≤ m ∧ C * m < AS.complexity (wmin x₀) m := sorry

/-- **Theorem B, the dichotomy**: *either* the complexity of the minimal word exceeds every
linear bound, *or* `K(x₀)` is irrational.  Both horns are statements one would like to have
and neither is available alone: the first would beat Dubickas's refereed linear record, the
second is a conditional irrationality statement about `ω_{3/2}`, open since 1977.

Certified by `comparator/kernel.json` under std3 plus `Subspace.evertseSchlickewei` — no
Mahler-method input. -/
theorem superlinear_or_K_irrational {x₀ : ℕ} (hx₀ : 0 < x₀) :
    (∀ C, ∃ m, 1 ≤ m ∧ C * m < AS.complexity (wmin x₀) m) ∨ Irrational (K x₀) := sorry

/-! ### Lane 4 — Theorem A, the transcendence criterion (std3 + [AF17] + [Sub]) -/

/-- **Theorem A**: if `K(x₀)` is algebraic then the minimal word is **not automatic**.  This
is the composition of the two halves — the one statement in the program that carries both
refereed axioms.

Certified by `comparator/criteria.json`. -/
theorem not_automatic_of_K_algebraic {x₀ : ℕ} (hx₀ : 0 < x₀) (halg : IsAlgebraic ℚ (K x₀)) :
    ¬ AS.IsAutomatic (wmin x₀) := sorry

/-- **Theorem A, the reading with content**: *if the minimal word of `xₙ₊₁ = ⌈3xₙ/2⌉` is
automatic, then `K(x₀)` is transcendental.*  It concludes the **transcendence** of a constant
not known to be **irrational**, from a combinatorial hypothesis on the word that generates
it.  This is the repository's headline claim.

Certified by `comparator/criteria.json` under std3 plus
`AF.transcendental_or_rat_of_automatic` and `Subspace.evertseSchlickewei` — and by nothing
else: no `sorry`, no third axiom, no open hypothesis. -/
theorem transcendental_of_automatic {x₀ : ℕ} (hx₀ : 0 < x₀)
    (hauto : AS.IsAutomatic (wmin x₀)) : Transcendental ℚ (K x₀) := sorry

/-! ### Lane 5 — the algebraic-multiplier bounded-gap kernel (std3 + [CZ04]) -/

/-- **The gap-bounded slice for algebraic irrational `δ`**: violators of gap `≤ S` are finite
in number.

Certified by `comparator/algslice.json` under std3 plus `CZ.pseudoPisot_approx_alg` — a
fourth lane, with no Subspace and no Mahler input. -/
theorem algGapBounded_slice_finite (δ : ℝ) (halg : IsAlgebraic ℚ δ)
    (hirr : Irrational δ) (S : ℕ) (θ : ℚ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    {p ∈ algViolators δ θ | p.2 ≤ p.1 + S}.Finite := sorry

/-! ### Lane 6 — the algebraic-multiplier upgrade (std3 + [CZ04] + [Sub]) -/

/-- **The conditional upgrade**: modulo a single named pair statement over `ℚ(K)`, superlinear
complexity follows in *every* algebraic case — retiring the Mahler lane from the algebraic
story entirely.

Certified by `comparator/algebraic.json` under std3 plus `CZ.pseudoPisot_approx_alg` and
`Subspace.evertseSchlickewei`. -/
theorem superlinear_of_K_algebraic_of_pairBranch {x₀ : ℕ} (hx₀ : 0 < x₀)
    (halg : IsAlgebraic ℚ (K x₀))
    (hpair : ∀ θ : ℚ, 0 < θ → θ < 1 → ∀ T ⊆ algViolators (K x₀) θ,
      Set.InjOn (fun p : ℕ × ℕ => p.2 - p.1) T → T.Finite) (C : ℕ) :
    ∃ m, 1 ≤ m ∧ C * m < AS.complexity (wmin x₀) m := sorry

/-- **Close repetitions die out for algebraic `K`** — unconditional, and a second
transcendence criterion with a periodicity-adjacent trigger: if `K(x₀)` is algebraic then
for every gap bound `S` and every slope `1/L`, only finitely many close repetitions exist.
Strictly stronger than aperiodicity on their overlap, and new content for algebraic
irrational `K`, where no complexity statement was previously available at all.

Certified by `comparator/algebraic.json`. -/
theorem closeRepetitions_finite_of_K_algebraic {x₀ : ℕ} (hx₀ : 0 < x₀)
    (halg : IsAlgebraic ℚ (K x₀)) (S L : ℕ) (hL : 1 ≤ L) :
    (closeRepetitions x₀ S L).Finite := sorry

end RB
