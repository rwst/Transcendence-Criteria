/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Challenge.AF.Assembly

/-!
# Challenge, the Mahler-method inputs (4/5): the ambient field of [AF22] §2.2

Mirrors `CITED/AdamczewskiFaverjonMahlerAmbient.lean`, which owns the auxiliary proof constants
`AF.laurentExpand._proof_1` and `AF.Twisted._proof_1` that `AF.toAmbientSeries` reuses.  See
`Challenge/AF.lean`.
-/

attribute [-instance] IsDomain.of_isSimpleRing CommCStarAlgebra.toNormedCommRing
  IsLocalRing.toNontrivial IsSimpleRing.instNontrivial NonUnitalCStarAlgebra.toNormedSpace
  CompleteLattice.toCompletePartialOrder

namespace AF

open scoped Polynomial LaurentSeries RatFunc

section Laurent

variable (K : Type*) [Field K]

/-- **`PowerSeries.expand` is injective.**  Here for the same reason as `AF.matX` in
`Challenge/AF/Subst.lean`: `AF.toAmbientSeries` reuses auxiliary proof constants owned by
`AF.laurentExpand` and `AF.Twisted`, which sit above it in the development's module, so
reproducing the names means reproducing the declarations that create them. -/
theorem expand_injective {n : ℕ} (hn : n ≠ 0) :
    Function.Injective (PowerSeries.expand (R := K) n hn) := by
  intro f g h
  ext m
  have hm := congrArg (PowerSeries.coeff (n * m)) h
  rwa [PowerSeries.coeff_expand, PowerSeries.coeff_expand, if_pos ⟨m, rfl⟩, if_pos ⟨m, rfl⟩,
    Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hn)] at hm

/-- **The substitution `z ↦ z^n` on `K⸨z⸩`**, the fraction field of `K⟦z⟧`. -/
noncomputable def laurentExpand {n : ℕ} (hn : n ≠ 0) : LaurentSeries K →+* LaurentSeries K :=
  IsFractionRing.lift (A := PowerSeries K) (K := LaurentSeries K) (L := LaurentSeries K)
    (g := (algebraMap (PowerSeries K) (LaurentSeries K)).comp
      (PowerSeries.expand n hn).toRingHom)
    (fun _ _ h => expand_injective K hn
      ((IsFractionRing.injective (PowerSeries K) (LaurentSeries K)) h))

end Laurent

/-- **`Ω` with its `K⸨z⸩`-algebra structure twisted by the substitution.** -/
def Twisted (K : Type*) [Field K] (Ω : Type*) [Field Ω] [Algebra (LaurentSeries K) Ω]
    {n : ℕ} (_ : n ≠ 0) : Type _ := Ω

/-- The solutions, read in the ambient field of [AF22] §2.2. -/
noncomputable def toAmbientSeries.{u_4, u_5} (K : Type u_4) [Field K] (Ω : Type u_5) [Field Ω]
    [Algebra (LaurentSeries K) Ω] : PowerSeries K →+* Ω :=
  (algebraMap (LaurentSeries K) Ω).comp (algebraMap (PowerSeries K) (LaurentSeries K))

end AF
