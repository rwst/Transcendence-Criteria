import B3.BlockConstruction
import AB.SubspaceTheoremE
import Mathlib.LinearAlgebra.Dual.Defs

namespace B3

open BL AB Function

def subspaceDen (c p : ℕ) : ℤ := 3 ^ c - 2 ^ p

theorem subspaceDen_odd (c p : ℕ) (hp : 0 < p) : Odd (subspaceDen c p) :=
  (Odd.pow ⟨1, by ring⟩).sub_even (Int.even_pow.mpr ⟨even_two, hp.ne'⟩)

noncomputable def subForms (a : ℤ) : Fin 3 → Module.Dual ℚ (Fin 3 → ℚ) :=
  ![LinearMap.proj 0, LinearMap.proj 1,
    (a : ℚ) • LinearMap.proj 0 + (a : ℚ) • LinearMap.proj 1 + LinearMap.proj 2]

theorem subForms_linearIndependent (a : ℤ) : LinearIndependent ℚ (subForms a) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h0 := congrFun (congrArg DFunLike.coe hg) (Pi.single 0 1)
  have h1 := congrFun (congrArg DFunLike.coe hg) (Pi.single 1 1)
  have h2 := congrFun (congrArg DFunLike.coe hg) (Pi.single 2 1)
  simp only [subForms, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    LinearMap.zero_apply, Pi.single_eq_same, smul_eq_mul] at h0 h1 h2
  intro i
  fin_cases i <;> simp_all

end B3
