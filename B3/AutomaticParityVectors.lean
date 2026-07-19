import BL.ConjugacyMap
import CITED.AlloucheShallitBasic

namespace B3

open BL Function

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

noncomputable def binaryDigit (v : ℤ_[2]) (k : ℕ) : ℕ := parity (S^[k] v)

def IsAutomatic2Adic (v : ℤ_[2]) : Prop := AS.IsAutomatic (binaryDigit v)

noncomputable def parityVector (n : ℕ) : ℤ_[2] := Q (n : ℤ_[2])

theorem Φ_parityVector (n : ℕ) : Φ (parityVector n) = (n : ℤ_[2]) := by
  unfold parityVector
  rw [← Φ_symm_eq_Q]
  exact Φ.apply_symm_apply _

end B3
