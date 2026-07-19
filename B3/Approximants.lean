import B3.StammeringApproximants

namespace B3

open BL Function Filter

theorem Φ_isometry (x y : ℤ_[2]) : ‖Φ x - Φ y‖ = ‖x - y‖ := by
  have hsb : Solenoidal (⇑Φ) ∧ Function.Bijective (⇑Φ) :=
    ⟨Φ_solenoidal, Φ.injective, Φ.surjective⟩
  have hiso := ((BL.corollary_A3 (⇑Φ)).out 0 2).mp hsb
  exact hiso x y

theorem norm_sub_le_of_toZModPow_eq {x y : ℤ_[2]} {N : ℕ}
    (h : PadicInt.toZModPow N x = PadicInt.toZModPow N y) : ‖x - y‖ ≤ (2 : ℝ) ^ (-(N : ℤ)) := by
  have hdvd : (2 : ℤ_[2]) ^ N ∣ (x - y) := (toZModPow_eq_iff_dvd_sub x y N).mp h
  simpa using (dvd_pow_iff_norm_le (x - y) N).mp hdvd

theorem approximant_distance_eq {v α : ℤ_[2]} {n : ℕ} (hv : Φ v = (n : ℤ_[2])) :
    ‖(n : ℤ_[2]) - Φ α‖ = ‖v - α‖ := by
  rw [← hv]; exact Φ_isometry v α

theorem approximant_distance_bound {v α : ℤ_[2]} {n N : ℕ} (hv : Φ v = (n : ℤ_[2]))
    (hagree : PadicInt.toZModPow N v = PadicInt.toZModPow N α) :
    ‖(n : ℤ_[2]) - Φ α‖ ≤ (2 : ℝ) ^ (-(N : ℤ)) := by
  rw [approximant_distance_eq hv]
  exact norm_sub_le_of_toZModPow_eq hagree

end B3
