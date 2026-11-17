import PfHk.CarlemanAnnularWeights

/-! Exact scalar comparisons used to absorb the quantum Zeeman field.
The radiation comparison has order tau inverse and the mass comparison
has order tau cubed inverse, without differentiating the magnetic field. -/

noncomputable section
namespace PfHk.PauliCarlemanWeights

open PfHk.CarlemanSpatialDensity PfHk.CarlemanWeights PfHk.PolarCalculus

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 20000

variable {I : Type*} [Fintype I]

theorem source_le_radiation {τ α R : ℝ} (hτ : 0 < τ)
    {X : Position I} (hR : ‖X‖ ≤ R) :
    sourceWeight τ α X ≤ (R ^ 2 / (2 * τ)) * radiationWeight τ α X := by
  have hr2 : ‖X‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hR 2
  have h := mul_le_mul_of_nonneg_left hr2
    (Real.exp_pos (2 * τ * weight α (-Real.log ‖X‖))).le
  apply h.trans_eq
  unfold radiationWeight
  field_simp [ne_of_gt hτ]

theorem source_le_mass {τ α σ : ℝ} (hτ : 0 < τ)
    {X : Position I} (hX : 0 < ‖X‖)
    (hratio : ‖X‖ ^ 4 ≤ σ * beta α (-Real.log ‖X‖)) :
    sourceWeight τ α X ≤ (σ / τ ^ 3) * massWeight τ α X := by
  have hr2 : 0 < ‖X‖ ^ 2 := sq_pos_of_pos hX
  have hquot : ‖X‖ ^ 2 ≤ σ * beta α (-Real.log ‖X‖) / ‖X‖ ^ 2 := by
    apply (le_div_iff₀ hr2).mpr
    simpa only [← pow_add] using hratio
  have h := mul_le_mul_of_nonneg_left hquot
    (Real.exp_pos (2 * τ * weight α (-Real.log ‖X‖))).le
  apply h.trans_eq
  unfold massWeight
  field_simp [ne_of_gt hτ, ne_of_gt hX]

end PfHk.PauliCarlemanWeights
