import PfHk.CarlemanWeights

/-! Uniform parameter choice for the classical and quantum Zeeman errors.
The quantum contribution has both tau inverse and tau cubed inverse decay. -/

noncomputable section
namespace PfHk.PauliCarlemanSmallness

set_option Elab.async false
set_option maxHeartbeats 20000

theorem exists_parameter {p ε : ℝ} (hp : 2 < p) (hε : 0 < ε)
    (Acl Arad Amass : ℝ) :
    ∃ τ₀ : ℝ, 1 ≤ τ₀ ∧ ∀ τ : ℝ, τ₀ ≤ τ →
      Acl * τ ^ (-(3 - 6 / p)) + Arad * τ ^ (-1 : ℝ) +
        Amass * τ ^ (-3 : ℝ) < ε := by
  have he : 0 < ε / 2 := by positivity
  obtain ⟨a, ha, hcl⟩ := CarlemanWeights.exists_scalar_parameter_small hp he Acl Amass
  obtain ⟨b, _hb, hq⟩ := CarlemanWeights.exists_parameter_small (by norm_num : (0 : ℝ) < 1)
    he Arad 0
  refine ⟨max a b, ha.trans (le_max_left _ _), ?_⟩
  intro τ hτ
  have h₁ := hcl τ ((le_max_left _ _).trans hτ)
  have h₂ := hq τ ((le_max_right _ _).trans hτ)
  simp only [zero_mul, add_zero] at h₂
  linarith only [h₁, h₂]

/-- The two physical error estimates are absorbed after one common
parameter choice. No independence of the spin components is needed. -/
theorem absorb {free full zcl zq error a b c τ p : ℝ}
    (hfree : 0 ≤ free)
    (hclassical : zcl ≤ a * τ ^ (-(3 - 6 / p)) * free)
    (hquantum : zq ≤ (b * τ ^ (-1 : ℝ) + c * τ ^ (-3 : ℝ)) * free)
    (herror : error ≤ 2 * zcl + 2 * zq)
    (htriangle : free ≤ 2 * full + 2 * error)
    (hsmall : a * τ ^ (-(3 - 6 / p)) + b * τ ^ (-1 : ℝ) +
      c * τ ^ (-3 : ℝ) ≤ 1 / 8) :
    free ≤ 4 * full := by
  have hmul := mul_le_mul_of_nonneg_right hsmall hfree
  have he : error ≤ free / 4 := by nlinarith only [hclassical, hquantum, herror, hmul]
  exact CarlemanAlgebra.perturbation_absorption htriangle he

end PfHk.PauliCarlemanSmallness
