import PfHk.WeightedNorm
import PfHk.CarlemanWeights
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Scalar-weight absorption of a real spectral shift. -/

noncomputable section
namespace PfHk.EnergyShiftAbsorption

open MeasureTheory Filter
open scoped ENNReal

set_option Elab.async false
set_option maxHeartbeats 20000

variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H] {μ : Measure X}

theorem absorb {m w : X → ℝ} {f error shifted : X → H}
    (hw : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hm : Integrable m μ) (hf : Integrable (fun x => w x * ‖f x‖ ^ 2) μ)
    (heMeas : AEStronglyMeasurable (fun x => w x * ‖error x‖ ^ 2) μ)
    (hsMeas : AEStronglyMeasurable (fun x => w x * ‖shifted x‖ ^ 2) μ)
    (heq : shifted =ᵐ[μ] fun x => f x - error x)
    (hsmall : ∀ᵐ x ∂μ, 2080 * (w x * ‖error x‖ ^ 2) ≤ m x)
    (hbound : (∫ x, m x ∂μ) ≤ 520 * ∫ x, w x * ‖f x‖ ^ 2 ∂μ) :
    Integrable (fun x => w x * ‖shifted x‖ ^ 2) μ ∧
      (∫ x, m x ∂μ) ≤ 2080 * ∫ x, w x * ‖shifted x‖ ^ 2 ∂μ := by
  have he0 : ∀ᵐ x ∂μ, 0 ≤ w x * ‖error x‖ ^ 2 :=
    hw.mono fun x hx => mul_nonneg hx (sq_nonneg _)
  have he : Integrable (fun x => w x * ‖error x‖ ^ 2) μ := hm.mono' heMeas (by
    filter_upwards [he0, hsmall] with x hx hs
    rw [Real.norm_of_nonneg hx]
    linarith only [hx, hs])
  have hs := (WeightedNorm.sub_integrable_bound hw hsMeas hf he heq).1
  have heNeg : Integrable (fun x => w x * ‖-error x‖ ^ 2) μ := by
    simpa only [norm_neg] using he
  have hreverse : f =ᵐ[μ] fun x => shifted x - -error x := by
    filter_upwards [heq] with x hx
    rw [hx]
    abel
  have htriangle := (WeightedNorm.sub_integrable_bound hw hf.aestronglyMeasurable
    hs heNeg hreverse).2
  simp only [norm_neg] at htriangle
  have heBound : 2080 * (∫ x, w x * ‖error x‖ ^ 2 ∂μ) ≤ ∫ x, m x ∂μ :=
    (integral_const_mul 2080 (fun x => w x * ‖error x‖ ^ 2)).symm.le.trans
      (integral_mono_ae (he.const_mul 2080) hm hsmall)
  exact ⟨hs, by linarith only [hbound, htriangle, heBound]⟩

theorem lintegral_bound {m s : X → ℝ}
    (hm : Integrable m μ) (hs : Integrable s μ)
    (hm0 : ∀ᵐ x ∂μ, 0 ≤ m x) (hs0 : ∀ᵐ x ∂μ, 0 ≤ s x)
    (hbound : (∫ x, m x ∂μ) ≤ 2080 * ∫ x, s x ∂μ) :
    (∫⁻ x, ENNReal.ofReal (m x) ∂μ) ≤
      ENNReal.ofReal 2080 * ∫⁻ x, ENNReal.ofReal (s x) ∂μ := by
  rw [← ofReal_integral_eq_lintegral_ofReal hm hm0,
    ← ofReal_integral_eq_lintegral_ofReal hs hs0, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2080)]
  exact ENNReal.ofReal_le_ofReal hbound

theorem real_smul_norm_sq [NormedSpace ℂ H] (E : ℝ) (v : H) :
    ‖(E : ℂ) • v‖ ^ 2 = E ^ 2 * ‖v‖ ^ 2 := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

theorem lp_real_smul_norm_sq_ae [NormedSpace ℂ H] (E : ℝ) (u : Lp H 2 μ) :
    (fun x => ‖((E : ℂ) • u) x‖ ^ 2) =ᵐ[μ] fun x => E ^ 2 * ‖u x‖ ^ 2 := by
  filter_upwards [Lp.coeFn_smul (E : ℂ) u] with x hx
  exact (congrArg (fun v : H => ‖v‖ ^ 2) hx).trans (real_smul_norm_sq E (u x))

theorem weighted_point {E w m q : ℝ} (h : 2080 * E ^ 2 * w ≤ m) (hq : 0 ≤ q) :
    2080 * (w * (E ^ 2 * q)) ≤ m * q := by
  calc
    _ = (2080 * E ^ 2 * w) * q := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h hq

theorem weight_shift_bound {r α τ E : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hα : 0 < α) (hτ : 0 ≤ τ) (hE : 2080 * E ^ 2 ≤ τ ^ 3)
    (hratio : 0 < r → r ^ (4 : ℝ) / CarlemanWeights.beta α (-Real.log r) ≤ 1) :
    2080 * E ^ 2 * (Real.exp (2 * τ * CarlemanWeights.weight α (-Real.log r)) * r ^ 2) ≤
      Real.exp (2 * τ * CarlemanWeights.weight α (-Real.log r)) * τ ^ 3 *
        CarlemanWeights.beta α (-Real.log r) * (r ^ 2)⁻¹ := by
  rcases hr.eq_or_lt with rfl | hr0
  · simp
  have hb := CarlemanWeights.beta_pos hα (neg_pos.mpr (Real.log_neg hr0 hr1))
  have hrad : r ^ 4 ≤ CarlemanWeights.beta α (-Real.log r) := by
    simpa only [Real.rpow_ofNat, one_mul] using (div_le_iff₀ hb).mp (hratio hr0)
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr0
  have hmul : (2080 * E ^ 2) * r ^ 4 ≤ τ ^ 3 * CarlemanWeights.beta α (-Real.log r) :=
    mul_le_mul hE hrad (by positivity) (pow_nonneg hτ 3)
  have hdiv : (2080 * E ^ 2) * r ^ 2 ≤
      (τ ^ 3 * CarlemanWeights.beta α (-Real.log r)) / r ^ 2 := by
    apply (le_div_iff₀ hr2).mpr
    calc
      _ = (2080 * E ^ 2) * r ^ 4 := by ring
      _ ≤ _ := hmul
  have h := mul_le_mul_of_nonneg_left hdiv
    (Real.exp_pos (2 * τ * CarlemanWeights.weight α (-Real.log r))).le
  simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

theorem parameter_cube_bound (E : ℝ) {τ : ℝ}
    (hτ : max 1 (2080 * E ^ 2) ≤ τ) : 1 ≤ τ ∧ 2080 * E ^ 2 ≤ τ ^ 3 := by
  have ht := (le_max_left 1 (2080 * E ^ 2)).trans hτ
  have hE := (le_max_right 1 (2080 * E ^ 2)).trans hτ
  have ht2 : 1 ≤ τ ^ 2 := one_le_pow₀ ht
  exact ⟨ht, hE.trans (by nlinarith only [ht, ht2])⟩

theorem exists_radius_ratio (α : ℝ) :
    ∃ R : ℝ, 0 < R ∧ R < Real.exp (-2) ∧
      ∀ r : ℝ, 0 < r → r ≤ R → r ^ (4 : ℝ) / CarlemanWeights.beta α (-Real.log r) ≤ 1 := by
  obtain ⟨R, hR, hsmall, hratio⟩ := CarlemanWeights.exists_radius_small α
    (by norm_num : (0 : ℝ) < 4) (by norm_num : (0 : ℝ) < 1)
  exact ⟨R, hR, hsmall, fun r hr hrR => (hratio r hr hrR).le⟩

end PfHk.EnergyShiftAbsorption
