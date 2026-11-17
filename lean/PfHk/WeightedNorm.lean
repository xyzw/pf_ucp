import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section
namespace PfHk.WeightedNorm

open MeasureTheory

set_option maxHeartbeats 20000
set_option Elab.async false

variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H] {μ : Measure X}

theorem sub_sq_bound (u v : H) : ‖u - v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le u v) 2
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]

theorem add_sq_bound (u v : H) : ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le u v) 2
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]

/-- Integrability of two weighted fields proves integrability of their
difference and its weighted norm-square estimate. -/
theorem sub_integrable_bound {w : X → ℝ} {f g h : X → H}
    (hw : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hm : AEStronglyMeasurable (fun x => w x * ‖h x‖ ^ 2) μ)
    (hf : Integrable (fun x => w x * ‖f x‖ ^ 2) μ)
    (hg : Integrable (fun x => w x * ‖g x‖ ^ 2) μ)
    (hh : h =ᵐ[μ] fun x => f x - g x) :
    Integrable (fun x => w x * ‖h x‖ ^ 2) μ ∧
      (∫ x, w x * ‖h x‖ ^ 2 ∂μ) ≤
        2 * (∫ x, w x * ‖f x‖ ^ 2 ∂μ) + 2 * (∫ x, w x * ‖g x‖ ^ 2 ∂μ) := by
  have hmajor : Integrable (fun x =>
      2 * (w x * ‖f x‖ ^ 2) + 2 * (w x * ‖g x‖ ^ 2)) μ :=
    (hf.const_mul 2).add (hg.const_mul 2)
  have hb : ∀ᵐ x ∂μ, w x * ‖h x‖ ^ 2 ≤
      2 * (w x * ‖f x‖ ^ 2) + 2 * (w x * ‖g x‖ ^ 2) := by
    filter_upwards [hw, hh] with x hx heq
    have hn := mul_le_mul_of_nonneg_left (sub_sq_bound (f x) (g x)) hx
    rw [heq]
    nlinarith
  have hi : Integrable (fun x => w x * ‖h x‖ ^ 2) μ :=
    hmajor.mono' hm (by
      filter_upwards [hw, hb] with x hx hbx
      simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx (sq_nonneg _))] using hbx)
  refine ⟨hi, (integral_mono_ae hi hmajor hb).trans_eq ?_⟩
  rw [integral_add (hf.const_mul 2) (hg.const_mul 2), integral_const_mul, integral_const_mul]

end PfHk.WeightedNorm
