import PfHk.UniqueContinuationLIntegral
import PfHk.WeightedNorm

/-! Fatou's lemma applied to the actual outer-minus-inner source. The
weighted error functions are squared norms of fields, rather than scalar
errors postulated independently of a commutator. -/

noncomputable section
namespace PfHk.CarlemanCutoffPassage

open MeasureTheory Filter
open scoped ENNReal Topology

set_option maxHeartbeats 20000
set_option Elab.async false

variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H]
  {μ ν : Measure X}

theorem remove_inner_source {F : ℕ → X → ℝ≥0∞} {f : X → ℝ≥0∞}
    {w : X → ℝ} {outer : X → H} {inner total : ℕ → X → H} {K B : ℝ}
    (hK : 0 ≤ K) (hw : ∀ᵐ x ∂ν, 0 ≤ w x)
    (hF : ∀ n, AEMeasurable (F n) μ)
    (hpoint : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (houter : Integrable (fun x => w x * ‖outer x‖ ^ 2) ν)
    (hinner : ∀ n, Integrable (fun x => w x * ‖inner n x‖ ^ 2) ν)
    (htotal : ∀ n, AEStronglyMeasurable (fun x => w x * ‖total n x‖ ^ 2) ν)
    (hsub : ∀ n, total n =ᵐ[ν] fun x => outer x - inner n x)
    (hcarleman : ∀ n, (∫⁻ x, F n x ∂μ) ≤
      ENNReal.ofReal K * (∫⁻ x, ENNReal.ofReal (w x * ‖total n x‖ ^ 2) ∂ν))
    (hbound : (∫ x, w x * ‖outer x‖ ^ 2 ∂ν) ≤ B)
    (herror : Tendsto (fun n => ∫ x, w x * ‖inner n x‖ ^ 2 ∂ν) atTop (𝓝 0)) :
    (∫⁻ x, f x ∂μ) ≤ ENNReal.ofReal (2 * K * B) := by
  apply UniqueContinuation.cutoff_removal hF hpoint
    (error := fun n => 2 * K * (∫ x, w x * ‖inner n x‖ ^ 2 ∂ν))
  · intro n
    obtain ⟨hi, hb⟩ := WeightedNorm.sub_integrable_bound hw
      (htotal n) houter (hinner n) (hsub n)
    have hp : 0 ≤ᵐ[ν] fun x => w x * ‖total n x‖ ^ 2 :=
      hw.mono fun _ hx => mul_nonneg hx (sq_nonneg _)
    calc
      _ ≤ ENNReal.ofReal K * (∫⁻ x, ENNReal.ofReal (w x * ‖total n x‖ ^ 2) ∂ν) :=
        hcarleman n
      _ = ENNReal.ofReal (K * (∫ x, w x * ‖total n x‖ ^ 2 ∂ν)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hi hp, ENNReal.ofReal_mul hK]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by
        have h₁ := mul_le_mul_of_nonneg_left hb hK
        have h₂ := mul_le_mul_of_nonneg_left hbound
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hK)
        nlinarith)
  · simpa using herror.const_mul (2 * K)

end PfHk.CarlemanCutoffPassage
