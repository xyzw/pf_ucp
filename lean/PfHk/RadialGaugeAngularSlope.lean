import PfHk.RadialGaugeCurvature
import PfHk.L2ParameterDerivative

/-! Uniform local difference-quotient bounds for the physical angular
labels. These bounds justify the strong L2 derivative on the unit sphere. -/

noncomputable section
namespace PfHk.RadialGauge

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.SymmetricLift GptLean.Representability PfHk.PhysicalFieldRegularity
open scoped ENNReal InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 600000

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)

def curvatureConstant : ℝ :=
  2 * Fintype.card (Fin N × Fin 3) * |e| * momentBound F χ hUV

theorem curvatureConstant_nonneg : 0 ≤ curvatureConstant (N := N) F χ hUV e := by
  unfold curvatureConstant
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (abs_nonneg _))
    (momentBound_nonneg F χ hUV)

/-- A uniform bound for the physical angular field label on each sphere. -/
theorem angularLabel_norm_le (θ ζ : Configuration N)
    (hθ : ‖θ‖ ≤ 1) (hζ : ‖ζ‖ ≤ 1) {r : ℝ} (hr : 0 ≤ r) :
    ‖angularLabel F χ hUV e θ ζ r‖ ≤ r ^ 2 * curvatureConstant (N := N) F χ hUV e := by
  have hC := curvatureConstant_nonneg (N := N) F χ hUV e
  have hdir : ‖θ‖ * ‖ζ‖ ≤ 1 :=
    (mul_le_mul hθ hζ (norm_nonneg _) (by norm_num)).trans_eq (by ring)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := r) (C := r * curvatureConstant (N := N) F χ hUV e)
    (f := fun s => s • curvature F χ hUV e (s • θ) θ ζ) (by
      intro s hs
      rw [Set.uIoc_of_le hr] at hs
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1.le]
      have hb := curvature_norm_le F χ hUV e (s • θ) θ ζ
      have h₁ := mul_le_mul_of_nonneg_left hdir hC
      have h₂ : ‖curvature F χ hUV e (s • θ) θ ζ‖ ≤
          curvatureConstant (N := N) F χ hUV e := by
        change ‖curvature F χ hUV e (s • θ) θ ζ‖ ≤ _ at hb
        dsimp only [curvatureConstant] at h₁ ⊢
        nlinarith only [hb, h₁]
      exact (mul_le_mul_of_nonneg_left h₂ hs.1.le).trans
        (mul_le_mul_of_nonneg_right hs.2 hC))
  simpa only [angularLabel, sub_zero, abs_of_nonneg hr, pow_two, mul_assoc, mul_comm, mul_left_comm] using h

theorem angular_derivative_norm_le (θ ζ : Configuration N) (s : ℝ) :
    ‖(-(Real.exp (-s) ^ 2)) • curvature F χ hUV e (Real.exp (-s) • θ) θ ζ‖ ≤
      Real.exp (-2 * s) * curvatureConstant (N := N) F χ hUV e * ‖θ‖ * ‖ζ‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (sq_nonneg _)]
  have h := mul_le_mul_of_nonneg_left
    (curvature_norm_le F χ hUV e (Real.exp (-s) • θ) θ ζ) (sq_nonneg (Real.exp (-s)))
  have heq : Real.exp (-s) ^ 2 = Real.exp (-2 * s) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [heq] at h
  rw [heq]
  unfold curvatureConstant
  nlinarith only [h]

/-- The local slope bound is uniform over unit angular directions. -/
theorem angularLabel_logarithmic_slope_bound (θ ζ : Configuration N)
    (hθ : ‖θ‖ ≤ 1) (hζ : ‖ζ‖ ≤ 1) (t h : ℝ) (hh : |h| ≤ 1) :
    ‖h⁻¹ • (angularLabel F χ hUV e θ ζ (Real.exp (-(t + h))) -
      angularLabel F χ hUV e θ ζ (Real.exp (-t)))‖ ≤
      Real.exp (2 - 2 * t) * curvatureConstant (N := N) F χ hUV e := by
  have hC := curvatureConstant_nonneg (N := N) F χ hUV e
  apply L2ParameterDerivative.local_slope_norm_le (mul_nonneg (Real.exp_pos _).le hC)
    (fun s _ => angularLabel_logarithmic_hasDerivAt F χ hUV e θ ζ s) _ hh
  intro s hs
  have hexp : Real.exp (-2 * s) ≤ Real.exp (2 - 2 * t) :=
    Real.exp_le_exp.mpr (by linarith [hs.1])
  have hnorm : ‖θ‖ * ‖ζ‖ ≤ 1 := by
    nlinarith [mul_le_mul hθ hζ (norm_nonneg ζ) (by norm_num : (0 : ℝ) ≤ 1)]
  have hcoef : 0 ≤ Real.exp (-2 * s) * curvatureConstant (N := N) F χ hUV e := by positivity
  have h₁ := mul_le_mul_of_nonneg_left hnorm hcoef
  have h₂ := mul_le_mul_of_nonneg_right hexp hC
  have h₃ := angular_derivative_norm_le F χ hUV e θ ζ s
  nlinarith

end PfHk.RadialGauge
