import GptLean.PhysicalSmearedKernel
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
An exponential spatial moment makes each coordinate slice of the physical
Fourier coefficient real analytic.  The proof constructs its complex Laplace
extension and differentiates the integral on an open strip.
-/

noncomputable section

namespace PfHk.ExponentialFourierAnalytic

open MeasureTheory Filter GptLean Gaussian PhysicalGroundState
open scoped Topology InnerProductSpace

set_option Elab.async false
set_option maxHeartbeats 800000

private def laplaceIntegrand (w : FieldSpace → ℝ) (k : FieldSpace)
    (j : Fin 3) (z : ℂ) (x : FieldSpace) : ℂ :=
  fieldPhase k x * Complex.exp (z * (x j : ℂ)) * (w x : ℂ)

/-- Complex extension in one coordinate, with the other momentum coordinates
held fixed. -/
def coordinateLaplace (w : FieldSpace → ℝ) (k : FieldSpace) (j : Fin 3)
    (z : ℂ) : ℂ := ∫ x, laplaceIntegrand w k j z x

private theorem integrand_measurable (w : FieldSpace → ℝ)
    (hw : Integrable w volume) (k : FieldSpace) (j : Fin 3) (z : ℂ) :
    AEStronglyMeasurable (laplaceIntegrand w k j z) volume := by
  have hj : Continuous (fun x : FieldSpace => (x j : ℂ)) := by fun_prop
  exact ((continuous_fieldPhase_right k).mul
    (Complex.continuous_exp.comp (continuous_const.mul hj))).aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hw.1)

private theorem norm_integrand (w : FieldSpace → ℝ) (k : FieldSpace)
    (j : Fin 3) (z : ℂ) (x : FieldSpace) :
    ‖laplaceIntegrand w k j z x‖ = Real.exp (z.re * x j) * |w x| := by
  simp [laplaceIntegrand, norm_fieldPhase, Complex.norm_exp]

private theorem exponent_le (β : ℝ) (hβ : 0 ≤ β) (z : ℂ)
    (hz : |z.re| ≤ β) (j : Fin 3) (x : FieldSpace) :
    z.re * x j ≤ β * ‖x‖ := by
  calc
    z.re * x j ≤ |z.re * x j| := le_abs_self _
    _ = |z.re| * |x j| := abs_mul _ _
    _ ≤ β * ‖x‖ := mul_le_mul hz (PiLp.norm_apply_le x j)
      (abs_nonneg _) hβ

private theorem integrand_integrable (w : FieldSpace → ℝ)
    (hw : Integrable w volume) {β : ℝ} (hβ : 0 ≤ β)
    (hm : Integrable (fun x => Real.exp (β * ‖x‖) * |w x|) volume)
    (k : FieldSpace) (j : Fin 3) (z : ℂ) (hz : |z.re| ≤ β) :
    Integrable (laplaceIntegrand w k j z) volume := by
  refine hm.mono' (integrand_measurable w hw k j z) (ae_of_all _ fun x => ?_)
  rw [norm_integrand]
  exact mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (exponent_le β hβ z hz j x)) (abs_nonneg _)

private theorem linear_exp_bound {β r : ℝ} (hβ : 0 < β) :
    r * Real.exp (β / 2 * r) ≤ (2 / β) * Real.exp (β * r) := by
  have hlinear : r ≤ (2 / β) * Real.exp (β / 2 * r) := by
    have h := Real.add_one_le_exp (β / 2 * r)
    have he : β / 2 * r ≤ Real.exp (β / 2 * r) := by linarith
    have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ 2 / β by positivity)
    field_simp at hm ⊢
    nlinarith
  calc
    r * Real.exp (β / 2 * r) ≤
        ((2 / β) * Real.exp (β / 2 * r)) * Real.exp (β / 2 * r) :=
      mul_le_mul_of_nonneg_right hlinear (Real.exp_pos _).le
    _ = (2 / β) * Real.exp (β * r) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- The coordinate Laplace transform is holomorphic on a strip about the
imaginary axis, obtained directly from the exponential moment. -/
theorem differentiableOn_coordinateLaplace (w : FieldSpace → ℝ)
    (hw : Integrable w volume) {β : ℝ} (hβ : 0 < β)
    (hm : Integrable (fun x => Real.exp (β * ‖x‖) * |w x|) volume)
    (k : FieldSpace) (j : Fin 3) :
    DifferentiableOn ℂ (coordinateLaplace w k j) {z | |z.re| < β / 2} := by
  intro z hz
  have hs : {z : ℂ | |z.re| < β / 2} ∈ 𝓝 z :=
    (isOpen_lt (Complex.continuous_re.abs) continuous_const).mem_nhds hz
  have hderiv := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := laplaceIntegrand w k j)
    (F' := fun z x => laplaceIntegrand w k j z x * (x j : ℂ))
    (bound := fun x => (2 / β) * (Real.exp (β * ‖x‖) * |w x|)) hs
    (Filter.Eventually.of_forall (integrand_measurable w hw k j))
    (integrand_integrable w hw hβ.le hm k j z (hz.le.trans (by linarith)))
    ((integrand_measurable w hw k j z).mul
      (show AEStronglyMeasurable (fun x : FieldSpace => (x j : ℂ)) volume by fun_prop))
    ?_ (hm.const_mul (2 / β)) ?_).2
  · exact hderiv.differentiableAt.differentiableWithinAt
  · refine ae_of_all _ fun x ε hε => ?_
    rw [norm_mul, norm_integrand, Complex.norm_real, Real.norm_eq_abs]
    have hexp : Real.exp (ε.re * x j) ≤ Real.exp (β / 2 * ‖x‖) :=
      Real.exp_le_exp.mpr (exponent_le (β / 2) (by positivity) ε hε.le j x)
    calc
      (Real.exp (ε.re * x j) * |w x|) * |x j| =
          (|x j| * Real.exp (ε.re * x j)) * |w x| := by ring
      _ ≤ (‖x‖ * Real.exp (β / 2 * ‖x‖)) * |w x| := by
        gcongr
        exact PiLp.norm_apply_le x j
      _ ≤ ((2 / β) * Real.exp (β * ‖x‖)) * |w x| :=
        mul_le_mul_of_nonneg_right (linear_exp_bound hβ) (abs_nonneg _)
      _ = (2 / β) * (Real.exp (β * ‖x‖) * |w x|) := by ring
  · refine ae_of_all _ fun x ε _ => ?_
    have hd := (((hasDerivAt_id ε).mul_const (x j : ℂ)).cexp.const_mul
      (fieldPhase k x)).mul_const (w x : ℂ)
    simp only [id_eq, one_mul] at hd
    convert hd using 1 <;> first | rfl | (dsimp only [laplaceIntegrand]; ring)

/-- Real analyticity of every affine coordinate slice of the actual physical
Fourier coefficient. -/
theorem analyticOnNhd_fourierCoeff_slice (w : FieldSpace → ℝ)
    (hw : Integrable w volume) {β : ℝ} (hβ : 0 < β)
    (hm : Integrable (fun x => Real.exp (β * ‖x‖) * |w x|) volume)
    (k : FieldSpace) (j : Fin 3) :
    AnalyticOnNhd ℝ (fun t : ℝ => fourierCoeff w
      (k + t • EuclideanSpace.single j 1)) Set.univ := by
  have ha := (differentiableOn_coordinateLaplace w hw hβ hm k j).analyticOnNhd
    (isOpen_lt Complex.continuous_re.abs continuous_const)
  intro t _
  have hc : AnalyticAt ℝ (fun t : ℝ => -(t : ℂ) * Complex.I) t :=
    (Complex.ofRealCLM.analyticAt t).neg.mul analyticAt_const
  have hh : AnalyticAt ℝ
      (fun s : ℝ => coordinateLaplace w k j (-(s : ℂ) * Complex.I)) t :=
    ((ha (-(t : ℂ) * Complex.I) (by simpa using (half_pos hβ))).restrictScalars
      (𝕜 := ℝ)).comp (f := fun s : ℝ => -(s : ℂ) * Complex.I) hc
  convert hh using 1
  funext s
  unfold PhysicalGroundState.fourierCoeff coordinateLaplace
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    simp only [laplaceIntegrand, fieldPhase, inner_add_left, inner_smul_left,
      EuclideanSpace.inner_single_left]
    simp only [conj_trivial, one_mul, Complex.ofReal_neg, Complex.ofReal_add,
      Complex.ofReal_mul]
    rw [← Complex.exp_add]
    congr 2
    ring

/-- The same conclusion in coordinate-update form, convenient for Fubini and
the uniqueness theorem for separately analytic functions. -/
theorem analyticOnNhd_fourierCoeff_update (w : FieldSpace → ℝ)
    (hw : Integrable w volume) {β : ℝ} (hβ : 0 < β)
    (hm : Integrable (fun x => Real.exp (β * ‖x‖) * |w x|) volume)
    (x : Fin 3 → ℝ) (j : Fin 3) :
    AnalyticOnNhd ℝ (fun t : ℝ => fourierCoeff w
      (WithLp.toLp 2 (Function.update x j t))) Set.univ := by
  have heq (t : ℝ) : WithLp.toLp 2 (Function.update x j t) =
      WithLp.toLp 2 (Function.update x j 0) + t • EuclideanSpace.single j 1 := by
    ext a
    by_cases ha : a = j
    · subst a
      simp [PiLp.add_apply, PiLp.smul_apply]
    · simp [PiLp.add_apply, PiLp.smul_apply, ha]
  have heqf : (fun t : ℝ => fourierCoeff w (WithLp.toLp 2 (Function.update x j t))) =
      (fun t : ℝ => fourierCoeff w
        (WithLp.toLp 2 (Function.update x j 0) + t • EuclideanSpace.single j 1)) :=
    funext fun t => congrArg (fourierCoeff w) (heq t)
  rw [heqf]
  exact analyticOnNhd_fourierCoeff_slice w hw hβ hm _ j

end PfHk.ExponentialFourierAnalytic
