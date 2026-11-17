import PfHk.SmoothCarlemanWeight
import PfHk.SmoothCutoffBounds
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! Spatial derivatives of the actual exponential Carleman weight.
The smooth extension is used only outside the small physical ball. -/

noncomputable section
namespace PfHk.SpatialCarlemanWeight

open Filter PfHk.CarlemanWeights PfHk.SmoothCutoffBounds
open scoped Topology

set_option Elab.async false
set_option maxHeartbeats 30000

variable {I : Type} [Fintype I] [DecidableEq I]

def logRadius (O x : EuclideanSpace ℝ I) : ℝ := -Real.log ‖x - O‖

def spatialExp (τ α : ℝ) (O x : EuclideanSpace ℝ I) : ℝ :=
  smoothExponential τ α (logRadius O x)

omit [DecidableEq I] in
theorem logRadius_contDiffAt (O x : EuclideanSpace ℝ I) (hx : x ≠ O) :
    ContDiffAt ℝ (⊤ : ℕ∞) (logRadius O) x :=
  (((contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.mpr hx)).log
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx))).neg

theorem spatialExp_contDiffAt (τ α : ℝ) (O x : EuclideanSpace ℝ I) (hx : x ≠ O) :
    ContDiffAt ℝ (⊤ : ℕ∞) (spatialExp τ α O) x :=
  (smoothExponential_contDiff τ α).contDiffAt.comp x (logRadius_contDiffAt O x hx)

omit [DecidableEq I] in
theorem spatialExp_eq (τ α : ℝ) (O x : EuclideanSpace ℝ I)
    (ht : 1 ≤ -Real.log (dist x O)) :
    spatialExp τ α O x = Real.exp (τ * weight α (-Real.log (dist x O))) := by
  exact smoothExponential_eq τ α (by simpa only [logRadius, dist_eq_norm] using ht)

omit [DecidableEq I] in
theorem logRadius_hasFDerivAt (O x : EuclideanSpace ℝ I) (hx : x ≠ O) :
    HasFDerivAt (logRadius O) (-(‖x-O‖ ^ 2)⁻¹ • innerSL ℝ (x-O)) x := by
  have hq := (((hasFDerivAt_id (𝕜 := ℝ) x).sub_const O).norm_sq).log
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)))
  have heq : logRadius O = fun y => -(1/2 : ℝ) * Real.log (‖y-O‖ ^ 2) := by
    funext y
    rw [Real.log_pow]
    simp only [logRadius]
    ring
  rw [heq]
  apply (hq.const_mul (-(1/2 : ℝ))).congr_fderiv
  ext y
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, id_eq]
  ring

theorem logRadius_coordinate (O x : EuclideanSpace ℝ I) (hx : x ≠ O) (i : I) :
    coordinateDerivative (logRadius O) i x = -(x-O) i / ‖x-O‖ ^ 2 := by
  rw [coordinateDerivative, (logRadius_hasFDerivAt O x hx).fderiv]
  simp only [smul_apply, innerSL_apply_apply,
    EuclideanSpace.inner_single_right, conj_trivial, smul_eq_mul]
  ring

theorem norm_coordinate_le (x : EuclideanSpace ℝ I) (i : I) : |x i| ≤ ‖x‖ := by
  simpa only [EuclideanSpace.inner_single_right, conj_trivial, mul_one,
    PiLp.norm_single, norm_one, mul_one, one_mul] using
    (abs_real_inner_le_norm x (EuclideanSpace.single i 1))

theorem logRadius_first_bound (O x : EuclideanSpace ℝ I) (hx : x ≠ O) (i : I) :
    |coordinateDerivative (logRadius O) i x| ≤ 1 / ‖x-O‖ := by
  have hr : 0 < ‖x-O‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  rw [logRadius_coordinate O x hx, abs_div, abs_neg, abs_of_pos (sq_pos_of_pos hr)]
  apply (div_le_div_of_nonneg_right (norm_coordinate_le (x-O) i) (sq_nonneg _)).trans_eq
  field_simp

theorem logRadius_second_coordinate (O x : EuclideanSpace ℝ I) (hx : x ≠ O) (i j : I) :
    coordinateDerivative (coordinateDerivative (logRadius O) i) j x =
      -(if i = j then 1 else 0) / ‖x-O‖ ^ 2 +
        2 * (x-O) i * (x-O) j / (‖x-O‖ ^ 2) ^ 2 := by
  let c : EuclideanSpace ℝ I →L[ℝ] ℝ := (innerSL ℝ).flip (EuclideanSpace.single i 1)
  have hc : (fun y : EuclideanSpace ℝ I => (y-O) i) = fun y => c (y-O) := by
    funext y
    change (y-O) i = inner ℝ (y-O) (EuclideanSpace.single i 1)
    simp only [EuclideanSpace.inner_single_right, conj_trivial, one_mul]
  have hd := (c.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const O)).neg.mul
    ((hasDerivAt_inv (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)))).comp_hasFDerivAt x
      (((hasFDerivAt_id (𝕜 := ℝ) x).sub_const O).norm_sq))
  have he : coordinateDerivative (logRadius O) i =ᶠ[𝓝 x]
      (fun y => -(y-O) i / ‖y-O‖ ^ 2) := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    exact logRadius_coordinate O y hy i
  change (fderiv ℝ (coordinateDerivative (logRadius O) i) x) (EuclideanSpace.single j 1) = _
  rw [Filter.EventuallyEq.fderiv_eq he]
  simp only [div_eq_mul_inv]
  simp_rw [congrFun hc]
  have hd' := hd
  change HasFDerivAt (fun y => -c (y-O) * (‖y-O‖ ^ 2)⁻¹) _ x at hd'
  rw [hd'.fderiv]
  simp only [Function.comp_apply, Pi.neg_apply, id_eq]
  simp only [smul_apply, add_apply,
    neg_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply, smul_eq_mul]
  simp only [c, ContinuousLinearMap.flip_apply, innerSL_apply_apply,
    EuclideanSpace.inner_single_right, PiLp.single_apply, conj_trivial, one_mul]
  split_ifs <;> ring

theorem logRadius_second_bound (O x : EuclideanSpace ℝ I) (hx : x ≠ O) (i j : I) :
    |coordinateDerivative (coordinateDerivative (logRadius O) i) j x| ≤ 3 / ‖x-O‖ ^ 2 := by
  have hr : 0 < ‖x-O‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  have hi := norm_coordinate_le (x-O) i
  have hj := norm_coordinate_le (x-O) j
  rw [logRadius_second_coordinate O x hx]
  apply (abs_add_le _ _).trans
  have hδ : |(if i = j then 1 else 0 : ℝ)| ≤ 1 := by split_ifs <;> norm_num
  have ha : |-(if i = j then 1 else 0 : ℝ) / ‖x-O‖ ^ 2| ≤ 1 / ‖x-O‖ ^ 2 := by
    rw [abs_div, abs_neg, abs_of_pos (sq_pos_of_pos hr)]
    exact div_le_div_of_nonneg_right hδ (sq_nonneg _)
  have hb : |2 * (x-O) i * (x-O) j / (‖x-O‖ ^ 2) ^ 2| ≤ 2 / ‖x-O‖ ^ 2 := by
    rw [abs_div, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_pos (sq_pos_of_pos (sq_pos_of_pos hr))]
    apply (div_le_div_of_nonneg_right
      (mul_le_mul (mul_le_mul_of_nonneg_left hi (by norm_num)) hj (abs_nonneg _)
        (by positivity)) (sq_nonneg _)).trans_eq
    field_simp
  exact (add_le_add ha hb).trans_eq (by ring)

theorem spatialExp_coordinate (τ α : ℝ) (O x : EuclideanSpace ℝ I) (hx : x ≠ O) (i : I) :
    coordinateDerivative (spatialExp τ α O) i x =
      deriv (smoothExponential τ α) (logRadius O x) * coordinateDerivative (logRadius O) i x := by
  have h := (smoothExponential_hasDerivAt τ α (logRadius O x)).comp_hasFDerivAt x
    (logRadius_hasFDerivAt O x hx)
  unfold coordinateDerivative
  rw [(show HasFDerivAt (spatialExp τ α O) _ x from h).fderiv,
    (logRadius_hasFDerivAt O x hx).fderiv]
  rfl

theorem spatialExp_second_coordinate (τ α : ℝ) (O x : EuclideanSpace ℝ I)
    (hx : x ≠ O) (i j : I) :
    coordinateDerivative (coordinateDerivative (spatialExp τ α O) i) j x =
      deriv (deriv (smoothExponential τ α)) (logRadius O x) *
        coordinateDerivative (logRadius O) j x * coordinateDerivative (logRadius O) i x +
      deriv (smoothExponential τ α) (logRadius O x) *
        coordinateDerivative (coordinateDerivative (logRadius O) i) j x := by
  have he : coordinateDerivative (spatialExp τ α O) i =ᶠ[𝓝 x]
      fun y => deriv (smoothExponential τ α) (logRadius O y) *
        coordinateDerivative (logRadius O) i y := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    exact spatialExp_coordinate τ α O y hy i
  have hd := (smoothExponential_deriv_hasDerivAt τ α (logRadius O x)).comp_hasFDerivAt x
    (logRadius_hasFDerivAt O x hx)
  have hc : DifferentiableAt ℝ (coordinateDerivative (logRadius O) i) x :=
    (((logRadius_contDiffAt O x hx).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply
      contDiffAt_const).differentiableAt (by simp)
  change (fderiv ℝ (coordinateDerivative (spatialExp τ α O) i) x) (EuclideanSpace.single j 1) = _
  have hd' := hd.mul hc.hasFDerivAt
  change HasFDerivAt (fun y => deriv (smoothExponential τ α) (logRadius O y) * coordinateDerivative (logRadius O) i y) _ x at hd'
  rw [Filter.EventuallyEq.fderiv_eq he, hd'.fderiv]
  simp only [coordinateDerivative]
  rw [
    (logRadius_hasFDerivAt O x hx).fderiv]
  simp only [Function.comp_apply, add_apply, smul_apply, smul_eq_mul]
  ring

theorem exponential_derivative_bounds {τ α t : ℝ} (hτ : 1 ≤ τ)
    (hα : 0 < α) (ht : 2 ≤ t) :
    |deriv (smoothExponential τ α) t| ≤ τ * Real.exp (τ * weight α t) ∧
    |deriv (deriv (smoothExponential τ α)) t| ≤ 2 * τ^2 * Real.exp (τ * weight α t) := by
  have hf := weightPrime_pos_le_one hα ht
  have hb := beta_le_one hα ht
  have hb0 := (beta_pos hα (by linarith : 0<t)).le
  have he := (Real.exp_pos (τ * weight α t)).le
  have hτ0 : 0 ≤ τ := by linarith
  have hf0 : 0 ≤ weightPrime α t := hf.1.le
  have hf1 : weightPrime α t ≤ 1 := hf.2
  rw [smoothExponential_deriv τ α (by linarith), smoothExponential_second τ α (by linarith)]
  constructor
  · rw [abs_of_nonneg (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hf.2 (mul_nonneg hτ0 he)]
  · have hf2 : weightPrime α t ^ 2 ≤ 1 := by nlinarith
    rw [abs_of_nonneg (by positivity)]
    have h1 := mul_le_mul_of_nonneg_left hb hτ0
    have h2 := mul_le_mul_of_nonneg_left hf2 (sq_nonneg τ)
    have h3 : τ * beta α t + τ^2 * weightPrime α t ^ 2 ≤ 2*τ^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h3 he]

theorem spatialExp_first_bound {τ α : ℝ} (hτ : 1 ≤ τ) (hα : 0 < α)
    (O x : EuclideanSpace ℝ I) (hx : x ≠ O) (ht : 2 ≤ -Real.log (dist x O)) (i : I) :
    |coordinateDerivative (spatialExp τ α O) i x| ≤
      τ / dist x O * Real.exp (τ * weight α (-Real.log (dist x O))) := by
  have hd := (exponential_derivative_bounds hτ hα
    (show 2 ≤ logRadius O x by simpa only [logRadius, dist_eq_norm] using ht)).1
  rw [spatialExp_coordinate τ α O x hx, abs_mul]
  have h := mul_le_mul hd (logRadius_first_bound O x hx i) (abs_nonneg _) (by positivity)
  simpa only [logRadius, dist_eq_norm, mul_one_div, div_mul_eq_mul_div, mul_div_assoc] using h

theorem spatialExp_second_bound {τ α : ℝ} (hτ : 1 ≤ τ) (hα : 0 < α)
    (O x : EuclideanSpace ℝ I) (hx : x ≠ O) (ht : 2 ≤ -Real.log (dist x O)) (i j : I) :
    |coordinateDerivative (coordinateDerivative (spatialExp τ α O) i) j x| ≤
      5 * τ^2 / dist x O ^ 2 * Real.exp (τ * weight α (-Real.log (dist x O))) := by
  have hr : 0 < ‖x-O‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  have hτ0 : 0 ≤ τ := by linarith
  have hd := exponential_derivative_bounds hτ hα
    (show 2 ≤ logRadius O x by simpa only [logRadius, dist_eq_norm] using ht)
  rw [spatialExp_second_coordinate τ α O x hx]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul, abs_mul]
  have h1 := mul_le_mul (mul_le_mul hd.2 (logRadius_first_bound O x hx j)
    (abs_nonneg _) (by positivity)) (logRadius_first_bound O x hx i) (abs_nonneg _) (by positivity)
  have h2 := mul_le_mul hd.1 (logRadius_second_bound O x hx i j) (abs_nonneg _) (by positivity)
  apply (add_le_add h1 h2).trans
  simp only [logRadius, dist_eq_norm]
  field_simp
  have he := (Real.exp_pos (τ * weight α (-Real.log ‖x-O‖))).le
  nlinarith [mul_nonneg (show 0 ≤ τ^2 - τ by nlinarith) he]

end PfHk.SpatialCarlemanWeight
