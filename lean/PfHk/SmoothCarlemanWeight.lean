import PfHk.CarlemanWeightDerivatives
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! A globally smooth extension of the actual logarithmic weight.
It agrees with the physical weight throughout the half-cylinder t ≥ 2. -/

noncomputable section
namespace PfHk.CarlemanWeights

open Filter Set
open scoped Topology ENNReal
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

def smoothWeight (α t : ℝ) : ℝ :=
  t + Real.smoothTransition (2*t-1) * t ^ (-α)

theorem smoothWeight_contDiff (α : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (smoothWeight α) := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  by_cases ht : t = 0
  · subst t
    apply (contDiffAt_id : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => x) 0).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds (by norm_num : (0 : ℝ) < 1/2)] with x hx
    have hx' : x < 1/2 := hx
    simp only [smoothWeight, Real.smoothTransition.zero_of_nonpos (by linarith : 2*x-1 ≤ 0),
      zero_mul, add_zero, id_eq]
  · exact contDiffAt_id.add
      ((Real.smoothTransition.contDiffAt.comp t
        ((contDiffAt_const.mul contDiffAt_id).sub contDiffAt_const)).mul
        (Real.contDiffAt_rpow_const_of_ne ht))

theorem smoothWeight_eq {α t : ℝ} (ht : 1 ≤ t) : smoothWeight α t = weight α t := by
  unfold smoothWeight weight
  rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 2*t-1), one_mul]

theorem smoothWeight_eventuallyEq (α : ℝ) {t : ℝ} (ht : 1 < t) :
    smoothWeight α =ᶠ[𝓝 t] weight α := by
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact smoothWeight_eq hs.le

theorem smoothWeight_hasDerivAt (α : ℝ) {t : ℝ} (ht : 1 < t) :
    HasDerivAt (smoothWeight α) (weightPrime α t) t :=
  (weight_hasDerivAt α (by linarith : 0<t)).congr_of_eventuallyEq
    (smoothWeight_eventuallyEq α ht)

def smoothExponential (τ α t : ℝ) : ℝ := Real.exp (τ * smoothWeight α t)

theorem smoothExponential_contDiff (τ α : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothExponential τ α) :=
  (contDiff_const.mul (smoothWeight_contDiff α)).exp

theorem smoothExponential_eq (τ α : ℝ) {t : ℝ} (ht : 1 ≤ t) :
    smoothExponential τ α t = Real.exp (τ * weight α t) := by
  unfold smoothExponential
  rw [smoothWeight_eq ht]

theorem smoothExponential_hasDerivAt (τ α t : ℝ) :
    HasDerivAt (smoothExponential τ α) (deriv (smoothExponential τ α) t) t :=
  ((smoothExponential_contDiff τ α).differentiable (by simp) t).hasDerivAt

theorem smoothExponential_deriv_hasDerivAt (τ α t : ℝ) :
    HasDerivAt (deriv (smoothExponential τ α)) (deriv (deriv (smoothExponential τ α)) t) t :=
  (((smoothExponential_contDiff τ α).of_le (by norm_num)).differentiable_deriv_two t).hasDerivAt

theorem smoothExponential_deriv (τ α : ℝ) {t : ℝ} (ht : 1 < t) :
    deriv (smoothExponential τ α) t = Real.exp (τ * weight α t) * (τ * weightPrime α t) := by
  have h := ((smoothWeight_hasDerivAt α ht).const_mul τ).exp
  have he := h.deriv
  rw [smoothWeight_eq ht.le] at he
  exact he

theorem smoothExponential_second (τ α : ℝ) {t : ℝ} (ht : 1 < t) :
    deriv (deriv (smoothExponential τ α)) t = Real.exp (τ * weight α t) *
      (τ * beta α t + τ ^ 2 * weightPrime α t ^ 2) := by
  have h := (((weight_hasDerivAt α (by linarith : 0<t)).const_mul τ).exp).mul
    ((weightPrime_hasDerivAt α (by linarith : 0<t)).const_mul τ)
  have heq : deriv (smoothExponential τ α) =ᶠ[𝓝 t]
      fun s => Real.exp (τ * weight α s) * (τ * weightPrime α s) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact smoothExponential_deriv τ α hs
  have hd := (h.congr_of_eventuallyEq heq).deriv
  exact hd.trans (by ring)

end PfHk.CarlemanWeights
