import PfHk.CylinderIdentity
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Module

/-! Exponential conjugation of the cylinder differential expression,
including the ordinary derivative product rules and radial norm recovery. -/

noncomputable section
namespace PfHk.CylinderConjugation

open CylinderIdentity
open scoped InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def weighted (τ : ℝ) (f : ℝ → ℝ) (w : ℝ → H) (t : ℝ) : H :=
  Real.exp (τ * f t) • w t

def weightedFirst (τ : ℝ) (f p : ℝ → ℝ) (w dw : ℝ → H) (t : ℝ) : H :=
  Real.exp (τ * f t) • (dw t + (τ * p t) • w t)

def weightedSecond (τ : ℝ) (f p b : ℝ → ℝ) (w dw ddw : ℝ → H) (t : ℝ) : H :=
  Real.exp (τ * f t) • (ddw t + (2 * τ * p t) • dw t +
    (τ * b t + τ ^ 2 * p t ^ 2) • w t)

theorem weighted_hasDerivAt {τ t : ℝ} {f p : ℝ → ℝ} {w dw : ℝ → H}
    (hf : HasDerivAt f (p t) t) (hw : HasDerivAt w (dw t) t) :
    HasDerivAt (weighted τ f w) (weightedFirst τ f p w dw t) t := by
  have h := ((hf.const_mul τ).exp).smul hw
  convert h using 1
  · rfl
  · unfold weightedFirst
    module

theorem weightedFirst_hasDerivAt {τ t : ℝ} {f p b : ℝ → ℝ} {w dw ddw : ℝ → H}
    (hf : HasDerivAt f (p t) t) (hp : HasDerivAt p (b t) t)
    (hw : HasDerivAt w (dw t) t) (hdw : HasDerivAt dw (ddw t) t) :
    HasDerivAt (weightedFirst τ f p w dw) (weightedSecond τ f p b w dw ddw t) t := by
  have hi := hdw.add ((hp.const_mul τ).smul hw)
  have h := ((hf.const_mul τ).exp).smul hi
  convert h using 1
  · rfl
  · unfold weightedSecond
    change Real.exp (τ * f t) •
        (ddw t + (2 * τ * p t) • dw t + (τ * b t + τ ^ 2 * p t ^ 2) • w t) =
      Real.exp (τ * f t) • (ddw t + ((τ * p t) • dw t + (τ * b t) • w t)) +
        (Real.exp (τ * f t) * (τ * p t)) • (dw t + (τ * p t) • w t)
    module

/-- The exact `e^(τf) Q e^(-τf) = S+B` identity. The angular and
radiation images scale linearly with the scalar weight. -/
theorem operator_conjugation (τ c t : ℝ) (f p b r : ℝ → ℝ)
    (w dw ddw k q : ℝ → H) :
    symmetricPart τ c p r (weighted τ f w) (weightedSecond τ f p b w dw ddw)
        (weighted τ f k) (weighted τ f q) t +
      skewPart τ p b (weighted τ f w) (weightedFirst τ f p w dw) t =
    Real.exp (τ * f t) • (-ddw t + k t + c ^ 2 • w t + r t • q t) := by
  unfold symmetricPart skewPart weighted weightedFirst weightedSecond
  module

theorem weighted_norm_sq (τ t : ℝ) (f : ℝ → ℝ) (w : ℝ → H) :
    ‖weighted τ f w t‖ ^ 2 = Real.exp (2 * τ * f t) * ‖w t‖ ^ 2 := by
  rw [weighted, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]
  rw [pow_two, ← Real.exp_add]
  congr 2
  ring

/-- Recovering the radial covariant derivative from the weighted curve
costs only the retained radial and mass terms. -/
theorem radial_norm_sq_le (z dz : H) {τ p c : ℝ} (hτ : 0 ≤ τ)
    (hp : |p| ≤ 1) (hc : |c| ≤ τ) :
    ‖-dz + (τ * p - c) • z‖ ^ 2 ≤ 2 * ‖dz‖ ^ 2 + 8 * τ ^ 2 * ‖z‖ ^ 2 := by
  have hp₂ : p ^ 2 ≤ 1 := by nlinarith [sq_abs p, mul_self_le_mul_self (abs_nonneg p) hp]
  have hc₂ : c ^ 2 ≤ τ ^ 2 := by nlinarith [sq_abs c, mul_self_le_mul_self (abs_nonneg c) hc]
  have hpm := mul_le_mul_of_nonneg_left hp₂ (sq_nonneg τ)
  have hcoef : (τ * p - c) ^ 2 ≤ 4 * τ ^ 2 := by
    nlinarith [sq_nonneg (τ * p + c)]
  have h : ‖-dz + (τ * p - c) • z‖ ^ 2 ≤
      2 * ‖-dz‖ ^ 2 + 2 * ‖(τ * p - c) • z‖ ^ 2 := by
    have ha := pow_le_pow_left₀ (norm_nonneg _)
      (norm_add_le (-dz) ((τ * p - c) • z)) 2
    nlinarith [sq_nonneg (‖-dz‖ - ‖(τ * p - c) • z‖)]
  rw [norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h
  have hm := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖z‖)
  nlinarith only [h, hm]

end PfHk.CylinderConjugation
