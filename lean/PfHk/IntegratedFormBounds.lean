import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Passing pointwise quadratic-form derivative bounds to the actual
integrated quadratic forms. The proof uses integral monotonicity and a
quadratic discriminant, and does not assume an integrated error estimate. -/

noncomputable section
namespace PfHk.IntegratedFormBounds

open MeasureTheory
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem integral_sq_le_product {v K G : X → ℝ}
    (hv : Integrable v μ) (hK : Integrable K μ) (hG : Integrable G μ)
    (hK₀ : ∀ᵐ x ∂μ, 0 ≤ K x) (hG₀ : ∀ᵐ x ∂μ, 0 ≤ G x)
    (hbound : ∀ᵐ x ∂μ, v x ^ 2 ≤ K x * G x) :
    (∫ x, v x ∂μ) ^ 2 ≤ (∫ x, K x ∂μ) * ∫ x, G x ∂μ := by
  have hquad (a : ℝ) : 0 ≤ (∫ x, K x ∂μ) * (a * a) +
      (-2 * ∫ x, v x ∂μ) * a + ∫ x, G x ∂μ := by
    have hh := integral_mono_ae (hv.const_mul (2 * a)) ((hK.const_mul (a ^ 2)).add hG) (by
      filter_upwards [hK₀, hG₀, hbound] with x hk hg hx
      have h := mul_le_mul_of_nonneg_left hx (sq_nonneg a)
      have h' : (a * v x) ^ 2 ≤ (a ^ 2 * K x) * G x := by nlinarith
      have h'' := two_mul_le_add_of_sq_le_mul (mul_nonneg (sq_nonneg a) hk) hg h'
      change 2 * a * v x ≤ a ^ 2 * K x + G x
      nlinarith only [h''])
    have hadd := integral_add (hK.const_mul (a ^ 2)) hG
    simp only [Pi.add_apply] at hadd hh
    rw [hadd, integral_const_mul, integral_const_mul] at hh
    nlinarith
  have h := discrim_le_zero hquad
  unfold discrim at h
  nlinarith

/-- The sphere-integrated curvature bound retains the same coefficient.
The measure may be the genuine surface measure on any unit sphere. -/
theorem integrated_angular_bound {v K T M : X → ℝ} {C r : ℝ}
    (hv : Integrable v μ) (hK : Integrable K μ)
    (hT : Integrable T μ) (hM : Integrable M μ)
    (hK₀ : ∀ᵐ x ∂μ, 0 ≤ K x) (hT₀ : ∀ᵐ x ∂μ, 0 ≤ T x)
    (hM₀ : ∀ᵐ x ∂μ, 0 ≤ M x)
    (hbound : ∀ᵐ x ∂μ, v x ^ 2 ≤ C ^ 2 * r ^ 4 * K x * (T x + M x)) :
    (∫ x, v x ∂μ) ^ 2 ≤ C ^ 2 * r ^ 4 * (∫ x, K x ∂μ) *
      ((∫ x, T x ∂μ) + ∫ x, M x ∂μ) := by
  have h := integral_sq_le_product hv hK ((hT.add hM).const_mul (C ^ 2 * r ^ 4)) hK₀
    (by
      filter_upwards [hT₀, hM₀] with x ht hm
      change 0 ≤ C ^ 2 * r ^ 4 * (T x + M x)
      positivity)
    (hbound.mono fun x hx => hx.trans_eq (by simp only [Pi.add_apply]; ring))
  have hadd := integral_add hT hM
  simp only [Pi.add_apply] at hadd h
  rw [integral_const_mul, hadd] at h
  exact h.trans_eq (by ring)

/-- The sphere-integrated radiation derivative has the square-radius
coefficient, exactly as required in the cylinder commutator. -/
theorem integrated_radiation_bound {v T M : X → ℝ} {C r : ℝ}
    (hv : Integrable v μ) (hT : Integrable T μ) (hM : Integrable M μ)
    (hT₀ : ∀ᵐ x ∂μ, 0 ≤ T x) (hM₀ : ∀ᵐ x ∂μ, 0 ≤ M x)
    (hbound : ∀ᵐ x ∂μ, v x ^ 2 ≤ C ^ 2 * r ^ 2 * T x * M x) :
    (∫ x, v x ∂μ) ^ 2 ≤ C ^ 2 * r ^ 2 * (∫ x, T x ∂μ) * ∫ x, M x ∂μ := by
  have h := integral_sq_le_product hv hT (hM.const_mul (C ^ 2 * r ^ 2)) hT₀
    (hM₀.mono fun x hx => mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hx)
    (hbound.mono fun x hx => hx.trans_eq (by ring))
  rw [integral_const_mul] at h
  exact h.trans_eq (by ring)

end PfHk.IntegratedFormBounds
