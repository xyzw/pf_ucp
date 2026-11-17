import PfHk.CarlemanWeights

/-! The higher derivatives and uniform bounds for the actual logarithmic
weight used in the cylinder estimate. -/

noncomputable section
namespace PfHk.CarlemanWeights

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

open Filter Set
open scoped Topology

def betaPrime (α t : ℝ) : ℝ := α * (α + 1) * (-α - 2) * t ^ (-α - 3)
def betaSecond (α t : ℝ) : ℝ := α * (α + 1) * (α + 2) * (α + 3) * t ^ (-α - 4)

theorem beta_hasDerivAt (α : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (beta α) (betaPrime α t) t := by
  have h := (Real.hasDerivAt_rpow_const (x := t) (p := -α - 2)
    (Or.inl ht.ne')).const_mul (α * (α + 1))
  convert h using 1 <;> first | rfl |
    (unfold betaPrime; rw [show -α - 2 - 1 = -α - 3 by ring]; ring)

theorem betaPrime_hasDerivAt (α : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (betaPrime α) (betaSecond α t) t := by
  have h := (Real.hasDerivAt_rpow_const (x := t) (p := -α - 3)
    (Or.inl ht.ne')).const_mul (α * (α + 1) * (-α - 2))
  convert h using 1 <;> first | rfl |
    (unfold betaSecond; rw [show -α - 3 - 1 = -α - 4 by ring]; ring)

/-- Two applications of Bernoulli's inequality give `α (α + 1) ≤ 2 ^ (α + 2)`
for every positive exponent. -/
theorem mul_add_one_le_two_rpow {α : ℝ} (hα : 0 < α) :
    α * (α + 1) ≤ (2 : ℝ) ^ (α + 2) := by
  have hsq (p : ℝ) : (2 : ℝ) ^ (2 * p) = ((2 : ℝ) ^ p) ^ 2 := by
    rw [show 2 * p = p * 2 by ring, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_two]
  have hhalf : α + 1 / 2 ≤ (2 : ℝ) ^ ((α + 2) / 2) := by
    by_cases h3 : α ≤ 3
    · have h := one_add_le_two_rpow (p := (α + 2) / 2) (by linarith)
      linarith
    · have h3' : 3 < α := not_le.mp h3
      have h := one_add_le_two_rpow (p := (α + 2) / 4) (by linarith)
      have hs := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1 + (α + 2) / 4) h 2
      rw [← hsq, show 2 * ((α + 2) / 4) = (α + 2) / 2 by ring] at hs
      nlinarith [sq_nonneg (α - 2)]
  have hs := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ α + 1 / 2) hhalf 2
  rw [← hsq, show 2 * ((α + 2) / 2) = α + 2 by ring] at hs
  nlinarith

/-- The convexity coefficient is at most one on `t ≥ 2`, for every
positive exponent. -/
theorem beta_le_one {α t : ℝ} (hα : 0 < α) (ht : 2 ≤ t) : beta α t ≤ 1 := by
  have ht₀ : 0 < t := by linarith
  have hmono : (2 : ℝ) ^ (α + 2) ≤ t ^ (α + 2) :=
    Real.rpow_le_rpow (by norm_num) ht (by linarith)
  have hpos : 0 < t ^ (α + 2) := Real.rpow_pos_of_pos ht₀ _
  unfold beta
  rw [show -α - 2 = -(α + 2) by ring, Real.rpow_neg ht₀.le, ← div_eq_mul_inv,
    div_le_one hpos]
  exact (mul_add_one_le_two_rpow hα).trans hmono

theorem betaSecond_nonneg {α t : ℝ} (hα : 0 < α) (ht : 0 < t) :
    0 ≤ betaSecond α t := by unfold betaSecond; positivity

theorem betaSecond_eq {α t : ℝ} (ht : 0 < t) :
    betaSecond α t = (α + 2) * (α + 3) * beta α t * t ^ (-2 : ℝ) := by
  unfold betaSecond beta
  rw [show -α - 4 = (-α - 2) + (-2 : ℝ) by ring, Real.rpow_add ht]
  ring

/-- The fourth derivative of the weight is controlled by `β` once the
cylinder coordinate dominates the exponent, `t ≥ max 2 (4 α)`. -/
theorem betaSecond_le {α t : ℝ} (hα : 0 < α) (ht : 2 ≤ t) (hαt : 4 * α ≤ t) :
    |betaSecond α t| ≤ 9 * beta α t := by
  have ht₀ : 0 < t := by linarith
  rw [abs_of_nonneg (betaSecond_nonneg hα ht₀), betaSecond_eq ht₀]
  have hβ := (beta_pos hα ht₀).le
  have h16 : (4 * α) * (4 * α) ≤ t * t :=
    mul_le_mul hαt hαt (by linarith) ht₀.le
  have h2 : 2 * t ≤ t * t := by nlinarith
  have hpow : (α + 2) * (α + 3) * t ^ (-2 : ℝ) ≤ 9 := by
    rw [Real.rpow_neg ht₀.le, Real.rpow_two, ← div_eq_mul_inv, div_le_iff₀ (pow_pos ht₀ 2)]
    nlinarith
  calc (α + 2) * (α + 3) * beta α t * t ^ (-2 : ℝ)
      = ((α + 2) * (α + 3) * t ^ (-2 : ℝ)) * beta α t := by ring
    _ ≤ 9 * beta α t := mul_le_mul_of_nonneg_right hpow hβ

theorem fourth_derivative_small {α τ t : ℝ} (hα : 0 < α)
    (hτ : 9 ≤ τ) (ht : 2 ≤ t) (hαt : 4 * α ≤ t) :
    |betaSecond α t| ≤ τ ^ 2 * beta α t / 8 := by
  have h := betaSecond_le hα ht hαt
  have hβ := (beta_pos hα (by linarith : 0 < t)).le
  have hτ₂ : 72 ≤ τ ^ 2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hτ₂ hβ
  nlinarith

/-- One half-cylinder works for both the curvature smallness and the
radius-to-convexity bound. The threshold is independent of the curve. -/
theorem exists_cylinder_small (α C : ℝ) (hα : 0 < α) :
    ∃ t₀ : ℝ, 2 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t →
      Real.exp (-2 * t) ≤ beta α t ∧ 64 * C ^ 2 * Real.exp (-2 * t) ≤ beta α t := by
  let ε : ℝ := 1 / (1 + 64 * C ^ 2)
  have hε : 0 < ε := by unfold ε; positivity
  have hevent := (cylinderRatio_tendsto_zero α (by norm_num : (0 : ℝ) < 2)).eventually_lt_const hε
  obtain ⟨T, hT⟩ := eventually_atTop.1 hevent
  refine ⟨max T 2, le_max_right _ _, ?_⟩
  intro t ht
  have ht₂ : 2 ≤ t := (le_max_right T 2).trans ht
  have ht₀ : 0 < t := by linarith
  have hβ := beta_pos hα ht₀
  have h := hT t ((le_max_left T 2).trans ht)
  have heq : (Real.exp (-t)) ^ (2 : ℝ) = Real.exp (-2 * t) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  rw [cylinderRatio, heq] at h
  have hsmall := (div_lt_iff₀ hβ).mp h
  have hε₁ : ε ≤ 1 := by
    unfold ε
    apply (div_le_iff₀ (by positivity : 0 < 1 + 64 * C ^ 2)).mpr
    nlinarith [sq_nonneg C]
  have hεC : 64 * C ^ 2 * ε ≤ 1 := by
    unfold ε
    rw [← mul_div_assoc, mul_one]
    apply (div_le_iff₀ (by positivity : 0 < 1 + 64 * C ^ 2)).mpr
    linarith
  constructor
  · exact hsmall.le.trans (by nlinarith [mul_le_mul_of_nonneg_right hε₁ hβ.le])
  · have h₁ := mul_le_mul_of_nonneg_left hsmall.le (by positivity : 0 ≤ 64 * C ^ 2)
    have h₂ := mul_le_mul_of_nonneg_right hεC hβ.le
    nlinarith

end PfHk.CarlemanWeights
