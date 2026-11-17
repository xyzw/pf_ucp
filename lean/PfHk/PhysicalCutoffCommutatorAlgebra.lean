import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import GptLean.NonattainmentEnergySplit

/-! The finite Hilbert-space algebra in the scalar cutoff commutator. -/

namespace PfHk.PhysicalCutoffCommutator

open scoped InnerProductSpace

theorem cutoff_kinetic_pair {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (a b c : H →L[ℂ] H)
    (ha : ∀ x y, ⟪x, a y⟫_ℂ = ⟪a x, y⟫_ℂ)
    (hb : ∀ x y, ⟪x, b y⟫_ℂ = ⟪b x, y⟫_ℂ)
    (u v du dv : H)
    (hcov : ⟪v, b du + (-Complex.I) • c u⟫_ℂ = ⟪dv, b u⟫_ℂ) :
    ⟪dv, a du + (-Complex.I) • b u⟫_ℂ =
      ⟪a dv + (-Complex.I) • b v, du⟫_ℂ +
        2 * ⟪v, (-Complex.I) • b du + (-(1 / 2) : ℂ) • c u⟫_ℂ := by
  have hh : ⟪dv, b u⟫_ℂ = ⟪v, b du⟫_ℂ + (-Complex.I) * ⟪v, c u⟫_ℂ := by
    rw [← hcov, inner_add_right, inner_smul_right]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    map_neg, Complex.conj_I, neg_neg, ← ha, ← hb, hh]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- Pointwise estimate for the exact first-order cutoff commutator.
The two scalar coefficients are the cutoff gradient and its Laplacian. -/
theorem cutoff_commutator_norm_sq {H J : Type*} [Fintype J]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (g : J → ℝ) (Δ : ℝ) (D : J → H) (u : H) :
    ‖(-Complex.I) • (∑ i, (g i : ℂ) • D i) + (-(Δ / 2) : ℂ) • u‖ ^ 2 ≤
      2 * (∑ i, g i ^ 2) * (∑ i, ‖D i‖ ^ 2) + (1 / 2 : ℝ) * Δ ^ 2 * ‖u‖ ^ 2 := by
  have hadd : ∀ v w : H, ‖v + w‖ ^ 2 ≤ 2 * ‖v‖ ^ 2 + 2 * ‖w‖ ^ 2 := by
    intro v w
    have ht := pow_le_pow_left₀ (norm_nonneg (v + w)) (norm_add_le v w) 2
    nlinarith [sq_nonneg (‖v‖ - ‖w‖)]
  have hs := GptLean.Nonattainment.norm_sum_real_smul_sq_le g D
  calc
    _ ≤ 2 * ‖(-Complex.I) • (∑ i, (g i : ℂ) • D i)‖ ^ 2 +
        2 * ‖(-(Δ / 2) : ℂ) • u‖ ^ 2 := hadd _ _
    _ = 2 * ‖∑ i, (g i : ℂ) • D i‖ ^ 2 + (1 / 2 : ℝ) * Δ ^ 2 * ‖u‖ ^ 2 := by
      norm_num [norm_smul, norm_div, Complex.norm_real, Real.norm_eq_abs, mul_pow, div_pow, sq_abs]
      ring
    _ ≤ _ := by nlinarith


end PfHk.PhysicalCutoffCommutator
