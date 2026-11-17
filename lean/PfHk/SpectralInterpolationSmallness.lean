import PfHk.PhysicalDyadicSpectral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Subquadratic spectral orders are infinitesimally bounded relative to
the comparison graph. The proof uses the existing spectral interpolation
inequality and real-power decay. -/

noncomputable section
namespace PfHk.SpectralInterpolationSmallness

open Filter GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  PfHk.PhysicalOperatorDomain PfHk.PhysicalDyadicIntegralFractional
open scoped Topology

set_option Elab.async false
set_option maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] PhysicalPFReference.inclusion
  PhysicalPFReference.ordinary PhysicalPFReference.radiation

theorem weighted_product {θ ε : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      x ^ (1 - θ) * y ^ θ ≤ ε * y + K * x := by
  have hevent := (tendsto_rpow_neg_atTop (sub_pos.mpr hθ1)).eventually_lt_const hε
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hevent
  let T : ℝ := max T₀ 1
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hsmall : T ^ (-(1 - θ)) < ε := hT₀ T (le_max_left _ _)
  refine ⟨T ^ θ, Real.rpow_nonneg hT.le _, ?_⟩
  intro x y hx hy
  have collapse (z : ℝ) (hz : 0 ≤ z) : z ^ (1 - θ) * z ^ θ = z := by
    rw [← Real.rpow_add_of_nonneg hz (sub_nonneg.mpr hθ1.le) hθ]
    norm_num
  by_cases hxy : y ≤ T * x
  · have h := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hy hxy hθ)
      (Real.rpow_nonneg hx (1 - θ))
    apply h.trans
    rw [Real.mul_rpow hT.le hx]
    calc
      _ = T ^ θ * (x ^ (1 - θ) * x ^ θ) := by ring
      _ = T ^ θ * x := by rw [collapse x hx]
      _ ≤ ε * y + T ^ θ * x := le_add_of_nonneg_left (mul_nonneg hε.le hy)
  · have hxbound : x ≤ y / T := by
      apply (le_div_iff₀ hT).mpr
      have h := le_of_not_ge hxy
      nlinarith
    have h := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hx hxbound (sub_nonneg.mpr hθ1.le))
      (Real.rpow_nonneg hy θ)
    apply h.trans
    calc
      _ = T ^ (-(1 - θ)) * y := by
        rw [Real.div_rpow hy hT.le, div_mul_eq_mul_div, collapse y hy,
          div_eq_mul_inv, ← Real.rpow_neg hT.le]
        ring
      _ ≤ ε * y := mul_le_mul_of_nonneg_right hsmall.le hy
      _ ≤ ε * y + T ^ θ * x :=
        le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg hT.le _) hx)

variable {I : Type} [Fintype I] [DecidableEq I]

theorem fractional_norm_sq
    (spectral : ComparisonSpectralCalculus (I := I))
    {s ε : ℝ} (hs : 0 ≤ s) (hs2 : s < 2) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (u : Reference I (fun _ => 0)) (L : WaveSpace I)
        (hL : IsComparisonPair (fun _ => 0) u L),
        fractionalNormSq spectral s u ⟨L, hL⟩ ≤
          ε * ‖L‖ ^ 2 + K * ‖inclusion I (fun _ => 0) u‖ ^ 2 := by
  have hex := weighted_product
    (θ := s / 2) (by linarith) (by linarith) hε
  let K := Classical.choose hex
  have hbound := Classical.choose_spec hex
  refine ⟨K, hbound.1, ?_⟩
  intro u L hL
  exact (spectral.interpolation s hs hs2.le u ⟨L, hL⟩ L hL).trans
    (hbound.2 _ _ (sq_nonneg _) (sq_nonneg _))

end PfHk.SpectralInterpolationSmallness
