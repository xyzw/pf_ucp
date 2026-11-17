import GptLean.PhysicalPairSpatialTests
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! Smooth compact spatial tests separate the actual density-current pair. -/

noncomputable section

namespace GptLean.PhysicalPairSpace

open MeasureTheory
open scoped ContDiff

structure SmoothSpatialTest extends SpatialTest where
  smooth : ContDiff ℝ ∞ weight
  compact : HasCompactSupport weight

theorem exists_smoothSpatialTest (f : Position → ℝ) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) :
    ∃ (t : SmoothSpatialTest) (c : ℝ), 0 < c ∧ ∀ x, t.weight x = c * f x := by
  obtain ⟨b, hb⟩ := hf.continuous.bounded_above_of_compact_support hs
  let c := (max b 1)⁻¹
  have hp : 0 < max b 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hc : 0 < c := inv_pos.mpr hp
  have hsm : ContDiff ℝ ∞ (fun x => c * f x) := contDiff_const.mul hf
  refine ⟨{
    weight := fun x => c * f x
    measurable := hsm.continuous.aestronglyMeasurable
    bounded := ?_
    smooth := hsm
    compact := hs.mul_left }, c, hc, fun _ => rfl⟩
  intro x
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos hc]
  exact (mul_le_mul_of_nonneg_left ((hb x).trans (le_max_left _ _)) hc.le).trans_eq
    (inv_mul_cancel₀ hp.ne')

theorem ae_eq_of_smoothSpatialTests {f g : Position → ℝ}
    (hf : Integrable f volume) (hg : Integrable g volume)
    (h : ∀ t : SmoothSpatialTest,
      (∫ x, t.weight x * f x) = ∫ x, t.weight x * g x) : f =ᵐ[volume] g := by
  apply ae_eq_of_integral_contDiff_smul_eq hf.locallyIntegrable hg.locallyIntegrable
  intro φ hφ hs
  obtain ⟨t, c, hc, ht⟩ := exists_smoothSpatialTest φ hφ hs
  have he := h t
  simp only [ht, mul_assoc, integral_const_mul] at he
  exact mul_left_cancel₀ hc.ne' he

theorem pair_eq_of_smooth_spatial_test_maps (p q : Pair)
    (hρ : ∀ t : SmoothSpatialTest, spatialDensityTest t.toBoundedSpatialTest p =
      spatialDensityTest t.toBoundedSpatialTest q)
    (hj : ∀ b, ∀ t : SmoothSpatialTest, spatialCurrentTest b t.toBoundedSpatialTest p =
      spatialCurrentTest b t.toBoundedSpatialTest q) : p = q := by
  apply pair_ext_ae
  · apply ae_eq_of_smoothSpatialTests (density_integrable p) (density_integrable q)
    intro t
    exact (spatialDensityTest_eq t.toBoundedSpatialTest p).symm.trans
      ((hρ t).trans (spatialDensityTest_eq t.toBoundedSpatialTest q))
  · have h (b : Fin 3) : (fun x => currentL1 p x b) =ᵐ[volume]
        (fun x => currentL1 q x b) := by
      apply ae_eq_of_smoothSpatialTests (current_component_integrable p b)
        (current_component_integrable q b)
      intro t
      exact (spatialCurrentTest_eq b t.toBoundedSpatialTest p).symm.trans
        ((hj b t).trans (spatialCurrentTest_eq b t.toBoundedSpatialTest q))
    filter_upwards [ae_all_iff.mpr h] with x hx
    exact PiLp.ext hx

end GptLean.PhysicalPairSpace
