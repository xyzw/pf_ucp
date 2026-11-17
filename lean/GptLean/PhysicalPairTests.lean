import GptLean.PhysicalPairSpace
import GptLean.RemovalPhysicalPair

/-! Scalar bounded spatial tests separate all components of the physical pair. -/

noncomputable section

namespace GptLean.PhysicalPairSpace

open MeasureTheory RemovalConstraints

theorem density_integrable (p : Pair) : Integrable (densityL1 p) volume :=
  memLp_one_iff_integrable.mp (Lp.memLp _)

theorem current_component_integrable (p : Pair) (b : Fin 3) :
    Integrable (fun x => currentL1 p x b) volume :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) b).integrable_comp
    (memLp_one_iff_integrable.mp (Lp.memLp (currentL1 p)))

theorem pair_eq_of_bounded_spatial_tests (p q : Pair)
    (hρ : ∀ t : BoundedSpatialTest (volume : Measure Position),
      (∫ x, t.weight x * densityL1 p x) = ∫ x, t.weight x * densityL1 q x)
    (hj : ∀ b : Fin 3, ∀ t : BoundedSpatialTest (volume : Measure Position),
      (∫ x, t.weight x * currentL1 p x b) = ∫ x, t.weight x * currentL1 q x b) : p = q := by
  apply pair_ext_ae
  · exact ae_eq_of_boundedSpatialTests (density_integrable p) (density_integrable q) hρ
  · have h (b : Fin 3) :
        (fun x => currentL1 p x b) =ᵐ[volume] (fun x => currentL1 q x b) :=
      ae_eq_of_boundedSpatialTests (current_component_integrable p b)
        (current_component_integrable q b) (hj b)
    filter_upwards [ae_all_iff.mpr h] with x hx
    exact PiLp.ext hx

end GptLean.PhysicalPairSpace
