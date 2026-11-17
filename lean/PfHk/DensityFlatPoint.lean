import PfHk.UniqueContinuationDensity

noncomputable section
namespace PfHk.UniqueContinuationDensity

open MeasureTheory Filter Set
open scoped ENNReal Topology

set_option maxHeartbeats 10000
set_option Elab.async false

theorem exists_flat_point_of_density {I H : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup H] {ψ : EuclideanSpace ℝ I → H} {q : ℝ}
    (hd : (Fintype.card I : ℝ) = 2 * q) (hmeas : Measurable (fun x => ‖ψ x‖))
    {U : Set (EuclideanSpace ℝ I)} (hU : ∀ᵐ x ∂volume, x ∈ U)
    (hpositive : 0 < volume {x | ψ x = 0})
    (hflat : ∀ x₀, Tendsto (fun r =>
      (volume (nonzeroRegion ψ x₀ r)).toReal / r ^ (2 * q)) (𝓝[>] 0) (𝓝 0) →
        InfiniteOrder.FlatAtZero (localMass (μ := volume) ψ x₀)) :
    ∃ x₀ ∈ U, ψ x₀ = 0 ∧ InfiniteOrder.FlatAtZero (localMass (μ := volume) ψ x₀) := by
  have hZ : MeasurableSet {x | ψ x ≠ 0} := by
    simpa only [norm_pos_iff] using measurableSet_lt
      (measurable_const : Measurable (fun _ : EuclideanSpace ℝ I => (0 : ℝ))) hmeas
  obtain ⟨x₀, hxU, hxzero, hxdensity⟩ := exists_zero_density_point hZ hpositive hU
  refine ⟨x₀, hxU, hxzero, hflat x₀ ?_⟩
  convert hxdensity using 1
  funext r
  rw [← hd, Real.rpow_natCast]

end PfHk.UniqueContinuationDensity
