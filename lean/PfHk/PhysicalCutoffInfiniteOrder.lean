import PfHk.PhysicalCutoffCommutatorLimit
import PfHk.PhysicalInfiniteOrder

/-! Physical Caccioppoli supplies the energy decay in the inner cutoff
passage. Thus only infinite-order mass decay remains as a premise here. -/

noncomputable section
namespace PfHk.PhysicalCutoffCommutator

open MeasureTheory Filter Set GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open PfHk.PhysicalLocalEnergy
open scoped Topology

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 20000
set_option Elab.async false

variable {I : Type} [Fintype I] [DecidableEq I]
  (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)
  (A : I → Position I → ℝ) (positive negative : Position I → ℝ)

theorem eigenstate_inner_commutator_tendsto
    (a : ℝ → TwiceDifferentiableMultiplier I) (u : Reference I V)
    (hu : ExternalDomain V A positive negative u) (x₀ : Position I)
    {E : ℝ}
    (heigen : IsExternalWeakEigenstate V C κ hκ M hbound e A positive negative E u hu)
    (C₀ : ℝ) (hnegative : ScalarMultiplierBound negative (1 / 4) C₀)
    {L₀ : ℝ} (b : ∀ r : Ioc (0 : ℝ) 1, BallCutoff x₀ r L₀)
    {α τ G L R : ℝ} (hα : 0 < α) (hτ : 0 ≤ τ)
    (hG : 0 ≤ G) (hL : 0 ≤ L) (hR : 0 < R) (hRsmall : 2 * R ≤ Real.exp (-2))
    (hgrad : ∀ ε, 0 < ε → ε ≤ R → ∀ x, ∑ i, (a ε).scalar.gradient i x ^ 2 ≤ G / ε ^ 2)
    (hlap : ∀ ε, 0 < ε → ε ≤ R → ∀ x, laplacian (a ε) x ^ 2 ≤ L / ε ^ 4)
    (houtgrad : ∀ ε, 0 < ε → ε ≤ R → ∀ x,
      x ∉ Metric.ball x₀ (2 * ε) \ Metric.ball x₀ ε → ∀ i, (a ε).scalar.gradient i x = 0)
    (houtlap : ∀ ε, 0 < ε → ε ≤ R → ∀ x,
      x ∉ Metric.ball x₀ (2 * ε) \ Metric.ball x₀ ε → laplacian (a ε) x = 0)
    (hmass : InfiniteOrder.FlatAtZero (fun r => massOn (Metric.ball x₀ r) (inclusion I V u))) :
    Tendsto (fun ε => ∫ x,
      Real.exp (2 * τ * CarlemanWeights.weight α (-Real.log (dist x x₀))) * (dist x x₀) ^ 2 *
        ‖commutator V C κ hκ M hbound e A positive negative (a ε) u hu x‖ ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  exact inner_commutator_tendsto V C κ hκ M hbound e A positive negative a u hu x₀
    hα hτ hG hL hR hRsmall hgrad hlap houtgrad houtlap hmass
    (PhysicalInfiniteOrder.physical_covariant_energy_flat_of_mass_flat
      V C κ hκ M hbound e A positive negative heigen C₀ hnegative x₀ b hmass)

end PfHk.PhysicalCutoffCommutator
