import PfHk.PhysicalCutoffCommutatorEstimate
import PfHk.UniqueContinuationErrorComparison

/-! Infinite-order local mass and covariant-energy decay remove the
actual inner cutoff commutator in its weighted integral norm. -/

noncomputable section
namespace PfHk.PhysicalCutoffCommutator

open MeasureTheory Filter GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open GptLean.ElectronicH1Multiplier PfHk.PhysicalLocalEnergy
open scoped InnerProductSpace Topology ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 20000
set_option Elab.async false

attribute [local irreducible] PhysicalPFReference.covariant PhysicalPFReference.field
  PhysicalPFReference.ordinary PhysicalPFReference.inclusion PhysicalPFReference.radiation
  PhysicalPFReference.potential PhysicalPFScalarMultiplier.multiply
  roughMultiply externalCovariant massOn commutator

variable {I : Type} [Fintype I] [DecidableEq I]

variable (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)
  (A : I → Position I → ℝ) (positive negative : Position I → ℝ)

/-- The inner cutoff error for the actual physical operator tends to zero
when the actual mass and covariant energy vanish to infinite order. -/
theorem inner_commutator_tendsto (a : ℝ → TwiceDifferentiableMultiplier I) (u : Reference I V)
    (hu : ExternalDomain V A positive negative u) (x₀ : Position I)
    {α τ G L R : ℝ} (hα : 0 < α) (hτ : 0 ≤ τ)
    (hG : 0 ≤ G) (hL : 0 ≤ L) (hR : 0 < R) (hRsmall : 2 * R ≤ Real.exp (-2))
    (hgrad : ∀ ε, 0 < ε → ε ≤ R → ∀ x, ∑ i, (a ε).scalar.gradient i x ^ 2 ≤ G / ε ^ 2)
    (hlap : ∀ ε, 0 < ε → ε ≤ R → ∀ x, laplacian (a ε) x ^ 2 ≤ L / ε ^ 4)
    (houtgrad : ∀ ε, 0 < ε → ε ≤ R → ∀ x,
      x ∉ Metric.ball x₀ (2 * ε) \ Metric.ball x₀ ε → ∀ i, (a ε).scalar.gradient i x = 0)
    (houtlap : ∀ ε, 0 < ε → ε ≤ R → ∀ x,
      x ∉ Metric.ball x₀ (2 * ε) \ Metric.ball x₀ ε → laplacian (a ε) x = 0)
    (hmass : InfiniteOrder.FlatAtZero (fun r => massOn (Metric.ball x₀ r) (inclusion I V u)))
    (henergy : InfiniteOrder.FlatAtZero (fun r => ∑ i, massOn (Metric.ball x₀ r)
      (externalCovariant V C κ hκ M hbound e A positive negative u hu i))) :
    Filter.Tendsto (fun ε => ∫ x,
      Real.exp (2 * τ * CarlemanWeights.weight α (-Real.log (dist x x₀))) * (dist x x₀) ^ 2 *
        ‖commutator V C κ hκ M hbound e A positive negative (a ε) u hu x‖ ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  exact UniqueContinuation.tendsto_zero_of_inner_bound
    (U := fun r => massOn (Metric.ball x₀ r) (inclusion I V u))
    (K := fun r => ∑ i, massOn (Metric.ball x₀ r)
      (externalCovariant V C κ hκ M hbound e A positive negative u hu i))
    (fun r _ => massOn_nonneg _ _)
    (fun r _ => Finset.sum_nonneg fun i _ => massOn_nonneg _ _)
    hmass henergy hα.le hτ hR
    (fun ε => integral_nonneg fun x =>
      mul_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _)) (sq_nonneg _))
    (fun ε hε hεR => inner_annulus_commutator_bound
      V C κ hκ M hbound e A positive negative (a ε) u hu x₀
      hα hτ hε (by linarith) hG hL
      (hgrad ε hε hεR) (hlap ε hε hεR) (houtgrad ε hε hεR) (houtlap ε hε hεR))

end PfHk.PhysicalCutoffCommutator
