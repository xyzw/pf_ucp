import PfHk.PhysicalScalarSobolev
import PfHk.InfiniteOrderMonotone

noncomputable section
namespace PfHk.PhysicalInfiniteOrder

open MeasureTheory Filter Set GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open GptLean.ElectronicH1Multiplier PfHk.PhysicalLocalEnergy
open PfHk.UniqueContinuationDensity
open scoped ENNReal Topology

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 20000
set_option Elab.async false

attribute [local irreducible] PhysicalPFReference.inclusion PhysicalPFScalarMultiplier.multiply
  PhysicalPFReference.ordinary PhysicalPFReference.radiation externalCovariant massOn

variable {I : Type} [Fintype I] [DecidableEq I]
variable (V : Position I → ℝ)
variable (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)
  (A : I → Position I → ℝ) (positive negative : Position I → ℝ)

/-- Infinite-order decay of mass transfers to the actual covariant and
radiation energy by the proved physical cutoff estimate. -/
theorem physical_energy_flat_of_mass_flat {E : ℝ} {u : Reference I V}
    {hu : ExternalDomain V A positive negative u}
    (heigen : IsExternalWeakEigenstate V C κ hκ M hbound e A positive negative E u hu)
    (C₀ : ℝ) (hnegative : ScalarMultiplierBound negative (1 / 4) C₀)
    {L : ℝ} (x₀ : Position I)
    (a : ∀ r : Ioc (0 : ℝ) 1, BallCutoff x₀ r L)
    (hflat : InfiniteOrder.FlatAtZero
      (fun r => massOn (Metric.ball x₀ r) (inclusion I V u))) :
    InfiniteOrder.FlatAtZero (fun r =>
      (∑ i, massOn (Metric.ball x₀ r)
        (externalCovariant V C κ hκ M hbound e A positive negative u hu i)) +
      massOn (Metric.ball x₀ r) (radiation I V u)) := by
  let K := 8 * (|E| + |C₀|) + 4 * Fintype.card I * L ^ 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  apply InfiniteOrder.energy_flat_of_mass_flat (K := K + 1) (R₀ := 1)
    (by linarith) zero_lt_one hflat
  intro r hr hr1
  let b := a ⟨r, hr, hr1⟩
  have hcov : (∑ i, massOn (Metric.ball x₀ r)
      (externalCovariant V C κ hκ M hbound e A positive negative u hu i)) ≤
      ∑ i, ‖externalCovariant V C κ hκ M hbound e A positive negative
        (PhysicalPFScalarMultiplier.multiply V b.multiplier u)
          (hu.localize V b.multiplier) i‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    exact b.local_norm_bound i (-Complex.I) (inclusion I V u) _ _
      (externalCovariant_localize V C κ hκ M hbound e A positive negative u hu b.multiplier i)
  have hrad := b.local_multiplier_bound (radiation I V u)
    (radiation I V (PhysicalPFScalarMultiplier.multiply V b.multiplier u))
    (PhysicalPFScalarMultiplier.radiation_multiply V b.multiplier u)
  have hbound := caccioppoli_localized V C κ hκ M hbound e A positive negative
    heigen C₀ hnegative hr hr1 b
  have hgrad := normGradientEnergy_nonneg V (PhysicalPFScalarMultiplier.multiply V b.multiplier u)
  have hlocal := add_le_add hcov hrad
  calc
    _ ≤ K / r ^ 2 * massOn (Metric.ball x₀ (2 * r)) (inclusion I V u) := by
      exact hlocal.trans ((le_add_of_nonneg_right hgrad).trans hbound)
    _ ≤ (K + 1) / r ^ 2 * massOn (Metric.ball x₀ (2 * r)) (inclusion I V u) :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (by linarith) (sq_nonneg r)) (massOn_nonneg _ _)

theorem physical_covariant_energy_flat_of_mass_flat {E : ℝ} {u : Reference I V}
    {hu : ExternalDomain V A positive negative u}
    (heigen : IsExternalWeakEigenstate V C κ hκ M hbound e A positive negative E u hu)
    (C₀ : ℝ) (hnegative : ScalarMultiplierBound negative (1 / 4) C₀)
    {L : ℝ} (x₀ : Position I)
    (a : ∀ r : Ioc (0 : ℝ) 1, BallCutoff x₀ r L)
    (hflat : InfiniteOrder.FlatAtZero
      (fun r => massOn (Metric.ball x₀ r) (inclusion I V u))) :
    InfiniteOrder.FlatAtZero (fun r => ∑ i, massOn (Metric.ball x₀ r)
      (externalCovariant V C κ hκ M hbound e A positive negative u hu i)) := by
  have htotal := physical_energy_flat_of_mass_flat V C κ hκ M hbound e A positive negative
    heigen C₀ hnegative x₀ a hflat
  apply InfiniteOrder.FlatAtZero.mono htotal
  intro r _
  exact le_add_of_nonneg_right (massOn_nonneg (Metric.ball x₀ r) (radiation I V u))

end PfHk.PhysicalInfiniteOrder
