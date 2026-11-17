import GptLean.ElectronicH1DifferentiableMultiplier

/-! The scalar cutoff data used in the physical local-energy estimate. -/

noncomputable section
namespace PfHk.PhysicalLocalEnergy

open GptLean.ElectronicH1Multiplier

variable {I : Type} [Fintype I] [DecidableEq I]

structure BallCutoff (x₀ : EuclideanSpace ℝ I) (r L : ℝ) where
  multiplier : DifferentiableMultiplier I
  nonneg : ∀ x, 0 ≤ multiplier.weight x
  le_one : ∀ x, multiplier.weight x ≤ 1
  eq_one : ∀ x ∈ Metric.ball x₀ r, multiplier.weight x = 1
  eq_zero : ∀ x ∉ Metric.ball x₀ (2 * r), multiplier.weight x = 0
  gradient_bound : ∀ i x, |multiplier.gradient i x| ≤ L / r

end PfHk.PhysicalLocalEnergy
