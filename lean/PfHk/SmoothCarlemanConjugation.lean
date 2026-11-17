import PfHk.SmoothCarlemanWeight
import PfHk.CylinderConjugation

noncomputable section
namespace PfHk.CarlemanWeights

open CylinderConjugation
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem smoothExponential_weighted (τ α : ℝ) (u : ℝ → H) {t : ℝ} (ht : 2 ≤ t) :
    smoothExponential τ α t • u t = weighted τ (weight α) u t := by
  rw [smoothExponential_eq τ α (by linarith : 1≤t)]
  rfl

theorem smoothExponential_weightedFirst (τ α : ℝ) (u du : ℝ → H) {t : ℝ} (ht : 2 ≤ t) :
    smoothExponential τ α t • du t + deriv (smoothExponential τ α) t • u t =
      weightedFirst τ (weight α) (weightPrime α) u du t := by
  rw [smoothExponential_eq τ α (by linarith : 1≤t),
    smoothExponential_deriv τ α (by linarith : 1<t)]
  unfold weightedFirst
  module

theorem smoothExponential_weightedSecond (τ α : ℝ) (u du ddu : ℝ → H)
    {t : ℝ} (ht : 2 ≤ t) :
    smoothExponential τ α t • ddu t + (2 * deriv (smoothExponential τ α) t) • du t +
      deriv (deriv (smoothExponential τ α)) t • u t =
      weightedSecond τ (weight α) (weightPrime α) (beta α) u du ddu t := by
  rw [smoothExponential_eq τ α (by linarith : 1≤t),
    smoothExponential_deriv τ α (by linarith : 1<t),
    smoothExponential_second τ α (by linarith : 1<t)]
  unfold weightedSecond
  module

end PfHk.CarlemanWeights
