import PfHk.PhysicalUCPCoefficients
import PfHk.PhysicalCoulombLocalBound

/-! Actual repulsive Coulomb interactions give the nonnegative locally
bounded remainder in the global coefficient package for continuation. -/

noncomputable section
namespace PfHk.PhysicalCoulombUCPCoefficients

open MeasureTheory GptLean GptLean.SymmetricLift
  PfHk.PhysicalUCPCoefficients PfHk.FriedrichsDivergenceBackground
open scoped ENNReal

set_option Elab.async false
set_option maxHeartbeats 20000

def data {N : ℕ}
    (A : Fin N → Fin 3 → ElectronicPosition → ℝ)
    (d v : Fin N → ElectronicPosition → ℝ)
    (ell p : ℝ) (hell : 2 < ell) (hp : 2 < p)
    (hA : ∀ n i (o : ElectronicPosition) (r : ℝ), 0 < r →
      MemLp (A n i) 6 (volume.restrict (Metric.ball o r)))
    (hd : ∀ n (o : ElectronicPosition) (r : ℝ), 0 < r →
      MemLp (d n) (ENNReal.ofReal ell) (volume.restrict (Metric.ball o r)))
    (hv : ∀ n (o : ElectronicPosition) (r : ℝ), 0 < r →
      MemLp (v n) (ENNReal.ofReal p) (volume.restrict (Metric.ball o r)))
    (hdiv : ∀ n, WeakDivergence (A n) (d n))
    (hsum : ∀ n, ∃ w : PhysicalPairDuality.ScalarPotential,
      v n =ᵐ[volume] (w.val : ElectronicPosition → ℝ))
    (c : ℝ) (hc : 0 ≤ c) : Data N (distinctConfigurations N) where
  vectorCoefficient := A
  divergenceCoefficient := d
  scalarCoefficient := v
  boundedCoefficient := fun X => c * PhysicalCoulombH1.potential N X
  divergenceExponent := ell
  scalarExponent := p
  divergenceExponent_gt_two := hell
  scalarExponent_gt_two := hp
  vector_local_memLp := hA
  divergence_local_memLp := hd
  scalar_local_memLp := hv
  weakDivergence := hdiv
  scalar_in_sum := hsum
  bounded_measurable :=
    (PhysicalCoulombLocalBound.scaled_potential_measurable c).aestronglyMeasurable
  bounded_nonneg := Filter.Eventually.of_forall
    (PhysicalCoulombLocalBound.scaled_potential_nonneg c hc)
  bounded_local_memLp := fun _ hO =>
    PhysicalCoulombLocalBound.scaled_potential_local_memLp c hO

end PfHk.PhysicalCoulombUCPCoefficients
