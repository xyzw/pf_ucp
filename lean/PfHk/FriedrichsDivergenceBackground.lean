import PfHk.CoordinateMultiplication
import GptLean.ElectronicH1DifferentiableMultiplier

/-! Ordinary Friedrichs approximation for one-body vector fields with a
distributional divergence. This background contains only scalar functions,
their derivatives and Lq convergence. No Hilbert-valued multiplier estimate,
PF operator identity or operator-domain conclusion is a field. -/

noncomputable section
namespace PfHk.FriedrichsDivergenceBackground

open MeasureTheory Filter GptLean.PhysicalSourceCoordinates
open GptLean.ElectronicH1Multiplier PfHk.CoordinateSobolev
open scoped ENNReal Topology ContDiff

def WeakDivergence (A : Fin 3 → Position → ℝ) (d : Position → ℝ) : Prop :=
  ∀ φ : Position → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ x, d x * φ x) =
      -(∑ i : Fin 3, ∫ x, A i x * fderiv ℝ φ x (EuclideanSpace.single i 1))

def configurationVector {N : ℕ} (A : Fin N → Fin 3 → Position → ℝ)
    (i : Fin N × Fin 3) : Configuration N → ℝ := coordinateCoefficient i.1 (A i.1 i.2)

def configurationDivergence {N : ℕ} (d : Fin N → Position → ℝ) : Configuration N → ℝ :=
  fun x => ∑ n, coordinateCoefficient n (d n) x

/-- A sequence from ordinary convolution. Pullback identities describe the
actual coefficient error and the actual trace of its derivative. -/
structure Approximation {N : ℕ} (A : Fin N → Fin 3 → Position → ℝ)
    (d : Fin N → Position → ℝ) (q : ℝ) where
  coefficient : ℕ → (Fin N × Fin 3) → DifferentiableMultiplier (Fin N × Fin 3)
  vectorError : ℕ → (Fin N × Fin 3) → Position → ℝ
  divergenceError : ℕ → Fin N → Position → ℝ
  vector_memLp : ∀ k i, MemLp (vectorError k i) 6 volume
  divergence_memLp : ∀ k n, MemLp (divergenceError k n) (ENNReal.ofReal q) volume
  vector_tendsto : ∀ i, Tendsto
    (fun k => (eLpNorm (vectorError k i) 6 volume).toReal) atTop (𝓝 0)
  divergence_tendsto : ∀ n, Tendsto
    (fun k => (eLpNorm (divergenceError k n) (ENNReal.ofReal q) volume).toReal) atTop (𝓝 0)
  vector_identity : ∀ k i x,
    (coefficient k i).weight x - configurationVector A i x =
      coordinateCoefficient i.1 (vectorError k i) x
  divergence_identity : ∀ k x,
    (∑ i, (coefficient k i).gradient i x) - configurationDivergence d x =
      ∑ n, coordinateCoefficient n (divergenceError k n) x

/-- Simultaneous Friedrichs approximation in L6 for a vector field and in
Lq for its distributional divergence. The selected particle pullbacks are
ordinary finite-dimensional linear maps. -/
structure StandardFriedrichsDivergence where
  resolve : ∀ (N : ℕ) (A : Fin N → Fin 3 → Position → ℝ)
    (d : Fin N → Position → ℝ) (q : ℝ), 2 < q →
    (∀ n i, MemLp (A n i) 6 volume) →
    (∀ n, MemLp (d n) (ENNReal.ofReal q) volume) →
    (∀ n, WeakDivergence (A n) (d n)) → Approximation A d q

end PfHk.FriedrichsDivergenceBackground
