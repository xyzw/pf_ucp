import PfHk.FriedrichsDivergenceBackground
import PfHk.SignedScalarMultiplier
import GptLean.PhysicalPairDuality
import GptLean.PhysicalCoulombH1

/-! Identical-particle coefficients shared by the common form and the
physical continuation coefficient package. -/

noncomputable section
namespace PfHk.PhysicalCommonFormDomain

open GptLean.PhysicalPairDuality GptLean.PhysicalSourceCoordinates
open PfHk.CoordinateSobolev PfHk.FriedrichsDivergenceBackground

variable {N : ℕ}

def vectorCoefficient (A : VectorPotential) : Fin N → Fin 3 → Position → ℝ :=
  fun _ i x => A.val x i

def vector (A : VectorPotential) : (Fin N × Fin 3) → Configuration N → ℝ :=
  configurationVector (vectorCoefficient A)

def scalar (v : ScalarPotential) (c : ℝ) (X : Configuration N) : ℝ :=
  (∑ n : Fin N, coordinateCoefficient n (v.val : Position → ℝ) X) +
    c * GptLean.PhysicalCoulombH1.potential N X

def positive (v : ScalarPotential) (c : ℝ) : Configuration N → ℝ :=
  SignedScalarMultiplier.positiveAmplitude (scalar v c)

def negative (v : ScalarPotential) (c : ℝ) : Configuration N → ℝ :=
  SignedScalarMultiplier.negativeAmplitude (scalar v c)

end PfHk.PhysicalCommonFormDomain
