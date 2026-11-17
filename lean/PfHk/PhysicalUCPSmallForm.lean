import PfHk.ScalarPotentialSmallForm
import PfHk.PhysicalUCPCoefficients

/-! The negative form bound used by physical infinite-order vanishing follows
from the actual global scalar coefficient class. Nonnegative many-body
terms, including repulsive Coulomb terms, do not enter its constant. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed GptLean.SymmetricLift.TensorHilbert.inner
namespace PfHk.PhysicalUCPCoefficients

open GptLean.SymmetricLift PfHk.PhysicalLocalEnergy

variable {N : ℕ} {U : Set (Configuration N)}

theorem Data.negative_small_form (a : Data N U) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ScalarMultiplierBound a.negative ε C :=
  ScalarPotentialSmallForm.negative_bound_of_scalarPotential a.scalarCoefficient
    a.scalar_in_sum a.negative a.negative_measurable a.negative_sq_le hε

theorem Data.negative_quarter_form (a : Data N U) :
    ∃ C : ℝ, 0 ≤ C ∧ ScalarMultiplierBound a.negative (1 / 4) C :=
  a.negative_small_form (by norm_num)

end PfHk.PhysicalUCPCoefficients

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed GptLean.SymmetricLift.TensorHilbert.inner
