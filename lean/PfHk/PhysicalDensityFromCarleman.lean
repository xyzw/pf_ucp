import PfHk.PhysicalUniqueContinuation
import PfHk.NonvanishingDensity
import GptLean.PhysicalFockSeparable

/-! The continuation transfer on actual collision-free configuration
space gives positivity of the actual electronic density. The physical
Carleman estimate and full-space weak eigenstate are explicit inputs. -/

noncomputable section
namespace PfHk.PhysicalCarlemanInput

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open GptLean.SymmetricLift PfHk.PhysicalLocalEnergy PfHk.PhysicalInfiniteOrder

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 20000
set_option Elab.async false

variable {N : ℕ} (i : Fin N)
  (V : Configuration N → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Configuration N → WeightedPhotonKernel)
  (hκ : ∀ j, AEStronglyMeasurable (κ j) volume)
  (M : ℝ) (hbound : ∀ j, ∀ᵐ x ∂volume, ‖κ j x‖ ≤ M) (e : ℝ)
  (A : (Fin N × Fin 3) → Configuration N → ℝ) (positive negative : Configuration N → ℝ)

include i in
theorem configuration_density_positive {E α : ℝ}
    (hCarleman : UniformLocalOperatorCarleman V C κ hκ M hbound e A positive negative E α
      (distinctConfigurations N))
    (hα : 0 < α)
    {u : Reference (Fin N × Fin 3) V} {hu : ExternalDomain V A positive negative u}
    (heigen : IsExternalWeakEigenstate V C κ hκ M hbound e A positive negative E u hu)
    (C₀ : ℝ) (hnegative : ScalarMultiplierBound negative (1 / 4) C₀)
    {p q S : ℝ} (hpq : p.HolderConjugate q)
    (hd : (Fintype.card (Fin N × Fin 3) : ℝ) = 2 * q)
    (hS : 0 ≤ S) (hSob : ScalarSobolevBound (I := Fin N × Fin 3) p S)
    (hu_ne : inclusion (Fin N × Fin 3) V u ≠ 0) :
    ∀ᵐ x ∂volume, 0 < PhysicalElectronicDensity.density
      (inclusion (Fin N × Fin 3) V u) x := by
  letI : Nonempty (Fin N) := ⟨i⟩
  apply NonvanishingDensity.density_pos_ae i
  exact ae_nonzero_of_uniform_operatorCarleman V C κ hκ M hbound e A positive negative
    hCarleman hα (ConfigurationGeometry.regular_isConnected N).isPreconnected
    (ConfigurationGeometry.regular_ae N) heigen C₀ hnegative hpq hd hS hSob hu_ne

end PfHk.PhysicalCarlemanInput
