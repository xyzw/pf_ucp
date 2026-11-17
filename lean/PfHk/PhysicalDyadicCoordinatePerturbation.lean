import PfHk.PhysicalDyadicMagneticPerturbation
import PfHk.PhysicalCoordinateMultipliers
import PfHk.PhysicalDyadicSpectralZero

/-! Ordinary coordinate Sobolev and joint spectral calculus instantiate
all unweighted multiplier inputs of the concrete weighted perturbation estimates. -/

noncomputable section
namespace PfHk.PhysicalDyadicCoordinatePerturbation

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference GptLean.SymmetricLift
  PfHk.PhysicalLocalEnergy PfHk.PhysicalOperatorDomain PfHk.PhysicalDyadicIntegralFractional
  PfHk.PhysicalDyadicScalarPerturbation PfHk.PhysicalDyadicMagneticPerturbation
  PfHk.PhysicalCoordinateMultipliers PfHk.CoordinateSobolev
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 20000

attribute [local irreducible] inclusion covariant PhysicalPFScalarMultiplier.multiply roughMultiply
  PfHk.PhysicalDyadicPartition.localizedField GptLean.ElectronicH1Multiplier.DifferentiableMultiplier.multiplier
  ScalarFractionalMultiplier CovariantFractionalMultiplier
  fractionalNormSq fractionalVector

variable {N : ℕ}

theorem coordinate_scalar_endpoint (S : CoordinateSobolev.Data PhotonFock N)
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    (joint : CoordinateComparisonSpectral.Data spectral)
    {q : ℝ} (hq : 2 < q) (n : Fin N) (b : GptLean.PhysicalSourceCoordinates.Position → ℝ)
    (hb : MemLp b (ENNReal.ofReal q) volume) :
    ScalarFractionalMultiplier spectral (coordinateCoefficient n b) (3 / q)
      (coefficientNormSq S q b) := by
  unfold ScalarFractionalMultiplier
  intro u v hu
  exact scalar_multiplier S spectral joint hq n b hb u ⟨v, hu⟩

theorem coordinate_low_endpoint (S : CoordinateSobolev.Data PhotonFock N)
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    (joint : CoordinateComparisonSpectral.Data spectral)
    (n : Fin N) (b : GptLean.PhysicalSourceCoordinates.Position → ℝ) (hb : MemLp b 6 volume) :
    ScalarFractionalMultiplier spectral (coordinateCoefficient n b) (1 / 2)
      (coefficientNormSq S 6 b) := by
  have hb' : MemLp b (ENNReal.ofReal (6 : ℝ)) volume := by simpa using hb
  have h := coordinate_scalar_endpoint S spectral joint (by norm_num : (2 : ℝ) < 6) n b hb'
  norm_num at h
  exact h

theorem bounded_endpoint
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    (b : Configuration N → ℝ) (hb : MemLp b ∞ volume) :
    ScalarFractionalMultiplier spectral b 0 ((eLpNorm b ∞ volume).toReal ^ 2) := by
  unfold ScalarFractionalMultiplier
  intro u v hu
  have h := bounded_multiplier b hb (inclusion (Fin N × Fin 3) (fun _ => 0) u)
  let hm : HasMultiplier b (inclusion (Fin N × Fin 3) (fun _ => 0) u) := Classical.choose h
  have hzero : fractionalNormSq spectral 0 u ⟨v, hu⟩ =
      ‖inclusion (Fin N × Fin 3) (fun _ => 0) u‖ ^ 2 :=
    fractionalNormSq_zero spectral u ⟨v, hu⟩
  refine ⟨hm, (Classical.choose_spec h).trans_eq ?_⟩
  exact congrArg (fun r : ℝ => (eLpNorm b ∞ volume).toReal ^ 2 * r) hzero.symm

theorem coordinate_high_endpoint (S : CoordinateSobolev.Data PhotonFock N)
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    (joint : CoordinateComparisonSpectral.Data spectral)
    (C : CanonicalSectorCCR photonMeasure)
    (κ : (Fin N × Fin 3) → Configuration N → WeightedPhotonKernel)
    (hκ : ∀ i : Fin N × Fin 3, AEStronglyMeasurable (κ i) volume)
    (M : ℝ) (hbound : ∀ i : Fin N × Fin 3, ∀ᵐ x : Configuration N ∂volume, ‖(κ i x).val‖ ≤ M) (e : ℝ)
    (n : Fin N) (i : Fin N × Fin 3) (b : GptLean.PhysicalSourceCoordinates.Position → ℝ)
    (hb : MemLp b 6 volume) :
    CovariantFractionalMultiplier C κ hκ M hbound e spectral (coordinateCoefficient n b) i
      ((2 + 20 * e ^ 2 * (max M 0) ^ 2) * coefficientNormSq S 6 b) := by
  unfold CovariantFractionalMultiplier
  intro u v hu
  exact covariant_coordinate_multiplier S spectral joint C κ hκ M hbound e n i b hb u ⟨v, hu⟩

end PfHk.PhysicalDyadicCoordinatePerturbation
