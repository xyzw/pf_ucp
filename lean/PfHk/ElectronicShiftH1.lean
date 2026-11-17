import GptLean.TransformationsTranslationReference

/-! The ordinary H1 translation with its scalar structures fixed before
specialization to the photon Fock space. -/

noncomputable section
namespace PfHk.PhysicalElectronicShift

open GptLean GptLean.TransformationsAffine GptLean.TransformationsTranslation

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000

attribute [local irreducible] ElectronicH1Complex.complexWeakGraph
  ElectronicH1Complex.value ElectronicH1Complex.derivative

variable {I : Type} {H : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [NormedSpace ℝ H]
  [IsScalarTower ℝ ℂ H] [CompleteSpace H]

def h1Shift (c : EuclideanSpace ℝ I) (u : ElectronicH1Complex.ComplexH1 H I) :
    ElectronicH1Complex.ComplexH1 H I :=
  (AffineIsometry.translation c).pullH1Fun (E := H) u

theorem h1Shift_value (c : EuclideanSpace ℝ I) (u : ElectronicH1Complex.ComplexH1 H I) :
    ElectronicH1Complex.value (E := H) (I := I) (h1Shift (I := I) (H := H) c u) = shiftL2 (I := I) (F := H) c (ElectronicH1Complex.value (E := H) (I := I) u) :=
  ((AffineIsometry.translation c).value_pullH1 (E := H) u).trans
    (pull_eq_shiftL2 (I := I) (F := H) c _)

theorem h1Shift_derivative (c : EuclideanSpace ℝ I)
    (u : ElectronicH1Complex.ComplexH1 H I) (j : I) :
    ElectronicH1Complex.derivative (E := H) (I := I) j (h1Shift (I := I) (H := H) c u) =
      shiftL2 (I := I) (F := H) c (ElectronicH1Complex.derivative (E := H) (I := I) j u) :=
  ((AffineIsometry.translation c).derivative_pullH1 (E := H) j u).trans
    ((congrArg ((AffineIsometry.translation c).pull (E := H) ℂ)
      (AffineIsometry.translation_sum c j fun k => ElectronicH1Complex.derivative (E := H) (I := I) k u)).trans
        (pull_eq_shiftL2 (I := I) (F := H) c _))

end PfHk.PhysicalElectronicShift
