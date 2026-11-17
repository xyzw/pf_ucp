import PfHk.PauliMagneticOperator
import PfHk.PauliLocalEnergy
import GptLean.PhysicalPFCovariantSymmetry

/-! Symmetry and electronic cutoff rules for the actual quantum Zeeman
multiplier. They follow from the existing physical field rules applied
to the magnetic coupling profile. -/

noncomputable section
namespace PfHk.PauliMagneticFormRules

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.SymmetricLift GptLean.ElectronicH1Multiplier
  PfHk.PauliSpin PfHk.PhysicalFieldRegularity PfHk.PauliMagneticOperator
open scoped InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 70000

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
attribute [local irreducible] referenceSubspace inclusion radiationSource
  PhysicalPFReference.field PhysicalPFScalarMultiplier.multiply
  DifferentiableMultiplier.multiplier

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ)
  (C : CanonicalSectorCCR photonMeasure)

theorem component_symmetric (n : Fin N) (k : Fin 3)
    (z u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    inner ℂ (inclusion (Fin N × Fin 3) (fun _ => 0) z) (component F χ hUV C n k u) =
      inner ℂ (component F χ hUV C n k z) (inclusion (Fin N × Fin 3) (fun _ => 0) u) := by
  have h := PhysicalPFReference.field_symmetric (Fin N × Fin 3) (fun _ => 0) C
    (fun _ => profile F χ hUV n k) (fun _ => profile_measurable F χ hUV n k)
    (2 * RadialGauge.momentBound F χ hUV) (fun _ => profile_bound F χ hUV n k)
    (n, k) z u
  unfold PhysicalPFReference.field at h
  exact h

theorem component_localize (a : DifferentiableMultiplier (Fin N × Fin 3))
    (n : Fin N) (k : Fin 3) (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    component F χ hUV C n k (PhysicalPFScalarMultiplier.multiply (fun _ => 0) a u) =
      a.multiplier (H := PhotonFock) (component F χ hUV C n k u) := by
  have h := PhysicalPFScalarMultiplier.field_multiply (fun _ => 0) a C
    (fun _ => profile F χ hUV n k) (fun _ => profile_measurable F χ hUV n k)
    (2 * RadialGauge.momentBound F χ hUV) (fun _ => profile_bound F χ hUV n k) u (n, k)
  unfold PhysicalPFReference.field at h
  exact h

theorem contraction_localize (a : DifferentiableMultiplier (Fin N × Fin 3))
    (n : Fin N) (u : PauliReference.Ref N) (s : SpinIndex N) :
    PauliMagneticOperator.contraction F χ hUV C n (PauliLocalEnergy.localize a u) s =
      a.multiplier (H := PhotonFock) (PauliMagneticOperator.contraction F χ hUV C n u s) := by
  have he (k : Fin 3) :
      (fun t => component F χ hUV C n k (PauliLocalEnergy.localize a u t)) =
        fun t => a.multiplier (H := PhotonFock) (component F χ hUV C n k (u t)) :=
    funext (fun t => component_localize F χ hUV C a n k (u t))
  unfold PauliMagneticOperator.contraction
  simp only [he, map_sum]
  exact Finset.sum_congr rfl (fun k _ => congrFun
    (sigmaFamily_map n k (a.multiplier (H := PhotonFock)).toLinearMap
      (fun t => component F χ hUV C n k (u t))) s)

theorem quantum_localize (a : DifferentiableMultiplier (Fin N × Fin 3))
    (e : ℝ) (u : PauliReference.Ref N) (s : SpinIndex N) :
    quantum F χ hUV C e (PauliLocalEnergy.localize a u) s =
      a.multiplier (H := PhotonFock) (quantum F χ hUV C e u s) := by
  unfold quantum
  simp only [contraction_localize, map_smul, map_sum]

end PfHk.PauliMagneticFormRules

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
