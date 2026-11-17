import PfHk.PauliOrbitalForm
import PfHk.PauliClassicalCurlForm
import PfHk.PauliQuantumFormPairing

/-! Assemble the component commutators into the actual sesquilinear
Pauli form. The classical curl is an integrable form pairing. The quantum
term is the already constructed physical Zeeman multiplier. -/

noncomputable section
namespace PfHk.PauliSquareForm

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.SymmetricLift PfHk.PauliSpin PfHk.PauliGroundState
  PfHk.PhysicalLocalEnergy PfHk.PauliSquareAlgebra
open scoped InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 70000

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
attribute [local irreducible] referenceSubspace inclusion radiation roughMultiply
  externalCovariant PauliMagneticOperator.component PauliMagneticOperator.quantum

variable {N : ℕ}

private theorem assemble (P O KP KO classical quantum trace : ℂ) (e : ℝ)
    (hp : P = KP) (ho : O = KO)
    (hq : quantum = ((-e / 2 : ℝ) : ℂ) * trace)
    (h : KP = KO + classical - (e : ℂ) / 2 * trace) :
    P = O + classical + quantum := by
  rw [hp, ho, hq, h]
  push_cast
  ring

/-- Classical Zeeman form with the kinetic factor one half. -/
def classicalForm
    (B : Fin N → Fin 3 → GptLean.PhysicalSourceCoordinates.Position → ℝ)
    (z u : Ref N) : ℂ :=
  (1 / 2 : ℂ) * ∑ n, ∑ k, matrixSpinTrace n k (fun s t =>
    PauliClassicalCurlForm.pairing n (B n k)
      (inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u t)))

variable (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Configuration N → WeightedPhotonKernel)
  (hκ : ∀ q, AEStronglyMeasurable (κ q) volume)
  (M : ℝ) (hκbound : ∀ q, ∀ᵐ X ∂volume, ‖κ q X‖ ≤ M) (e : ℝ)
  (F : Frame) (χ : ArticleCutoff) (hUV : PhysicalFieldRegularity.CarlemanUV χ)
  (A : (Fin N × Fin 3) → Configuration N → ℝ)
  (positive negative : Configuration N → ℝ)
  (B : Fin N → Fin 3 → GptLean.PhysicalSourceCoordinates.Position → ℝ)

/-- Algebraic assembly for the existing forms. The physical weak curl
theorem supplies the component identities in the public local endpoint. -/
theorem of_component_commutators (z u : Ref N)
    (hz : Domain A positive negative z) (hu : Domain A positive negative u)
    (hcomm : ∀ n k s t,
      inner ℂ (rawCovariant C κ hκ M hκbound e A positive negative z hz (n, k + 1) s)
        (rawCovariant C κ hκ M hκbound e A positive negative u hu (n, k + 2) t) -
      inner ℂ (rawCovariant C κ hκ M hκbound e A positive negative z hz (n, k + 2) s)
        (rawCovariant C κ hκ M hκbound e A positive negative u hu (n, k + 1) t) =
      -Complex.I * PauliClassicalCurlForm.pairing n (B n k)
        (inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
        (inclusion (Fin N × Fin 3) (fun _ => 0) (u t)) +
      Complex.I * (e : ℂ) * inner ℂ
        (inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
        (PauliMagneticOperator.component F χ hUV C n k (u t))) :
    rawForm C κ hκ M hκbound e A positive negative z u hz hu =
      PauliOrbitalForm.form C κ hκ M hκbound e A positive negative z u hz hu +
        classicalForm B z u +
        ∑ s, inner ℂ (inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
          (PauliMagneticOperator.quantum F χ hUV C e u s) := by
  have h := form_of_commutators (H := WaveSpace (Fin N × Fin 3)) e
    (fun n a s => rawCovariant C κ hκ M hκbound e A positive negative z hz (n, a) s)
    (fun n a s => rawCovariant C κ hκ M hκbound e A positive negative u hu (n, a) s)
    (fun n k s t => PauliClassicalCurlForm.pairing n (B n k)
      (inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u t)))
    (fun n k s t => inner ℂ (inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
      (PauliMagneticOperator.component F χ hUV C n k (u t)))
    (PauliOrbitalForm.common A positive negative z u hz hu) hcomm
  have hp := PauliOrbitalForm.rawForm_eq C κ hκ M hκbound e A positive negative z u hz hu
  have ho := PauliOrbitalForm.form_eq C κ hκ M hκbound e A positive negative z u hz hu
  have hq := PauliQuantumFormPairing.quantum_pairing F χ hUV C e z u
  exact assemble _ _ _ _ _ _ _ e hp ho hq h

end PfHk.PauliSquareForm

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
