import PfHk.PauliMagneticFormRules
import PfHk.PauliQuantumFormPairing
import PfHk.PauliZeemanFormAlgebra

/-! Hermitian symmetry of the actual quantum Zeeman form on all reference
spinors, obtained from the physical field symmetry and the Pauli trace. -/

noncomputable section
namespace PfHk.PauliMagneticFormRules

open GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.SymmetricLift PfHk.PauliSpin
  PfHk.PhysicalFieldRegularity PfHk.PauliSquareAlgebra PfHk.PauliMagneticOperator
open scoped InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 70000

private theorem conj_real_sum {J K : Type*} [Fintype J] [Fintype K]
    (c : ℝ) (b d : J → K → ℂ) (h : ∀ j k, star (b j k) = d j k) :
    star ((c : ℂ) * ∑ j, ∑ k, b j k) = (c : ℂ) * ∑ j, ∑ k, d j k := by
  change starRingEnd ℂ ((c : ℂ) * ∑ j, ∑ k, b j k) = _
  simp only [map_mul, map_sum, Complex.conj_ofReal]
  exact congrArg (fun z : ℂ => (c : ℂ) * z)
    (Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => h j k)

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
attribute [local irreducible] referenceSubspace inclusion component quantum

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ)
  (C : CanonicalSectorCCR photonMeasure)

theorem quantum_pairing_hermitian (e : ℝ) (z u : PauliReference.Ref N) :
    star (∑ s, inner ℂ (inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
      (quantum F χ hUV C e u s)) =
    ∑ s, inner ℂ (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))
      (quantum F χ hUV C e z s) := by
  have h (n : Fin N) (k : Fin 3) :
      star (matrixSpinTrace n k (fun s t => inner ℂ
        (inclusion (Fin N × Fin 3) (fun _ => 0) (z s)) (component F χ hUV C n k (u t)))) =
      matrixSpinTrace n k (fun s t => inner ℂ
        (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) (component F χ hUV C n k (z t))) := by
    apply PauliZeemanFormAlgebra.matrixSpinTrace_hermitian
    intro s t
    exact (inner_conj_symm _ _).trans (component_symmetric F χ hUV C n k (u s) (z t)).symm
  have hz := PauliQuantumFormPairing.quantum_pairing F χ hUV C e z u
  have hu := PauliQuantumFormPairing.quantum_pairing F χ hUV C e u z
  exact (congrArg star hz).trans ((conj_real_sum (-e / 2) _ _ h).trans hu.symm)

end PfHk.PauliMagneticFormRules

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
