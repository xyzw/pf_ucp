import PfHk.PauliSquareAlgebra
import PfHk.PauliMagneticOperator

/-! Identification of the weak quantum magnetic term with the existing
physical Zeeman operator. The finite-spin contraction is taken after
the curl fields have been constructed as actual L2 vectors. -/

noncomputable section
namespace PfHk.PauliQuantumFormPairing

open PauliSpin PauliSquareAlgebra
open scoped BigOperators InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

variable {N : ℕ}

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The matrix trace is the pairing with the actual finite-spin
contraction, including its off-diagonal spin components. -/
theorem contraction_pairing (n : Fin N) (z : SpinIndex N → H)
    (u : Fin 3 → SpinIndex N → H) :
    (∑ k, matrixSpinTrace n k (fun s t => inner ℂ (z s) (u k t))) =
      ∑ s, inner ℂ (z s) (PauliCurrentAlgebra.contraction n u s) := by
  simp only [← spinPair_eq_matrixSpinTrace, PauliCurrentCorrection.spinPair,
    PauliCurrentAlgebra.contraction, Finset.sum_apply, inner_sum]
  exact Finset.sum_comm

/-- Pairing a scaled sum of electron contractions distributes into the
corresponding scalar Pauli traces. -/
theorem scaled_contraction_pairing (c : ℂ) (z : SpinIndex N → H)
    (u : Fin N → Fin 3 → SpinIndex N → H) :
    (∑ s, inner ℂ (z s)
      (c • ∑ n, PauliCurrentAlgebra.contraction n (u n) s)) =
      c * ∑ n, ∑ k, matrixSpinTrace n k (fun s t => inner ℂ (z s) (u n k t)) := by
  calc
    _ = c * ∑ s, ∑ n, inner ℂ (z s)
        (PauliCurrentAlgebra.contraction n (u n) s) := by
      simp only [inner_smul_right, inner_sum, Finset.mul_sum]
    _ = c * ∑ n, ∑ s, inner ℂ (z s)
        (PauliCurrentAlgebra.contraction n (u n) s) :=
      congrArg (fun w : ℂ => c * w) Finset.sum_comm
    _ = _ := congrArg (fun w : ℂ => c * w)
      (Finset.sum_congr rfl (fun n _ => (contraction_pairing n z (u n)).symm))

end Hilbert

open GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.PhysicalNonattainmentFluxKernel Gaussian
  GptLean.SymmetricLift GptLean.Representability PfHk.PhysicalFieldRegularity

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

variable (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ)
  (C : CanonicalSectorCCR photonMeasure)

/-- The existing quantum Zeeman operator has exactly the coefficient
and finite-spin pairing produced by the weak Pauli-square expansion. -/
theorem quantum_pairing (e : ℝ) (z u : PauliReference.Ref N) :
    (∑ s, inner ℂ (E := WaveSpace (Fin N × Fin 3))
      (inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
      (PauliMagneticOperator.quantum F χ hUV C e u s)) =
      ((-e / 2 : ℝ) : ℂ) * ∑ n, ∑ k,
        matrixSpinTrace n k (fun s t => inner ℂ (E := WaveSpace (Fin N × Fin 3))
          (inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
          (PauliMagneticOperator.component F χ hUV C n k (u t))) := by
  exact scaled_contraction_pairing (H := WaveSpace (Fin N × Fin 3))
    ((-e / 2 : ℝ) : ℂ)
    (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
    (fun n k t => PauliMagneticOperator.component F χ hUV C n k (u t))

end PfHk.PauliQuantumFormPairing

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
