import PfHk.ElectronicH1MixedPairing
import PfHk.PauliSpinGradient
import PfHk.PauliReference

/-! The free Pauli kinetic energy on the actual finite-spin H1 space.
Its equality with the ordinary gradient energy follows from the checked
mixed derivative pairing, with no additional spectral premise. -/

noncomputable section
namespace PfHk.PauliFreeGradient

open MeasureTheory GptLean GptLean.ElectronicH1Complex
  GptLean.PhysicalFock GptLean.PhysicalPFReference
  PauliSpin PauliCurrentAlgebra

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

local instance l2DirectInner : InnerProductSpace ℂ (ElectronicH1Space.L2 H (Fin N × Fin 3)) :=
  { (inferInstance : InnerProductSpace ℂ (ElectronicH1Space.L2 H (Fin N × Fin 3))) with
    toNormedSpace := (inferInstance : NormedSpace ℂ (ElectronicH1Space.L2 H (Fin N × Fin 3))) }

theorem norm_sq (u : SpinIndex N → ComplexH1 H (Fin N × Fin 3)) (n : Fin N) :
    (∑ s, ‖contraction n (fun a s => ElectronicH1Complex.derivative (E := H) (I := Fin N × Fin 3) (n, a) (u s)) s‖ ^ 2) =
      ∑ a : Fin 3, ∑ s, ‖ElectronicH1Complex.derivative (E := H) (I := Fin N × Fin 3) (n, a) (u s)‖ ^ 2 := by
  apply PauliSpinGradient.free_gradient_norm_sq
    (H := ElectronicH1Space.L2 H (Fin N × Fin 3))
  intro a b s t
  exact ElectronicH1MixedPairing.complex_pairing (H := H) (I := Fin N × Fin 3)
    (u s) (u t) (n, a) (n, b)

theorem momentum_norm_sq (u : SpinIndex N → ComplexH1 H (Fin N × Fin 3)) (n : Fin N) :
    (∑ s, ‖contraction n (fun a s => (-Complex.I) • ElectronicH1Complex.derivative (E := H) (I := Fin N × Fin 3) (n, a) (u s)) s‖ ^ 2) =
      ∑ a : Fin 3, ∑ s, ‖ElectronicH1Complex.derivative (E := H) (I := Fin N × Fin 3) (n, a) (u s)‖ ^ 2 := by
  let d : Fin 3 → SpinIndex N → ElectronicH1Space.L2 H (Fin N × Fin 3) :=
    fun a s => ElectronicH1Complex.derivative (E := H) (I := Fin N × Fin 3) (n, a) (u s)
  have h := contraction_smul n (-Complex.I) d
  have hn (s : SpinIndex N) := congrArg
    (fun f : SpinIndex N → ElectronicH1Space.L2 H (Fin N × Fin 3) => ‖f s‖ ^ 2) h
  simp only [Pi.smul_apply, norm_smul, norm_neg, Complex.norm_I, one_mul] at hn
  exact (Finset.sum_congr rfl (fun s _ => hn s)).trans (norm_sq (H := H) (N := N) u n)

theorem reference_norm_sq (u : PauliReference.Ref N) (n : Fin N) :
    (∑ s, ‖contraction n (fun a s =>
      (-Complex.I) • ordinary (Fin N × Fin 3) (fun _ => 0) (n, a) (u s)) s‖ ^ 2) =
      ∑ a : Fin 3, ∑ s,
        ‖ordinary (Fin N × Fin 3) (fun _ => 0) (n, a) (u s)‖ ^ 2 :=
  momentum_norm_sq (H := PhotonFock) (N := N)
    (fun s => electronic (Fin N × Fin 3) (fun _ => 0) (u s)) n

end PfHk.PauliFreeGradient
