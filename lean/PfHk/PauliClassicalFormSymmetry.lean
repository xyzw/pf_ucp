import PfHk.PauliSquareForm
import PfHk.PauliZeemanFormAlgebra

/-! Hermitian symmetry of the real classical magnetic form. The identity
uses conjugation of the integral and the finite Pauli matrices. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliClassicalFormSymmetry

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  PfHk.PauliSpin PfHk.PauliGroundState PfHk.PauliSquareAlgebra
  PfHk.PauliClassicalCurlForm PfHk.PauliZeemanFormAlgebra
open scoped ComplexConjugate InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

theorem weightedInner_conj {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {μ : Measure X}
    (b : X → ℝ) (u v : Lp H 2 μ) (x : X) :
    star (weightedInner b u v x) = weightedInner b v u x := by
  change starRingEnd ℂ (weightedInner b u v x) = _
  simp only [weightedInner, map_mul, Complex.conj_ofReal, inner_conj_symm]

theorem pairing_conj {N : ℕ} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (n : Fin N) (b : PhysicalSourceCoordinates.Position → ℝ)
    (u v : ElectronicH1Space.L2 H (Fin N × Fin 3)) :
    star (pairing n b u v) = pairing n b v u := by
  change starRingEnd ℂ (∫ X, weightedInner (CoordinateSobolev.coordinateCoefficient n b) u v X) = _
  rw [← integral_conj]
  exact integral_congr_ae (Filter.Eventually.of_forall fun X => weightedInner_conj _ u v X)

attribute [local irreducible] referenceSubspace inclusion

private theorem half_trace_hermitian {N : ℕ}
    (B D : Fin N → Fin 3 → SpinIndex N → SpinIndex N → ℂ)
    (h : ∀ n k s t, star (B n k t s) = D n k s t) :
    star ((1 / 2 : ℂ) * ∑ n, ∑ k, matrixSpinTrace n k (B n k)) =
      (1 / 2 : ℂ) * ∑ n, ∑ k, matrixSpinTrace n k (D n k) := by
  change starRingEnd ℂ _ = _
  simp only [map_mul, map_div₀, map_one, map_ofNat, map_sum]
  apply congrArg (fun z : ℂ => (1 / 2 : ℂ) * z)
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro k _
  exact matrixSpinTrace_hermitian n k _ _ (h n k)

theorem classicalForm_hermitian {N : ℕ}
    (B : Fin N → Fin 3 → PhysicalSourceCoordinates.Position → ℝ) (z u : Ref N) :
    star (PauliSquareForm.classicalForm B z u) = PauliSquareForm.classicalForm B u z := by
  exact half_trace_hermitian
    (fun n k s t => pairing n (B n k)
      (inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u t)))
    (fun n k s t => pairing n (B n k)
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))
      (inclusion (Fin N × Fin 3) (fun _ => 0) (z t)))
    (fun n k s t => pairing_conj n (B n k) _ _)

end PfHk.PauliClassicalFormSymmetry

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
