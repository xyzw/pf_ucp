import PfHk.PauliSquareAlgebra

/-! Conjugate transposition of finite Pauli matrix contractions. -/

noncomputable section
namespace PfHk.PauliZeemanFormAlgebra

open PfHk.PauliSpin PfHk.PauliSquareAlgebra
open scoped ComplexConjugate

set_option Elab.async false
set_option maxHeartbeats 30000

variable {N : ℕ}

theorem conj_matrixSpinTrace (n : Fin N) (k : Fin 3)
    (B : SpinIndex N → SpinIndex N → ℂ) :
    star (matrixSpinTrace n k B) =
      matrixSpinTrace n k (fun s t => star (B t s)) := by
  change starRingEnd ℂ (matrixSpinTrace n k B) = _
  fin_cases k
  · simp only [matrixSpinTrace, map_sum]
    refine Fintype.sum_equiv (flipEquiv n) _ _ ?_
    intro s
    simp [flipEquiv]
  · simp only [matrixSpinTrace, map_sum]
    refine Fintype.sum_equiv (flipEquiv n) _ _ ?_
    intro s
    simp [flipEquiv]
  · simp only [matrixSpinTrace, map_sum]
    apply Finset.sum_congr rfl
    intro s _
    simp

theorem matrixSpinTrace_hermitian (n : Fin N) (k : Fin 3)
    (B D : SpinIndex N → SpinIndex N → ℂ)
    (h : ∀ s t, star (B t s) = D s t) :
    star (matrixSpinTrace n k B) = matrixSpinTrace n k D := by
  rw [conj_matrixSpinTrace]
  congr 1
  funext s t
  exact h s t

end PfHk.PauliZeemanFormAlgebra
