import PfHk.PauliCurrentAlgebra
import PfHk.PauliSpinMaps
import PfHk.FiniteWeightedSource

/-! Elementary bounds for Pauli contractions, used to recover ordinary
electronic derivatives from the actual Pauli kinetic form. -/

noncomputable section
namespace PfHk.PauliContractionBounds

open PauliSpin PauliCurrentAlgebra
set_option Elab.async false
set_option maxHeartbeats 30000

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem contraction_norm_sq_le (n : Fin N) (d : Fin 3 → SpinIndex N → H) :
    (∑ s, ‖contraction n d s‖ ^ 2) ≤ 3 * ∑ a, ∑ s, ‖d a s‖ ^ 2 := by
  have h (s : SpinIndex N) := FiniteWeightedSource.norm_sum_sq
    (Finset.univ : Finset (Fin 3)) (fun a => sigmaFamily n a (d a) s)
  calc
    _ ≤ 3 * ∑ s, ∑ a : Fin 3, ‖sigmaFamily n a (d a) s‖ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun s _ => by
        simpa only [contraction, Finset.sum_apply, Finset.card_univ,
          Fintype.card_fin, Nat.cast_ofNat] using h s)
    _ = _ := by
      congr 1
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun a _ => sigmaFamily_sum_norm_sq n a (d a))

omit [InnerProductSpace ℂ H] in
theorem three_square_bound (x y z : H) :
    ‖x + y + z‖ ^ 2 ≤ 3 * (‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2) := by
  have h := FiniteWeightedSource.norm_sum_sq (Finset.univ : Finset (Fin 3)) ![x, y, z]
  simpa [Fin.sum_univ_three] using h

theorem derivative_recovery (p q f a : H) (e : ℝ)
    (hp : p = q + (e : ℂ) • f - a) :
    ‖p‖ ^ 2 ≤ 3 * ‖q‖ ^ 2 + 3 * e ^ 2 * ‖f‖ ^ 2 + 3 * ‖a‖ ^ 2 := by
  have h := three_square_bound q ((e : ℂ) • f) (-a)
  rw [hp]
  simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
    norm_neg, ← sub_eq_add_neg] at h
  nlinarith only [h]

end PfHk.PauliContractionBounds
