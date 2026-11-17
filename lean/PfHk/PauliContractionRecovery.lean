import PfHk.PauliContractionBounds

/-! Recovering the free Pauli contraction from the covariant contraction
and its two multiplication terms, with constants independent of the spin
dimension. -/

noncomputable section
namespace PfHk.PauliContractionRecovery

open PauliSpin PauliCurrentAlgebra PauliContractionBounds

set_option Elab.async false
set_option maxHeartbeats 20000

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem contraction_sub (n : Fin N) (d f : Fin 3 → SpinIndex N → H) :
    contraction n (d - f) = contraction n d - contraction n f := by
  rw [sub_eq_add_neg, show -f = (-1 : ℂ) • f by simp]
  rw [contraction_add, contraction_smul]
  simp only [neg_one_smul, sub_eq_add_neg]

theorem contraction_recovery (n : Fin N)
    (p q f a : Fin 3 → SpinIndex N → H) (e : ℝ)
    (hp : p = q + (e : ℂ) • f - a) :
    (∑ s, ‖contraction n p s‖ ^ 2) ≤
      3 * (∑ s, ‖contraction n q s‖ ^ 2) +
      9 * e ^ 2 * (∑ b, ∑ s, ‖f b s‖ ^ 2) +
      9 * (∑ b, ∑ s, ‖a b s‖ ^ 2) := by
  have heq : contraction n p =
      contraction n q + (e : ℂ) • contraction n f - contraction n a := by
    rw [hp, contraction_sub, contraction_add, contraction_smul]
  have hsum : (∑ s, ‖contraction n p s‖ ^ 2) ≤
      3 * (∑ s, ‖contraction n q s‖ ^ 2) +
      3 * e ^ 2 * (∑ s, ‖contraction n f s‖ ^ 2) +
      3 * (∑ s, ‖contraction n a s‖ ^ 2) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro s _
    exact PauliContractionBounds.derivative_recovery _ _ _ _ e (congrFun heq s)
  have hf := mul_le_mul_of_nonneg_left (contraction_norm_sq_le n f)
    (show 0 ≤ 3 * e ^ 2 by positivity)
  have ha := mul_le_mul_of_nonneg_left (contraction_norm_sq_le n a)
    (by norm_num : (0 : ℝ) ≤ 3)
  nlinarith only [hsum, hf, ha]

end PfHk.PauliContractionRecovery
