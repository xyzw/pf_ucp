import PfHk.MultiplierNormAlgebra

/-! Scalar arithmetic for field multiplier estimates, kept independent of
the concrete Fock representation. -/

noncomputable section
namespace PfHk.MultiplierNormAlgebra

theorem field_square {H : Type*} [NormedAddCommGroup H]
    (M : ℝ) (f r v : H) (h : ‖f‖ ≤ 2 * M * ‖r‖ + M * ‖v‖) :
    ‖f‖ ^ 2 ≤ 8 * M ^ 2 * ‖r‖ ^ 2 + 2 * M ^ 2 * ‖v‖ ^ 2 := by
  have hs := two_term_square (norm_nonneg f) h
  nlinarith only [hs]

theorem covariant_square_combine (e M a p f r v : ℝ)
    (ha : a ≤ 2 * p + (2 * e ^ 2) * f)
    (hf : f ≤ 8 * M ^ 2 * r + 2 * M ^ 2 * v) :
    a ≤ 2 * p + 16 * e ^ 2 * M ^ 2 * r + 4 * e ^ 2 * M ^ 2 * v := by
  have hmul := mul_le_mul_of_nonneg_left hf (by positivity : 0 ≤ 2 * e ^ 2)
  nlinarith only [ha, hmul]

end PfHk.MultiplierNormAlgebra
