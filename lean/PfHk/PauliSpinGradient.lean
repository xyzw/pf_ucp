import PfHk.PauliCurrentCorrection

/-! Exact Pauli gradient cross terms and their cancellation for commuting
ordinary derivatives. The mixed-pairing hypothesis is an ordinary
integration-by-parts or Plancherel identity, not a Pauli estimate. -/

noncomputable section
namespace PfHk.PauliSpinGradient

open PauliSpin PauliCurrentAlgebra PauliCurrentCorrection
open scoped BigOperators

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The algebraic Pauli form expansion before inserting covariant
commutator identities. It retains all three antisymmetric cross terms. -/
theorem contraction_inner (n : Fin N)
    (d f : Fin 3 → SpinIndex N → H) :
    (∑ s, inner ℂ (contraction n d s) (contraction n f s)) =
      (∑ a, ∑ s, inner ℂ (d a s) (f a s)) + Complex.I *
        ((spinPair n (d 0) (f 1) 2 - spinPair n (d 1) (f 0) 2) +
          (spinPair n (d 1) (f 2) 0 - spinPair n (d 2) (f 1) 0) +
          (spinPair n (d 2) (f 0) 1 - spinPair n (d 0) (f 2) 1)) := by
  calc
    _ = ∑ a, ∑ b, ∑ s, inner ℂ (sigmaFamily n a (d a) s) (sigmaFamily n b (f b) s) := by
      simp only [contraction, Finset.sum_apply]
      simp_rw [sum_inner, inner_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ a, ∑ b, ∑ s, inner ℂ (d a s) (sigmaFamily n a (sigmaFamily n b (f b)) s) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      exact sigmaFamily_selfadjoint n a (d a) (sigmaFamily n b (f b))
    _ = _ := by
      simp only [Fin.sum_univ_three, sigmaFamily_square, sigma_zero_one, sigma_one_zero,
        sigma_one_two, sigma_two_one, sigma_two_zero, sigma_zero_two, Pi.smul_apply,
        inner_smul_right, ← Finset.mul_sum, spinPair]
      ring

/-- The free Pauli gradient has exactly the ordinary gradient norm.
The assumption holds for actual H1 weak derivatives by Plancherel. -/
theorem free_gradient_norm_sq (n : Fin N) (d : Fin 3 → SpinIndex N → H)
    (hmixed : ∀ a b s t, inner ℂ (d a s) (d b t) = inner ℂ (d b s) (d a t)) :
    (∑ s, ‖contraction n d s‖ ^ 2) = ∑ a, ∑ s, ‖d a s‖ ^ 2 := by
  have hreal (a b k : Fin 3) : (spinPair n (d a) (d b) k).im = 0 :=
    spinPair_im_of_symmetric n (d a) (d b) (hmixed b a) k
  have h := congrArg Complex.re (contraction_inner n d d)
  simp only [Complex.re_sum, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, Complex.add_im, Complex.sub_im, hreal, sub_self, add_zero,
    ] at h
  simpa only [← RCLike.re_to_complex, inner_self_eq_norm_sq] using h

end PfHk.PauliSpinGradient
