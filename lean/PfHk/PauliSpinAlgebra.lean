import PfHk.PauliSpinMaps

/-! The local Pauli multiplication rules on arbitrary complex module fibers.
Together with linear-map compatibility they give the algebraic spin part
of the covariant Pauli identity. -/

noncomputable section
namespace PfHk.PauliSpin

variable {N : ℕ} {H : Type*} [AddCommGroup H] [Module ℂ H]

theorem sigma_zero_one (n : Fin N) (u : SpinIndex N → H) :
    sigmaFamily n 0 (sigmaFamily n 1 u) = Complex.I • sigmaFamily n 2 u := by
  funext s
  simp only [sigmaFamily_zero, sigmaFamily_one, sigmaFamily_two, sign_flip,
    flip_flip, Pi.smul_apply, smul_smul]
  module

theorem sigma_one_zero (n : Fin N) (u : SpinIndex N → H) :
    sigmaFamily n 1 (sigmaFamily n 0 u) = -Complex.I • sigmaFamily n 2 u := by
  funext s
  simp [smul_smul]

theorem sigma_one_two (n : Fin N) (u : SpinIndex N → H) :
    sigmaFamily n 1 (sigmaFamily n 2 u) = Complex.I • sigmaFamily n 0 u := by
  funext s
  simp only [sigmaFamily_one, sigmaFamily_two, sigmaFamily_zero, sign_flip,
    Pi.smul_apply, smul_smul]
  match_scalars
  ring_nf
  simp

theorem sigma_two_one (n : Fin N) (u : SpinIndex N → H) :
    sigmaFamily n 2 (sigmaFamily n 1 u) = -Complex.I • sigmaFamily n 0 u := by
  funext s
  simp only [sigmaFamily_one, sigmaFamily_two, sigmaFamily_zero, Pi.smul_apply, smul_smul]
  match_scalars
  ring_nf
  simp

theorem sigma_two_zero (n : Fin N) (u : SpinIndex N → H) :
    sigmaFamily n 2 (sigmaFamily n 0 u) = Complex.I • sigmaFamily n 1 u := by
  funext s
  simp only [sigmaFamily_one, sigmaFamily_two, sigmaFamily_zero, Pi.smul_apply, smul_smul]
  match_scalars
  ring_nf
  simp [Complex.I_sq]

theorem sigma_zero_two (n : Fin N) (u : SpinIndex N → H) :
    sigmaFamily n 0 (sigmaFamily n 2 u) = -Complex.I • sigmaFamily n 1 u := by
  funext s
  simp only [sigmaFamily_one, sigmaFamily_two, sigmaFamily_zero, sign_flip,
    Pi.smul_apply, smul_smul]
  match_scalars
  ring_nf
  simp [Complex.I_sq]

/-- The Clifford anticommutator, including the diagonal case. -/
theorem sigmaFamily_anticommutator (n : Fin N) (μ ν : Fin 3) (u : SpinIndex N → H) :
    sigmaFamily n μ (sigmaFamily n ν u) + sigmaFamily n ν (sigmaFamily n μ u) =
      (if μ = ν then (2 : ℂ) else 0) • u := by
  fin_cases μ <;> fin_cases ν <;>
    simp [sigmaFamily_square, sigma_zero_one, sigma_one_zero, sigma_one_two,
      sigma_two_one, sigma_two_zero, sigma_zero_two, two_smul]

end PfHk.PauliSpin
