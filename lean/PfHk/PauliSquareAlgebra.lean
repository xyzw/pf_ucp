import PfHk.PauliSpinGradient

/-! Finite-spin assembly of the weak Pauli square. Scalar component
commutators are contracted with the actual Pauli matrices. For the
momentum convention `-i ∂ + A - e A_ph`, the resulting magnetic signs are
`+ (1/2) σ·B_cl - (e/2) σ·B_ph`. The analytic component commutators are
inputs to these algebraic lemmas, rather than an assumed Pauli identity. -/

noncomputable section
namespace PfHk.PauliSquareAlgebra

open PauliSpin PauliCurrentAlgebra PauliCurrentCorrection
open scoped BigOperators InnerProductSpace

set_option Elab.async false
set_option maxHeartbeats 50000

variable {N : ℕ}

/-- Contraction of a matrix of scalar component pairings with one local
Pauli matrix. Only the second spin index is acted on. -/
def matrixSpinTrace (n : Fin N) (k : Fin 3)
    (B : SpinIndex N → SpinIndex N → ℂ) : ℂ :=
  ∑ s, sigmaFamily n k (B s) s

theorem matrixSpinTrace_add (n : Fin N) (k : Fin 3)
    (B C : SpinIndex N → SpinIndex N → ℂ) :
    matrixSpinTrace n k (B + C) = matrixSpinTrace n k B + matrixSpinTrace n k C := by
  simp only [matrixSpinTrace, Pi.add_apply, sigmaFamily_add, Finset.sum_add_distrib]

theorem matrixSpinTrace_smul (n : Fin N) (k : Fin 3) (c : ℂ)
    (B : SpinIndex N → SpinIndex N → ℂ) :
    matrixSpinTrace n k (c • B) = c * matrixSpinTrace n k B := by
  simp only [matrixSpinTrace, Pi.smul_apply, sigmaFamily_smul, smul_eq_mul, Finset.mul_sum]

theorem matrixSpinTrace_sub (n : Fin N) (k : Fin 3)
    (B C : SpinIndex N → SpinIndex N → ℂ) :
    matrixSpinTrace n k (B - C) = matrixSpinTrace n k B - matrixSpinTrace n k C := by
  rw [sub_eq_add_neg, show -C = (-1 : ℂ) • C by simp,
    matrixSpinTrace_add, matrixSpinTrace_smul]
  ring

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The scalar-matrix contraction is the usual spin-summed inner pairing. -/
theorem spinPair_eq_matrixSpinTrace (n : Fin N) (k : Fin 3)
    (z u : SpinIndex N → H) :
    spinPair n z u k = matrixSpinTrace n k (fun s t => inner ℂ (z s) (u t)) := by
  fin_cases k <;>
    simp [spinPair, matrixSpinTrace, inner_smul_right, smul_eq_mul]

/-- Every component commutator contributes with its Pauli coefficient.
No differentiability or operator-domain statement is assumed here. -/
theorem spinPair_sub_of_components (n : Fin N) (k : Fin 3)
    (z₁ z₂ u₁ u₂ : SpinIndex N → H)
    (B C : SpinIndex N → SpinIndex N → ℂ) (b c : ℂ)
    (h : ∀ s t, inner ℂ (z₁ s) (u₂ t) - inner ℂ (z₂ s) (u₁ t) =
      b * B s t + c * C s t) :
    spinPair n z₁ u₂ k - spinPair n z₂ u₁ k =
      b * matrixSpinTrace n k B + c * matrixSpinTrace n k C := by
  rw [spinPair_eq_matrixSpinTrace, spinPair_eq_matrixSpinTrace, ← matrixSpinTrace_sub]
  have hm : (fun s t => inner ℂ (z₁ s) (u₂ t)) -
      (fun s t => inner ℂ (z₂ s) (u₁ t)) = b • B + c • C := by
    funext s t
    exact h s t
  rw [hm, matrixSpinTrace_add, matrixSpinTrace_smul, matrixSpinTrace_smul]

/-- Sesquilinear Pauli-square identity from the three cyclic scalar
commutators. Addition on `Fin 3` gives the cyclic pair `(k+1,k+2)`. -/
theorem contraction_pairing_of_commutators (n : Fin N) (e : ℝ)
    (d f : Fin 3 → SpinIndex N → H)
    (Bcl Bq : Fin 3 → SpinIndex N → SpinIndex N → ℂ)
    (hcomm : ∀ k s t,
      inner ℂ (d (k + 1) s) (f (k + 2) t) -
        inner ℂ (d (k + 2) s) (f (k + 1) t) =
          -Complex.I * Bcl k s t + Complex.I * (e : ℂ) * Bq k s t) :
    (∑ s, inner ℂ (contraction n d s) (contraction n f s)) =
      (∑ a, ∑ s, inner ℂ (d a s) (f a s)) +
        (∑ k, matrixSpinTrace n k (Bcl k)) -
        (e : ℂ) * ∑ k, matrixSpinTrace n k (Bq k) := by
  have hc (k : Fin 3) := spinPair_sub_of_components n k
    (d (k + 1)) (d (k + 2)) (f (k + 1)) (f (k + 2))
    (Bcl k) (Bq k) (-Complex.I) (Complex.I * (e : ℂ)) (hcomm k)
  have h₀ := hc 0
  have h₁ := hc 1
  have h₂ := hc 2
  simp only [zero_add, show (1 : Fin 3) + 1 = 2 by rfl,
    show (1 : Fin 3) + 2 = 0 by rfl, show (2 : Fin 3) + 1 = 0 by rfl,
    show (2 : Fin 3) + 2 = 1 by rfl] at h₀ h₁ h₂
  rw [PauliSpinGradient.contraction_inner, h₂, h₀, h₁]
  simp only [Fin.sum_univ_three]
  ring_nf
  simp [Complex.I_sq]
  ring

/-- The kinetic factor one half gives the manuscript's exact Zeeman signs. -/
theorem kinetic_pairing_of_commutators (n : Fin N) (e : ℝ)
    (d f : Fin 3 → SpinIndex N → H)
    (Bcl Bq : Fin 3 → SpinIndex N → SpinIndex N → ℂ)
    (hcomm : ∀ k s t,
      inner ℂ (d (k + 1) s) (f (k + 2) t) -
        inner ℂ (d (k + 2) s) (f (k + 1) t) =
          -Complex.I * Bcl k s t + Complex.I * (e : ℂ) * Bq k s t) :
    (1 / 2 : ℂ) * (∑ s, inner ℂ (contraction n d s) (contraction n f s)) =
      (1 / 2 : ℂ) * (∑ a, ∑ s, inner ℂ (d a s) (f a s)) +
        (1 / 2 : ℂ) * (∑ k, matrixSpinTrace n k (Bcl k)) -
        ((e : ℂ) / 2) * ∑ k, matrixSpinTrace n k (Bq k) := by
  rw [contraction_pairing_of_commutators n e d f Bcl Bq hcomm]
  ring

/-- Sum the kinetic identity over electrons and retain all common
radiation and scalar terms unchanged. -/
theorem form_of_commutators (e : ℝ)
    (d f : Fin N → Fin 3 → SpinIndex N → H)
    (Bcl Bq : Fin N → Fin 3 → SpinIndex N → SpinIndex N → ℂ)
    (common : ℂ)
    (hcomm : ∀ n k s t,
      inner ℂ (d n (k + 1) s) (f n (k + 2) t) -
        inner ℂ (d n (k + 2) s) (f n (k + 1) t) =
          -Complex.I * Bcl n k s t + Complex.I * (e : ℂ) * Bq n k s t) :
    (1 / 2 : ℂ) * (∑ n, ∑ s,
      inner ℂ (contraction n (d n) s) (contraction n (f n) s)) + common =
      ((1 / 2 : ℂ) * (∑ n, ∑ a, ∑ s, inner ℂ (d n a s) (f n a s)) + common) +
        (1 / 2 : ℂ) * (∑ n, ∑ k, matrixSpinTrace n k (Bcl n k)) -
        ((e : ℂ) / 2) * ∑ n, ∑ k, matrixSpinTrace n k (Bq n k) := by
  have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun n _ =>
    contraction_pairing_of_commutators n e (d n) (f n) (Bcl n) (Bq n) (hcomm n))
  rw [hs]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

end Hilbert
end PfHk.PauliSquareAlgebra
