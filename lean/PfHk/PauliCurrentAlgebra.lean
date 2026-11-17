import PfHk.PauliSpin

/-! The current conjugate to a real external vector potential in the
actual finite-spin Pauli kinetic square. These are identities for arbitrary
complex Hilbert-space coefficients, including photon and spatial L2 fibers.
No energy decomposition is assumed. -/

noncomputable section
namespace PfHk.PauliCurrentAlgebra

open PfHk.PauliSpin
open scoped BigOperators InnerProductSpace

set_option Elab.async false
set_option maxHeartbeats 200000

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Pauli contraction of the three covariant derivatives at one electron. -/
def contraction (n : Fin N) (d : Fin 3 → SpinIndex N → H) : SpinIndex N → H :=
  ∑ a, sigmaFamily n a (d a)

/-- The velocity obtained by differentiating the Pauli kinetic square. -/
def velocity (n : Fin N) (a : Fin 3) (d : Fin 3 → SpinIndex N → H) :
    SpinIndex N → H :=
  sigmaFamily n a (contraction n d)

def density (u : SpinIndex N → H) : ℝ := ∑ s, ‖u s‖ ^ 2

def current (n : Fin N) (u : SpinIndex N → H)
    (d : Fin 3 → SpinIndex N → H) (a : Fin 3) : ℝ :=
  ∑ s, (inner ℂ (u s) (velocity n a d s)).re

def kinetic (n : Fin N) (d : Fin 3 → SpinIndex N → H) : ℝ :=
  (1 / 2 : ℝ) * ∑ s, ‖contraction n d s‖ ^ 2

omit [InnerProductSpace ℂ H] in
theorem density_nonneg (u : SpinIndex N → H) : 0 ≤ density u :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem kinetic_nonneg (n : Fin N) (d : Fin 3 → SpinIndex N → H) :
    0 ≤ kinetic n d :=
  mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem contraction_add (n : Fin N) (d f : Fin 3 → SpinIndex N → H) :
    contraction n (d + f) = contraction n d + contraction n f := by
  simp only [contraction, Pi.add_apply, sigmaFamily_add, Finset.sum_add_distrib]

theorem contraction_smul (n : Fin N) (c : ℂ) (d : Fin 3 → SpinIndex N → H) :
    contraction n (c • d) = c • contraction n d := by
  simp only [contraction, Pi.smul_apply, sigmaFamily_smul, Finset.smul_sum]

theorem contraction_vector (n : Fin N) (b : Fin 3 → ℝ) (u : SpinIndex N → H) :
    contraction n (fun a => (b a : ℂ) • u) = fieldFamily n b u := by
  funext s
  simp only [contraction, Finset.sum_apply, sigmaFamily_smul, Pi.smul_apply,
    fieldFamily_eq_sum]

theorem contraction_shift (n : Fin N) (d : Fin 3 → SpinIndex N → H)
    (b : Fin 3 → ℝ) (u : SpinIndex N → H) :
    contraction n (fun a => d a + (b a : ℂ) • u) =
      contraction n d + fieldFamily n b u := by
  exact (contraction_add n d (fun a => (b a : ℂ) • u)).trans
    (congrArg (contraction n d + ·) (contraction_vector n b u))

theorem velocity_selfadjoint (n : Fin N) (u : SpinIndex N → H)
    (d : Fin 3 → SpinIndex N → H) (a : Fin 3) :
    (∑ s, (inner ℂ (sigmaFamily n a u s) (contraction n d s)).re) =
      current n u d a := by
  have h := congrArg Complex.re (sigmaFamily_selfadjoint n a u (contraction n d))
  simpa only [Complex.re_sum, current, velocity] using h

theorem field_current_pairing (n : Fin N) (u : SpinIndex N → H)
    (d : Fin 3 → SpinIndex N → H) (b : Fin 3 → ℝ) :
    (∑ s, (inner ℂ (contraction n d s) (fieldFamily n b u s)).re) =
      ∑ a, b a * current n u d a := by
  calc
    _ = ∑ s, (inner ℂ (fieldFamily n b u s) (contraction n d s)).re := by
      apply Finset.sum_congr rfl
      intro s _
      exact inner_re_symm (𝕜 := ℂ) _ _
    _ = ∑ s, ∑ a, b a *
        (inner ℂ (sigmaFamily n a u s) (contraction n d s)).re := by
      apply Finset.sum_congr rfl
      intro s _
      simp only [fieldFamily_eq_sum, sum_inner, inner_smul_left,
        Complex.re_sum, Complex.conj_ofReal, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    _ = ∑ a, b a * ∑ s,
        (inner ℂ (sigmaFamily n a u s) (contraction n d s)).re := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = _ := by simp only [velocity_selfadjoint]

/-- Exact external-potential contribution of the Pauli kinetic square.
The coefficient of the linear term is the Pauli current, including spin. -/
theorem kinetic_shift (n : Fin N) (u : SpinIndex N → H)
    (d : Fin 3 → SpinIndex N → H) (b : Fin 3 → ℝ) :
    kinetic n (fun a => d a + (b a : ℂ) • u) =
      kinetic n d + ∑ a, b a * current n u d a +
        (1 / 2 : ℝ) * (∑ a, b a ^ 2) * density u := by
  rw [kinetic, contraction_shift]
  simp only [Pi.add_apply, norm_add_sq (𝕜 := ℂ), RCLike.re_to_complex,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [field_current_pairing, fieldFamily_sum_norm_sq]
  unfold kinetic density
  ring

end PfHk.PauliCurrentAlgebra
