import PfHk.PauliCurrentAlgebra
import PfHk.PauliSpinAlgebra

/-! The Pauli velocity current is the orbital current plus half the curl
of magnetization. The algebra is proved on arbitrary complex Hilbert fibers.
Field expectations enter only through their reality, as supplied by a
symmetric field operator commuting with the spin matrices. -/

noncomputable section
namespace PfHk.PauliCurrentCorrection

open PauliSpin PauliCurrentAlgebra
open scoped BigOperators ComplexConjugate

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def spinPair (n : Fin N) (u v : SpinIndex N → H) (k : Fin 3) : ℂ :=
  ∑ s, inner ℂ (u s) (sigmaFamily n k v s)

theorem spinPair_add (n : Fin N) (u v w : SpinIndex N → H) (k : Fin 3) :
    spinPair n u (v + w) k = spinPair n u v k + spinPair n u w k := by
  simp only [spinPair, sigmaFamily_add, Pi.add_apply, inner_add_right, Finset.sum_add_distrib]

theorem spinPair_smul (n : Fin N) (u v : SpinIndex N → H) (k : Fin 3) (c : ℂ) :
    spinPair n u (c • v) k = c * spinPair n u v k := by
  simp only [spinPair, sigmaFamily_smul, Pi.smul_apply, inner_smul_right, Finset.mul_sum]

/-- Symmetry of a field on the finitely many spin components makes its
spin-matrix expectation real. No boundedness or everywhere-defined field
operator is required. -/
theorem spinPair_im_of_symmetric (n : Fin N) (u f : SpinIndex N → H)
    (h : ∀ s t, inner ℂ (f s) (u t) = inner ℂ (u s) (f t)) (k : Fin 3) :
    (spinPair n u f k).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  calc
    conj (spinPair n u f k) = ∑ s, inner ℂ (sigmaFamily n k f s) (u s) := by
      simp [spinPair, inner_conj_symm]
    _ = ∑ s, inner ℂ (f s) (sigmaFamily n k u s) := sigmaFamily_selfadjoint n k f u
    _ = spinPair n u f k := by
      apply Finset.sum_congr rfl
      intro s _
      fin_cases k <;> simp [inner_smul_right, h]

@[simp] theorem spinPair_self_im (n : Fin N) (u : SpinIndex N → H) (k : Fin 3) :
    (spinPair n u u k).im = 0 :=
  spinPair_im_of_symmetric n u u (fun _ _ => rfl) k

/-- The expression for a magnetization derivative when `g` is the
ordinary weak gradient. -/
def magnetizationDerivative (n : Fin N) (u : SpinIndex N → H)
    (g : Fin 3 → SpinIndex N → H) (b k : Fin 3) : ℝ :=
  2 * (spinPair n u (g b) k).re

def magnetizationCurl (n : Fin N) (u : SpinIndex N → H)
    (g : Fin 3 → SpinIndex N → H) : Fin 3 → ℝ :=
  ![magnetizationDerivative n u g 1 2 - magnetizationDerivative n u g 2 1,
    magnetizationDerivative n u g 2 0 - magnetizationDerivative n u g 0 2,
    magnetizationDerivative n u g 0 1 - magnetizationDerivative n u g 1 0]

def covariantDerivative (e : ℝ) (g f : Fin 3 → SpinIndex N → H) (a : Fin 3) :
    SpinIndex N → H := -Complex.I • g a + (-(e : ℂ)) • f a

def orbitalCurrent (u : SpinIndex N → H) (d : Fin 3 → SpinIndex N → H) (a : Fin 3) : ℝ :=
  (∑ s, inner ℂ (u s) (d a s)).re

theorem velocity_zero (n : Fin N) (d : Fin 3 → SpinIndex N → H) :
    velocity n 0 d = d 0 + Complex.I • sigmaFamily n 2 (d 1) +
      (-Complex.I) • sigmaFamily n 1 (d 2) := by
  simp only [velocity, contraction, Fin.sum_univ_three, sigmaFamily_add,
    sigmaFamily_square, sigma_zero_one, sigma_zero_two]

theorem velocity_one (n : Fin N) (d : Fin 3 → SpinIndex N → H) :
    velocity n 1 d = (-Complex.I) • sigmaFamily n 2 (d 0) + d 1 +
      Complex.I • sigmaFamily n 0 (d 2) := by
  simp only [velocity, contraction, Fin.sum_univ_three, sigmaFamily_add,
    sigmaFamily_square, sigma_one_zero, sigma_one_two]

theorem velocity_two (n : Fin N) (d : Fin 3 → SpinIndex N → H) :
    velocity n 2 d = Complex.I • sigmaFamily n 1 (d 0) +
      (-Complex.I) • sigmaFamily n 0 (d 1) + d 2 := by
  simp only [velocity, contraction, Fin.sum_univ_three, sigmaFamily_add,
    sigmaFamily_square, sigma_two_zero, sigma_two_one]

theorem current_zero (n : Fin N) (u : SpinIndex N → H) (d : Fin 3 → SpinIndex N → H) :
    current n u d 0 = orbitalCurrent u d 0 - (spinPair n u (d 1) 2).im +
      (spinPair n u (d 2) 1).im := by
  simp only [current, velocity_zero, Pi.add_apply, Pi.smul_apply, inner_add_right,
    inner_smul_right, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.neg_re, zero_mul, one_mul, neg_mul,
    Finset.sum_add_distrib, Finset.sum_neg_distrib, spinPair, orbitalCurrent,
    Complex.re_sum, Complex.im_sum, zero_sub]
  all_goals ring

theorem current_one (n : Fin N) (u : SpinIndex N → H) (d : Fin 3 → SpinIndex N → H) :
    current n u d 1 = orbitalCurrent u d 1 + (spinPair n u (d 0) 2).im -
      (spinPair n u (d 2) 0).im := by
  simp only [current, velocity_one, Pi.add_apply, Pi.smul_apply, inner_add_right,
    inner_smul_right, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.neg_re, zero_mul, one_mul, neg_mul,
    Finset.sum_add_distrib, Finset.sum_neg_distrib, spinPair, orbitalCurrent,
    Complex.re_sum, Complex.im_sum, zero_sub]
  all_goals ring

theorem current_two (n : Fin N) (u : SpinIndex N → H) (d : Fin 3 → SpinIndex N → H) :
    current n u d 2 = orbitalCurrent u d 2 - (spinPair n u (d 0) 1).im +
      (spinPair n u (d 1) 0).im := by
  simp only [current, velocity_two, Pi.add_apply, Pi.smul_apply, inner_add_right,
    inner_smul_right, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.neg_re, zero_mul, one_mul, neg_mul,
    Finset.sum_add_distrib, Finset.sum_neg_distrib, spinPair, orbitalCurrent,
    Complex.re_sum, Complex.im_sum, zero_sub]
  all_goals ring

theorem spinPair_covariant_im (n : Fin N) (u : SpinIndex N → H)
    (e : ℝ) (g f : Fin 3 → SpinIndex N → H) (a k : Fin 3)
    (hreal : (spinPair n u (f a) k).im = 0) :
    (spinPair n u (covariantDerivative e g f a) k).im =
      -(spinPair n u (g a) k).re := by
  rw [covariantDerivative, spinPair_add, spinPair_smul, spinPair_smul]
  simp [Complex.mul_im, hreal]

/-- The exact factor one half in the spin-summed Pauli combined current. -/
theorem current_correction (n : Fin N) (u : SpinIndex N → H) (e : ℝ)
    (g f : Fin 3 → SpinIndex N → H)
    (hreal : ∀ a k, (spinPair n u (f a) k).im = 0) (a : Fin 3) :
    current n u (covariantDerivative e g f) a =
      orbitalCurrent u (covariantDerivative e g f) a +
        (1 / 2 : ℝ) * magnetizationCurl n u g a := by
  fin_cases a <;>
    simp [current_zero, current_one, current_two, spinPair_covariant_im n u e g f _ _
      (hreal _ _), magnetizationCurl, magnetizationDerivative] <;> ring

end PfHk.PauliCurrentCorrection
