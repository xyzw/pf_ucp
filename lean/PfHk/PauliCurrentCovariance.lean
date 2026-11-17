import PfHk.PauliCurrentCorrection

/-! Gauge and photon-isometry covariance of the actual Pauli kinetic
square and current. These are pointwise Hilbert-space identities, so they
also apply to position-dependent unit phases and to the photon Weyl map. -/

noncomputable section
namespace PfHk.PauliCurrentAlgebra

open PauliSpin PauliCurrentCorrection
open scoped BigOperators

variable {N : ℕ} {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- Multiplication by a scalar unit phase on the non-spin Hilbert fiber. -/
def scalarIsometry (c : ℂ) (hc : ‖c‖ = 1) : H →ₗᵢ[ℂ] H where
  toFun u := c • u
  map_add' u v := smul_add c u v
  map_smul' z u := by simp [smul_smul, mul_comm]
  norm_map' u := by
    change ‖c • u‖ = ‖u‖
    rw [norm_smul, hc, one_mul]

theorem contraction_map (n : Fin N) (L : H →ₗ[ℂ] K)
    (d : Fin 3 → SpinIndex N → H) :
    contraction n (fun a s => L (d a s)) = fun s => L (contraction n d s) := by
  funext s
  simp [contraction, sigmaFamily_map, map_sum]

theorem velocity_map (n : Fin N) (a : Fin 3) (L : H →ₗ[ℂ] K)
    (d : Fin 3 → SpinIndex N → H) :
    velocity n a (fun b s => L (d b s)) = fun s => L (velocity n a d s) := by
  simp only [velocity, contraction_map, sigmaFamily_map]

theorem density_isometry (L : H →ₗᵢ[ℂ] K) (u : SpinIndex N → H) :
    density (fun s => L (u s)) = density u := by
  simp only [density, L.norm_map]

theorem current_isometry (n : Fin N) (L : H →ₗᵢ[ℂ] K)
    (u : SpinIndex N → H) (d : Fin 3 → SpinIndex N → H) (a : Fin 3) :
    current n (fun s => L (u s)) (fun b s => L (d b s)) a = current n u d a := by
  have hv := velocity_map n a L.toLinearMap d
  change velocity n a (fun b s => L (d b s)) = fun s => L (velocity n a d s) at hv
  simp only [current, hv, L.inner_map_map]

theorem kinetic_isometry (n : Fin N) (L : H →ₗᵢ[ℂ] K)
    (d : Fin 3 → SpinIndex N → H) :
    kinetic n (fun a s => L (d a s)) = kinetic n d := by
  have hd := contraction_map n L.toLinearMap d
  change contraction n (fun a s => L (d a s)) = fun s => L (contraction n d s) at hd
  simp only [kinetic, hd, L.norm_map]

theorem current_add (n : Fin N) (u : SpinIndex N → H)
    (d f : Fin 3 → SpinIndex N → H) (a : Fin 3) :
    current n u (d + f) a = current n u d a + current n u f a := by
  simp only [current, velocity, contraction_add, sigmaFamily_add, Pi.add_apply,
    inner_add_right, Complex.add_re, Finset.sum_add_distrib]

theorem current_vector (n : Fin N) (u : SpinIndex N → H) (b : Fin 3 → ℝ) (a : Fin 3) :
    current n u (fun μ => (b μ : ℂ) • u) a = b a * density u := by
  have ho (a : Fin 3) : orbitalCurrent u (fun μ => (b μ : ℂ) • u) a = b a * density u := by
    simp only [orbitalCurrent, Pi.smul_apply, inner_smul_right, Complex.re_sum,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    simp only [← inner_self_eq_norm_sq (𝕜 := ℂ), RCLike.re_to_complex, density, Finset.mul_sum]
  have hs (a k : Fin 3) : (spinPair n u ((b a : ℂ) • u) k).im = 0 := by
    rw [spinPair_smul]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      spinPair_self_im, mul_zero, zero_mul, add_zero]
  fin_cases a
  · change current n u (fun μ => (b μ : ℂ) • u) 0 = b 0 * density u
    rw [current_zero, ho, hs, hs]
    ring
  · change current n u (fun μ => (b μ : ℂ) • u) 1 = b 1 * density u
    rw [current_one, ho, hs, hs]
    ring
  · change current n u (fun μ => (b μ : ℂ) • u) 2 = b 2 * density u
    rw [current_two, ho, hs, hs]
    ring

/-- The state-dependent current acquires exactly density times the
external derivative shift. The magnetization contribution is unchanged. -/
theorem current_shift (n : Fin N) (u : SpinIndex N → H)
    (d : Fin 3 → SpinIndex N → H) (b : Fin 3 → ℝ) (a : Fin 3) :
    current n u (fun μ => d μ + (b μ : ℂ) • u) a =
      current n u d a + b a * density u := by
  exact (current_add n u d (fun μ => (b μ : ℂ) • u) a).trans
    (congrArg (current n u d a + ·) (current_vector n u b a))

theorem current_isometry_shift (n : Fin N) (L : H →ₗᵢ[ℂ] K)
    (u : SpinIndex N → H) (d : Fin 3 → SpinIndex N → H)
    (b : Fin 3 → ℝ) (a : Fin 3) :
    current n (fun s => L (u s)) (fun μ s => L (d μ s + (b μ : ℂ) • u s)) a =
      current n u d a + b a * density u := by
  exact (current_isometry n L u (fun μ => d μ + (b μ : ℂ) • u) a).trans
    (current_shift n u d b a)

theorem kinetic_isometry_shift (n : Fin N) (L : H →ₗᵢ[ℂ] K)
    (u : SpinIndex N → H) (d : Fin 3 → SpinIndex N → H) (b : Fin 3 → ℝ) :
    kinetic n (fun μ s => L (d μ s + (b μ : ℂ) • u s)) =
      kinetic n d + ∑ a, b a * current n u d a +
        (1 / 2 : ℝ) * (∑ a, b a ^ 2) * density u := by
  exact (kinetic_isometry n L (fun μ => d μ + (b μ : ℂ) • u)).trans
    (kinetic_shift n u d b)

end PfHk.PauliCurrentAlgebra
