import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! The explicitly normalized hydrogen orbital and its exponential density
moments. All integrals use the actual Euclidean volume measure. -/

noncomputable section
namespace PfHk.HydrogenOrbital

open MeasureTheory Filter Set Real
open scoped ENNReal InnerProductSpace

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000

abbrev Space := EuclideanSpace ℝ (Fin 3)

def orbital (Z : ℝ) (x : Space) : ℝ :=
  Real.sqrt (Z ^ 3 / Real.pi) * Real.exp (-Z * ‖x‖)

def density (Z : ℝ) (x : Space) : ℝ :=
  (Z ^ 3 / Real.pi) * Real.exp (-2 * Z * ‖x‖)

theorem continuous_orbital (Z : ℝ) : Continuous (orbital Z) := by
  unfold orbital
  fun_prop

theorem continuous_density (Z : ℝ) : Continuous (density Z) := by
  unfold density
  fun_prop

theorem orbital_pos {Z : ℝ} (hZ : 0 < Z) (x : Space) : 0 < orbital Z x := by
  unfold orbital
  positivity

theorem density_pos {Z : ℝ} (hZ : 0 < Z) (x : Space) : 0 < density Z x := by
  unfold density
  positivity

theorem orbital_sq {Z : ℝ} (hZ : 0 ≤ Z) (x : Space) :
    orbital Z x ^ 2 = density Z x := by
  rw [orbital, mul_pow, Real.sq_sqrt (by positivity), ← Real.exp_nat_mul]
  congr 1
  congr 1
  ring

/-- Radial exponential decay is integrable in the actual three-dimensional
Euclidean space. -/
theorem integrable_exp_norm {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : Space => Real.exp (-c * ‖x‖)) volume := by
  apply (integrable_fun_norm_addHaar (volume : Measure Space)
    (f := fun r : ℝ => Real.exp (-c * r))).2
  simpa only [finrank_euclideanSpace_fin, Nat.reduceSub,
    smul_eq_mul, Real.rpow_two, Real.rpow_one] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := (2 : ℝ)) (p := (1 : ℝ)) (by norm_num) (by norm_num) hc)

/-- The exact radial integral needed for hydrogen normalization. -/
theorem integral_exp_norm {c : ℝ} (hc : 0 < c) :
    (∫ x : Space, Real.exp (-c * ‖x‖)) = 8 * Real.pi / c ^ 3 := by
  rw [integral_fun_norm_addHaar (volume : Measure Space) (fun r => Real.exp (-c * r))]
  have hrad : (∫ r : ℝ in Ioi 0, r ^ 2 * Real.exp (-c * r)) = 2 / c ^ 3 := by
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 3) (by norm_num) hc
    norm_num [Real.rpow_natCast, Real.Gamma_nat_eq_factorial] at h
    convert h using 1
    · apply setIntegral_congr_fun measurableSet_Ioi
      intro r _
      dsimp only
      rw [neg_mul]
    · ring
  have hvol : (volume : Measure Space).real (Metric.ball 0 1) = Real.pi * 4 / 3 := by
    simp only [Measure.real, EuclideanSpace.volume_ball_fin_three, ENNReal.ofReal_one,
      one_pow, one_mul]
    exact ENNReal.toReal_ofReal (by positivity)
  simp only [finrank_euclideanSpace_fin, Nat.reduceSub, smul_eq_mul, nsmul_eq_mul]
  rw [hrad, hvol]
  ring

theorem density_integrable {Z : ℝ} (hZ : 0 < Z) :
    Integrable (density Z) volume := by
  unfold density
  simpa only [neg_mul, mul_assoc] using
    (integrable_exp_norm (c := 2 * Z) (by positivity)).const_mul (Z ^ 3 / Real.pi)

theorem integral_density {Z : ℝ} (hZ : 0 < Z) :
    (∫ x, density Z x) = 1 := by
  unfold density
  rw [integral_const_mul]
  have heq : (fun x : Space => Real.exp (-2 * Z * ‖x‖)) =
      (fun x => Real.exp (-(2 * Z) * ‖x‖)) := by
    funext x
    congr 1
    ring
  rw [heq, integral_exp_norm (by positivity)]
  field_simp
  ring

theorem orbital_memLp {Z : ℝ} (hZ : 0 < Z) : MemLp (orbital Z) 2 volume := by
  apply (memLp_two_iff_integrable_sq (continuous_orbital Z).aestronglyMeasurable).2
  simpa only [orbital_sq hZ.le] using density_integrable hZ

theorem integral_orbital_sq {Z : ℝ} (hZ : 0 < Z) :
    (∫ x, orbital Z x ^ 2) = 1 := by
  simpa only [orbital_sq hZ.le] using integral_density hZ

theorem integrable_exp_norm_div_norm {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : Space => Real.exp (-c * ‖x‖) / ‖x‖) volume := by
  apply (integrable_fun_norm_addHaar (volume : Measure Space)
    (f := fun r : ℝ => Real.exp (-c * r) / r)).2
  have hi := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := (1 : ℝ)) (p := (1 : ℝ)) (by norm_num) (by norm_num) hc
  apply hi.congr_fun _ measurableSet_Ioi
  intro r hr
  simp only [finrank_euclideanSpace_fin, Nat.reduceSub, smul_eq_mul, Real.rpow_one]
  field_simp

theorem integral_exp_norm_div_norm {c : ℝ} (hc : 0 < c) :
    (∫ x : Space, Real.exp (-c * ‖x‖) / ‖x‖) = 4 * Real.pi / c ^ 2 := by
  rw [integral_fun_norm_addHaar (volume : Measure Space)
    (fun r => Real.exp (-c * r) / r)]
  have hrad : (∫ r : ℝ in Ioi 0, r ^ 2 * (Real.exp (-c * r) / r)) = 1 / c ^ 2 := by
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (by norm_num) hc
    norm_num [Real.rpow_natCast, Real.Gamma_nat_eq_factorial] at h
    convert h using 1
    · apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      have he : -c * r = -(c * r) := by ring
      rw [he]
      field_simp
    · ring
  have hvol : (volume : Measure Space).real (Metric.ball 0 1) = Real.pi * 4 / 3 := by
    simp only [Measure.real, EuclideanSpace.volume_ball_fin_three, ENNReal.ofReal_one,
      one_pow, one_mul]
    exact ENNReal.toReal_ofReal (by positivity)
  simp only [finrank_euclideanSpace_fin, Nat.reduceSub, smul_eq_mul, nsmul_eq_mul]
  rw [hrad, hvol]
  ring

theorem density_div_norm_integrable {Z : ℝ} (hZ : 0 < Z) :
    Integrable (fun x => density Z x / ‖x‖) volume := by
  have hi := (integrable_exp_norm_div_norm (c := 2 * Z) (by positivity)).const_mul
    (Z ^ 3 / Real.pi)
  apply hi.congr
  exact ae_of_all _ fun x => by
    dsimp only
    unfold density
    have he : -(2 * Z) * ‖x‖ = -2 * Z * ‖x‖ := by ring
    rw [he]
    ring

/-- The Coulomb expectation in the normalized hydrogen orbital. -/
theorem integral_density_div_norm {Z : ℝ} (hZ : 0 < Z) :
    (∫ x, density Z x / ‖x‖) = Z := by
  have heq : (fun x : Space => density Z x / ‖x‖) =
      fun x => (Z ^ 3 / Real.pi) * (Real.exp (-(2 * Z) * ‖x‖) / ‖x‖) := by
    funext x
    unfold density
    have he : -(2 * Z) * ‖x‖ = -2 * Z * ‖x‖ := by ring
    rw [he]
    ring
  rw [heq, integral_const_mul, integral_exp_norm_div_norm (by positivity)]
  field_simp
  ring

/-- Every exponent below twice the Coulomb charge is a density moment. -/
theorem exponential_moment {Z α : ℝ} (_hZ : 0 < Z) (hα : α < 2 * Z) :
    Integrable (fun x => Real.exp (α * ‖x‖) * density Z x) volume := by
  have hi := (integrable_exp_norm (c := 2 * Z - α) (by linarith)).const_mul
    (Z ^ 3 / Real.pi)
  apply hi.congr
  exact ae_of_all _ fun x => by
    dsimp only
    unfold density
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring

end PfHk.HydrogenOrbital
