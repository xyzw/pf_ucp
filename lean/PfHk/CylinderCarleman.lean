import PfHk.CylinderIdentity
import PfHk.CarlemanWeights

/-!
A Carleman coercivity estimate for a moving nonnegative pair of quadratic
forms on an actual Hilbert-valued cylinder curve. The commutator and the
angular multiplier identities are obtained by differentiation in
`CylinderIdentity`. The present estimate combines them before integration.
Its hypotheses record the coefficient bounds that must be checked for the
physical radial gauge. It is not a theorem asserting those physical bounds.
-/

noncomputable section
namespace PfHk.CylinderCarleman

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open MeasureTheory Filter Set
open scoped InnerProductSpace Topology
open CylinderIdentity

/-- Young's inequality in the form needed for quadratic-form derivatives. -/
theorem abs_le_sum_of_sq_le {x a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : x ^ 2 ≤ 4 * a * b) : |x| ≤ a + b := by
  nlinarith [sq_abs x, sq_nonneg (a - b), abs_nonneg x]

/-- A small curvature coefficient gives the three separate angular errors.
Here `r` is the square of the physical radius. -/
theorem angular_error_bound {C r b τ K T M v : ℝ}
    (hr : 0 ≤ r) (hb : 0 ≤ b) (hτ : 1 ≤ τ)
    (hK : 0 ≤ K) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (hrb : r ≤ b) (hsmall : 64 * C ^ 2 * r ≤ b)
    (hderivative : v ^ 2 ≤ C ^ 2 * r ^ 2 * K * (T + M)) :
    |v| ≤ b / 16 * K + r / 16 * T + τ ^ 2 * b / 16 * M := by
  have hτsq : 1 ≤ τ ^ 2 := by nlinarith
  have h₁ : C ^ 2 * r ^ 2 ≤ b * r / 64 := by
    nlinarith [mul_le_mul_of_nonneg_right hsmall hr]
  have h₂ : C ^ 2 * r ^ 2 ≤ τ ^ 2 * b ^ 2 / 64 := by
    have hbr := mul_le_mul_of_nonneg_left hrb hb
    have hτb := mul_le_mul_of_nonneg_right hτsq (sq_nonneg b)
    nlinarith
  have h₃ := mul_le_mul_of_nonneg_right h₁ (mul_nonneg hK hT)
  have h₄ := mul_le_mul_of_nonneg_right h₂ (mul_nonneg hK hM)
  have h := abs_le_sum_of_sq_le
    (x := v) (a := b / 16 * K) (b := r / 16 * T + τ ^ 2 * b / 16 * M)
    (by positivity) (by positivity) (by nlinarith)
  linarith

/-- The radiation derivative has one more factor of physical radius. -/
theorem radiation_error_bound {C r b τ T M v : ℝ}
    (hr : 0 ≤ r) (hr₁ : r ≤ 1) (hb : 0 ≤ b) (hτ : 1 ≤ τ)
    (hT : 0 ≤ T) (hM : 0 ≤ M) (hsmall : 64 * C ^ 2 * r ≤ b)
    (hderivative : v ^ 2 ≤ C ^ 2 * r * T * M) :
    r * |v| ≤ r / 8 * T + τ ^ 2 * b / 16 * M := by
  have hτsq : 1 ≤ τ ^ 2 := by nlinarith
  have hCr : 0 ≤ C ^ 2 * r := mul_nonneg (sq_nonneg C) hr
  have h₁ : C ^ 2 * r ^ 2 ≤ τ ^ 2 * b / 32 := by
    have hh := mul_le_mul_of_nonneg_left hr₁ hCr
    have hh₂ := mul_le_mul_of_nonneg_right hτsq hb
    nlinarith
  have h₂ := mul_le_mul_of_nonneg_right h₁ (mul_nonneg hr (mul_nonneg hT hM))
  have h₃ := mul_le_mul_of_nonneg_left hderivative (sq_nonneg r)
  have h := abs_le_sum_of_sq_le
    (a := r / 8 * T) (b := τ ^ 2 * b / 16 * M)
    (by positivity) (by positivity) (x := r * v) (by nlinarith)
  simpa only [abs_mul, abs_of_nonneg hr] using h

/-- Combining the commutator with half the weighted multiplier identity
retains angular energy directly. All quantities here are pointwise. -/
theorem scalar_coercivity {τ c p b ddb r S B D M K T v w pair : ℝ}
    (hτ : 1 ≤ τ) (hb : 0 ≤ b) (hp : 3 / 4 ≤ p) (hp₁ : p ≤ 1)
    (hr : 0 ≤ r) (hS : 0 ≤ S) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (hK : 0 ≤ K) (hT : 0 ≤ T)
    (hf : |ddb| ≤ τ ^ 2 * b / 8)
    (hv : |v| ≤ b / 16 * K + r / 16 * T + τ ^ 2 * b / 16 * M)
    (hw : r * |w| ≤ r / 8 * T + τ ^ 2 * b / 16 * M)
    (hpair : τ / 2 * pair ≤ S / 4 + τ ^ 3 * b * M / 4) :
    S / 2 + B + τ * b * D + τ ^ 3 * b * M + τ * b * K / 4 + τ * r * T ≤
      S + B + (4 * τ * b * D + 4 * τ ^ 3 * p ^ 2 * b * M -
        τ * ddb * M - 2 * τ * p * v + 4 * τ * p * r * T -
        2 * τ * p * r * w) +
      τ / 2 * (b * (D + K + r * T + c ^ 2 * M) -
        τ ^ 2 * p ^ 2 * b * M - ddb / 2 * M - pair) := by
  have hτ₀ : 0 ≤ τ := by linarith
  have hp₀ : 0 ≤ p := by linarith
  have hmass : 0 ≤ τ ^ 3 * b * M := by positivity
  have hradial : 0 ≤ τ * b * D := by positivity
  have hang : 0 ≤ τ * b * K := by positivity
  have hrad : 0 ≤ τ * r * T := by positivity
  have hextra : 0 ≤ τ * b * (r * T + c ^ 2 * M) := by positivity
  have hp₂lo : 9 / 16 ≤ p ^ 2 := by nlinarith
  have hp₂hi : p ^ 2 ≤ 1 := by nlinarith
  have hmasslo := mul_le_mul_of_nonneg_right hp₂lo hmass
  have hmasshi := mul_le_mul_of_nonneg_right hp₂hi hmass
  have hradlo := mul_le_mul_of_nonneg_right hp hrad
  have hf' := mul_le_mul_of_nonneg_right ((le_abs_self ddb).trans hf)
    (mul_nonneg hτ₀ hM)
  have hv₀ : 0 ≤ b / 16 * K + r / 16 * T + τ ^ 2 * b / 16 * M := by positivity
  have hv' : p * v ≤ b / 16 * K + r / 16 * T + τ ^ 2 * b / 16 * M :=
    (mul_le_mul_of_nonneg_left ((le_abs_self v).trans hv) hp₀).trans
      (by nlinarith [mul_le_mul_of_nonneg_right hp₁ hv₀])
  have hv'' := mul_le_mul_of_nonneg_left hv' hτ₀
  have hw₀ : 0 ≤ r / 8 * T + τ ^ 2 * b / 16 * M := by positivity
  have hw' : p * (r * w) ≤ r / 8 * T + τ ^ 2 * b / 16 * M := by
    have hwa := mul_le_mul_of_nonneg_left (le_abs_self w) hr
    have hwb := mul_le_mul_of_nonneg_left (hwa.trans hw) hp₀
    have hwc := mul_le_mul_of_nonneg_right hp₁ hw₀
    nlinarith
  have hw'' := mul_le_mul_of_nonneg_left hw' hτ₀
  nlinarith

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The multiplier pairing is bounded by a square, without an integrated
Cauchy--Schwarz premise. -/
theorem multiplier_pair_bound (S z : H) {τ b : ℝ}
    (hτ : 1 ≤ τ) (hb : 0 ≤ b) (hb₁ : b ≤ 1) :
    τ / 2 * inner ℝ S (b • z) ≤ ‖S‖ ^ 2 / 4 + τ ^ 3 * b * ‖z‖ ^ 2 / 4 := by
  have hnorm : 0 ≤ ‖S - (τ * b) • z‖ ^ 2 := sq_nonneg _
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_right] at hnorm
  have hτ₀ : 0 ≤ τ := by linarith
  have hcoef : τ ^ 2 * b ^ 2 ≤ τ ^ 3 * b := by
    have h₁ : b ^ 2 ≤ b := by nlinarith [mul_le_mul_of_nonneg_left hb₁ hb]
    have h₂ : b ≤ τ * b := by nlinarith
    have h₃ := mul_le_mul_of_nonneg_left (h₁.trans h₂) (sq_nonneg τ)
    nlinarith
  have hh := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖z‖)
  rw [real_inner_smul_right]
  nlinarith

/-- Pointwise Hilbert-valued coercivity. The added flux derivative has
zero integral for the compactly supported cylinder vectors. -/
theorem pointwise_coercivity (τ c : ℝ)
    {p b ddb r kv qv : ℝ → ℝ} {z dz ddz k q : ℝ → H} {t : ℝ}
    (hτ : 1 ≤ τ) (hb : 0 ≤ b t) (hb₁ : b t ≤ 1)
    (hp : 3 / 4 ≤ p t) (hp₁ : p t ≤ 1) (hr : 0 ≤ r t)
    (hK : 0 ≤ inner ℝ (z t) (k t)) (hT : 0 ≤ inner ℝ (z t) (q t))
    (hf : |ddb t| ≤ τ ^ 2 * b t / 8)
    (hkv : |kv t| ≤ b t / 16 * inner ℝ (z t) (k t) +
      r t / 16 * inner ℝ (z t) (q t) + τ ^ 2 * b t / 16 * ‖z t‖ ^ 2)
    (hqv : r t * |qv t| ≤ r t / 8 * inner ℝ (z t) (q t) +
      τ ^ 2 * b t / 16 * ‖z t‖ ^ 2) :
    ‖symmetricPart τ c p r z ddz k q t‖ ^ 2 / 2 +
      ‖skewPart τ p b z dz t‖ ^ 2 + τ * b t * ‖dz t‖ ^ 2 +
      τ ^ 3 * b t * ‖z t‖ ^ 2 + τ * b t * inner ℝ (z t) (k t) / 4 +
      τ * r t * inner ℝ (z t) (q t) ≤
    ‖symmetricPart τ c p r z ddz k q t‖ ^ 2 + ‖skewPart τ p b z dz t‖ ^ 2 +
      commutatorDensity τ p b ddb r kv qv z dz q t +
      τ / 2 * (multiplierDensity τ c p b ddb r z dz k q t -
        inner ℝ (symmetricPart τ c p r z ddz k q t) (b t • z t)) := by
  have h := scalar_coercivity (c := c) (B := ‖skewPart τ p b z dz t‖ ^ 2) hτ hb hp hp₁ hr
    (sq_nonneg ‖symmetricPart τ c p r z ddz k q t‖) (sq_nonneg ‖dz t‖)
    (sq_nonneg ‖z t‖) hK hT hf hkv hqv
    (multiplier_pair_bound (symmetricPart τ c p r z ddz k q t) (z t) hτ hb hb₁)
  simpa only [commutatorDensity, multiplierDensity, real_inner_self_eq_norm_sq] using h

end PfHk.CylinderCarleman
