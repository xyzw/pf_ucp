import PfHk.CylinderPhysicalDensity

/-! Exact exponential scaling of the recovered cylinder energy and
source. All identities here are ordinary Hilbert-space algebra. -/

noncomputable section
namespace PfHk.CylinderConjugation

open CylinderIdentity
open scoped InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def recoveredDensity (τ c : ℝ) (p b r : ℝ → ℝ) (z dz k q : ℝ → H) (t : ℝ) : ℝ :=
  τ^3 * b t * ‖z t‖^2 + τ*b t *
    (‖-dz t + (τ*p t-c) • z t‖^2 + inner ℝ (z t) (k t)) +
    τ*r t * inner ℝ (z t) (q t)

def originalDensity (τ c : ℝ) (b r : ℝ → ℝ) (w dw k q : ℝ → H) (t : ℝ) : ℝ :=
  τ^3*b t*‖w t‖^2 + τ*b t*(‖dw t+c • w t‖^2 + inner ℝ (w t) (k t)) +
    τ*r t*inner ℝ (w t) (q t)

theorem exp_square (τ t : ℝ) (f : ℝ → ℝ) :
    Real.exp (τ*f t)^2 = Real.exp (2*τ*f t) := by
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

theorem weighted_radial (τ c t : ℝ) (f p : ℝ → ℝ) (w dw : ℝ → H) :
    -weightedFirst τ f p w dw t + (τ*p t-c) • weighted τ f w t =
      -(Real.exp (τ*f t) • (dw t+c • w t)) := by
  unfold weightedFirst weighted
  module

theorem weighted_inner (τ t : ℝ) (f : ℝ → ℝ) (w v : ℝ → H) :
    inner ℝ (weighted τ f w t) (weighted τ f v t) =
      Real.exp (2*τ*f t) * inner ℝ (w t) (v t) := by
  unfold weighted
  rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, ← pow_two, exp_square]

theorem recoveredDensity_weighted (τ c t : ℝ) (f p b r : ℝ → ℝ)
    (w dw k q : ℝ → H) :
    recoveredDensity τ c p b r (weighted τ f w) (weightedFirst τ f p w dw)
      (weighted τ f k) (weighted τ f q) t =
      Real.exp (2*τ*f t) * originalDensity τ c b r w dw k q t := by
  unfold recoveredDensity originalDensity
  rw [weighted_norm_sq, weighted_radial, norm_neg, norm_smul,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow, exp_square,
    weighted_inner, weighted_inner]
  ring

theorem operator_conjugation_of_values (τ c t : ℝ) (f p b r : ℝ → ℝ)
    (w dw ddw k q z dz ddz kz qz : ℝ → H)
    (hz : z t = weighted τ f w t) (hdz : dz t = weightedFirst τ f p w dw t)
    (hddz : ddz t = weightedSecond τ f p b w dw ddw t)
    (hk : kz t = weighted τ f k t) (hq : qz t = weighted τ f q t) :
    symmetricPart τ c p r z ddz kz qz t + skewPart τ p b z dz t =
      Real.exp (τ*f t) • (-ddw t+k t+c^2 • w t+r t • q t) := by
  unfold symmetricPart skewPart
  rw [hz, hdz, hddz, hk, hq]
  exact operator_conjugation τ c t f p b r w dw ddw k q

theorem recoveredDensity_of_values (τ c t : ℝ) (f p b r : ℝ → ℝ)
    (w dw k q z dz kz qz : ℝ → H)
    (hz : z t = weighted τ f w t) (hdz : dz t = weightedFirst τ f p w dw t)
    (hk : kz t = weighted τ f k t) (hq : qz t = weighted τ f q t) :
    recoveredDensity τ c p b r z dz kz qz t =
      Real.exp (2*τ*f t) * originalDensity τ c b r w dw k q t := by
  unfold recoveredDensity
  rw [hz, hdz, hk, hq]
  exact recoveredDensity_weighted τ c t f p b r w dw k q

theorem source_norm_sq_of_values (τ c t : ℝ) (f p b r : ℝ → ℝ)
    (w dw ddw k q z dz ddz kz qz : ℝ → H)
    (hz : z t = weighted τ f w t) (hdz : dz t = weightedFirst τ f p w dw t)
    (hddz : ddz t = weightedSecond τ f p b w dw ddw t)
    (hk : kz t = weighted τ f k t) (hq : qz t = weighted τ f q t) :
    ‖symmetricPart τ c p r z ddz kz qz t + skewPart τ p b z dz t‖^2 =
      Real.exp (2*τ*f t) * ‖-ddw t+k t+c^2 • w t+r t • q t‖^2 := by
  rw [operator_conjugation_of_values τ c t f p b r w dw ddw k q z dz ddz kz qz hz hdz hddz hk hq,
    norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow, exp_square]

end PfHk.CylinderConjugation
