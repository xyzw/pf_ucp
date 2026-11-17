import PfHk.CylinderEstimate
import PfHk.CylinderConjugation

/-! Recovery of the mass, physical radial/angular kinetic energy and
radiation terms from the retained cylinder coercivity. -/

noncomputable section
namespace PfHk.CylinderEstimate

open CylinderIdentity
open scoped InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem physical_density_le_retained (τ c t : ℝ) (p b r : ℝ → ℝ)
    (z dz ddz k q : ℝ → H) (hτ : 0 ≤ τ) (hb : 0 ≤ b t) (hr : 0 ≤ r t)
    (hp : |p t| ≤ 1) (hc : |c| ≤ τ)
    (hK : 0 ≤ inner ℝ (z t) (k t)) (hT : 0 ≤ inner ℝ (z t) (q t)) :
    τ^3 * b t * ‖z t‖^2 + τ * b t *
      (‖-dz t + (τ*p t-c) • z t‖^2 + inner ℝ (z t) (k t)) +
      τ * r t * inner ℝ (z t) (q t) ≤
    16 * retained τ c p b r z dz ddz k q t := by
  have hrad := mul_le_mul_of_nonneg_left
    (CylinderConjugation.radial_norm_sq_le (z t) (dz t) hτ hp hc) (mul_nonneg hτ hb)
  have hD := mul_nonneg (mul_nonneg hτ hb) (sq_nonneg ‖dz t‖)
  have hM := mul_nonneg (mul_nonneg (pow_nonneg hτ 3) hb) (sq_nonneg ‖z t‖)
  have hKK := mul_nonneg (mul_nonneg hτ hb) hK
  have hTT := mul_nonneg (mul_nonneg hτ hr) hT
  unfold retained
  nlinarith only [hrad, hD, hM, hKK, hTT,
    sq_nonneg ‖symmetricPart τ c p r z ddz k q t‖,
    sq_nonneg ‖skewPart τ p b z dz t‖]

end PfHk.CylinderEstimate
