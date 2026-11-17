import PfHk.PolarInnerCalculus
import PfHk.CarlemanPolarMeasure

/-! Exact real source pairing under a unitary gauge and conformal polar
scaling. This identity has no physical operator premise. -/

noncomputable section
namespace PfHk.PolarCalculus

open scoped InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

theorem source_amplitude_eq (c t : ℝ) :
    2*Real.exp (-(c+2)*t) = 2*Real.exp (-c*t)*Real.exp (-t)^2 := by
  rw [mul_assoc]
  congr 1
  simp only [pow_two, ← Real.exp_add]
  congr 1
  ring

variable (I : Type*) [Fintype I] [DecidableEq I]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [NormedSpace ℂ H]

theorem conformal_source_pair (U : H ≃ₗᵢ[ℂ] H) (t : ℝ) (x y : H) :
    inner ℝ (Real.exp (-conformalExponent I*t) • U x)
      ((2*Real.exp (-(conformalExponent I+2)*t)) • U y) =
      2*logarithmicJacobian I t*inner ℝ x y := by
  rw [source_amplitude_eq, real_inner_smul_left, real_inner_smul_right,
    complexIsometry_real_inner, logarithmicJacobian_eq_conformal]
  ring

end PfHk.PolarCalculus
