import PfHk.DyadicScalarNorm
import PfHk.MultiplierNormAlgebra

noncomputable section
namespace PfHk.PhysicalDyadicProductRule

open MeasureTheory GptLean GptLean.ElectronicH1Multiplier GptLean.ElectronicH1Space
  PfHk.PhysicalCutoffCommutator

set_option Elab.async false
set_option maxHeartbeats 20000

section Norm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem product_rule_norm_sq (v Dv va Dva : H) {a d η k : ℝ}
    (ha : 0 < a) (hη : |η| ≤ 1) (_hk : 0 ≤ k) (hd : |d| ≤ k * a)
    (hv : va = a • v) (hD : Dva = a • Dv + (-Complex.I) • (d • v)) :
    ‖η • (a • Dv)‖ ^ 2 ≤ 2 * ‖Dva‖ ^ 2 + (2 * k ^ 2) * ‖va‖ ^ 2 := by
  have hn : ‖a • Dv‖ ≤ ‖Dva‖ + k * ‖va‖ := by
    have heq : a • Dv = Dva - (-Complex.I) • (d • v) := by rw [hD]; abel
    calc
      _ = ‖Dva - (-Complex.I) • (d • v)‖ := congrArg norm heq
      _ ≤ ‖Dva‖ + ‖(-Complex.I) • (d • v)‖ := norm_sub_le _ _
      _ = ‖Dva‖ + |d| * ‖v‖ := by simp only [norm_smul, norm_neg, Complex.norm_I, one_mul, Real.norm_eq_abs]
      _ ≤ ‖Dva‖ + (k * a) * ‖v‖ := add_le_add le_rfl (mul_le_mul_of_nonneg_right hd (norm_nonneg v))
      _ = ‖Dva‖ + k * ‖va‖ := by rw [hv, norm_smul, Real.norm_eq_abs, abs_of_pos ha]; ring
  have hnη : ‖η • (a • Dv)‖ ≤ ‖Dva‖ + k * ‖va‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_of_le_one_left (norm_nonneg _) hη).trans hn
  have hs := pow_le_pow_left₀ (norm_nonneg _) hnη 2
  nlinarith [sq_nonneg (‖Dva‖ - k * ‖va‖)]

end Norm

variable {I H : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem multiplier_value_ae (a : DifferentiableMultiplier I) (ψ z : L2 H I)
    (hz : z = a.multiplier ψ) :
    (z : EuclideanSpace ℝ I → H) =ᵐ[volume] fun x => a.weight x • ψ x := by
  rw [hz]
  exact scalar_multiplier_ae a ψ

theorem multiplier_derivative_ae (a : DifferentiableMultiplier I) (i : I)
    (ψ D Dz : L2 H I)
    (hD : Dz = a.multiplier D + (-Complex.I) • a.derivativeMultiplier i ψ) :
    (Dz : EuclideanSpace ℝ I → H) =ᵐ[volume]
      fun x => a.weight x • D x + (-Complex.I) • (a.gradient i x • ψ x) := by
  filter_upwards [Lp.coeFn_add (a.multiplier D) ((-Complex.I) • a.derivativeMultiplier i ψ),
    Lp.coeFn_smul (-Complex.I) (a.derivativeMultiplier i ψ), scalar_multiplier_ae a D,
    PhotonLocalization.realL2Multiplier_apply (a.gradient i) (a.gradient_measurable i).aestronglyMeasurable
      a.derivativeBound (ae_of_all _ (a.derivative_bounded i)) ψ] with x hadd hsmul hmul hder
  change a.derivativeMultiplier i ψ x = a.gradient i x • ψ x at hder
  rw [hD, hadd, Pi.add_apply, hsmul, Pi.smul_apply, hmul, hder]

theorem product_localization_bound (a η w : DifferentiableMultiplier I) (i : I)
    (ψ D z Dz g gh gl : L2 H I) (b : EuclideanSpace ℝ I → ℝ) {k : ℝ}
    (hk : 0 ≤ k) (hz : z = a.multiplier ψ)
    (hD : Dz = a.multiplier D + (-Complex.I) • a.derivativeMultiplier i ψ)
    (hw : ∀ x, w.weight x = η.weight x * a.weight x)
    (hη : ∀ x, |η.weight x| ≤ 1)
    (ha : ∀ x, η.weight x ≠ 0 → 0 < a.weight x)
    (hd : ∀ x, η.weight x ≠ 0 → |a.gradient i x| ≤ k * a.weight x)
    (hg : (g : EuclideanSpace ℝ I → H) =ᵐ[volume] fun x => b x • D x)
    (hh : (gh : EuclideanSpace ℝ I → H) =ᵐ[volume] fun x => b x • Dz x)
    (hl : (gl : EuclideanSpace ℝ I → H) =ᵐ[volume] fun x => b x • z x) :
    ‖w.multiplier g‖ ^ 2 ≤ 2 * ‖gh‖ ^ 2 + (2 * k ^ 2) * ‖gl‖ ^ 2 := by
  apply PfHk.MultiplierNormAlgebra.l2_square_bound volume _ _ _ 2 (2 * k ^ 2)
  filter_upwards [scalar_multiplier_ae w g, hg, hh, hl,
    multiplier_derivative_ae a i ψ D Dz hD, multiplier_value_ae a ψ z hz]
    with x hloc hgx hhx hlx hDx hzx
  rw [hloc, hgx, hhx, hlx, hw x, mul_smul]
  by_cases hzero : η.weight x = 0
  · rw [hzero, zero_smul, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    positivity
  · apply product_rule_norm_sq (b x • ψ x) (b x • D x) (b x • z x) (b x • Dz x)
      (ha x hzero) (hη x) hk (hd x hzero)
    · rw [hzx, smul_comm (b x) (a.weight x)]
    · rw [hDx, smul_add, smul_comm (b x) (a.weight x),
        smul_comm (b x) (-Complex.I), smul_comm (b x) (a.gradient i x)]

end PfHk.PhysicalDyadicProductRule
