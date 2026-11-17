import GptLean.ElectronicH1Multiplier

/-! The symmetrized weighted momentum on the actual complex H1 domain. -/

noncomputable section

namespace GptLean.ElectronicH1Multiplier.SmoothMultiplier

open ElectronicH1Complex
open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000

variable {I H : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (a : SmoothMultiplier I)

def momentum (i : I) : ComplexH1 H I →L[ℂ] ElectronicH1Space.L2 H I :=
  (-Complex.I) • (a.multiplier.comp (derivative i)) +
    (-Complex.I / 2) • ((a.derivativeMultiplier i).comp value)

theorem momentum_symmetric (i : I) (u v : ComplexH1 H I) :
    ⟪value u, a.momentum i v⟫_ℂ = ⟪a.momentum i u, value v⟫_ℂ := by
  have hp := a.weighted_integration_by_parts (realEquiv u) (realEquiv v) i
  have hd := a.derivativeMultiplier_symmetric i (value u) (value v)
  change ⟪value u, (-Complex.I) • a.multiplier (derivative i v) +
    (-Complex.I / 2) • a.derivativeMultiplier i (value v)⟫_ℂ =
      ⟪(-Complex.I) • a.multiplier (derivative i u) +
        (-Complex.I / 2) • a.derivativeMultiplier i (value u), value v⟫_ℂ
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
  change ⟪value u, a.multiplier (derivative i v)⟫_ℂ =
    -(⟪a.multiplier (derivative i u), value v⟫_ℂ +
      ⟪a.derivativeMultiplier i (value u), value v⟫_ℂ) at hp
  rw [hp, hd]
  simp only [map_neg, map_div₀, map_ofNat, Complex.conj_I]
  ring

theorem momentum_diagonal (i : I) (u : ComplexH1 H I) :
    (⟪value u, a.momentum i u⟫_ℂ).re =
      (⟪value u, a.multiplier ((-Complex.I) • derivative i u)⟫_ℂ).re := by
  have hd := a.derivativeMultiplier_symmetric i (value u) (value u)
  have him : (⟪value u, a.derivativeMultiplier i (value u)⟫_ℂ).im = 0 := by
    have hd' := congrArg Complex.im hd
    have hc := congrArg Complex.im
      (inner_conj_symm (𝕜 := ℂ) (value u) (a.derivativeMultiplier i (value u)))
    simp only [Complex.conj_im] at hc
    linarith
  change (⟪value u, (-Complex.I) • a.multiplier (derivative i u) +
      (-Complex.I / 2) • a.derivativeMultiplier i (value u)⟫_ℂ).re = _
  simp only [inner_add_right, Complex.add_re, map_smul, inner_smul_right]
  simp only [Complex.mul_re, Complex.neg_re, Complex.I_re, neg_zero, zero_mul,
    Complex.neg_im, Complex.I_im, Complex.div_ofNat_re, Complex.div_ofNat_im, him,
    mul_zero, sub_zero, zero_div, add_zero]

end GptLean.ElectronicH1Multiplier.SmoothMultiplier
