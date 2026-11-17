import GptLean.ElectronicH1Symmetry
import GptLean.PhotonLocalizationLocalForms

/-! Smooth bounded multipliers preserve H1 and give the weighted integration-by-parts law. -/

noncomputable section

namespace GptLean.ElectronicH1Multiplier

open MeasureTheory ElectronicH1Space PhotonLocalization
open scoped ENNReal ContDiff InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000

variable (I : Type*) [Fintype I] [DecidableEq I]

structure SmoothMultiplier where
  weight : EuclideanSpace ℝ I → ℝ
  smooth : ContDiff ℝ ∞ weight
  bound : ℝ
  bounded : ∀ x, |weight x| ≤ bound
  derivativeBound : ℝ
  derivative_bounded : ∀ i x,
    |fderiv ℝ weight x (EuclideanSpace.single i 1)| ≤ derivativeBound

namespace SmoothMultiplier

variable {I} (a : SmoothMultiplier I)

def gradient (i : I) (x : EuclideanSpace ℝ I) : ℝ :=
  fderiv ℝ a.weight x (EuclideanSpace.single i 1)

theorem gradient_continuous (i : I) : Continuous (a.gradient i) :=
  (a.smooth.continuous_fderiv (by simp)).clm_apply continuous_const

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def multiplier : L2 H I →L[ℂ] L2 H I :=
  realL2Multiplier a.weight a.smooth.continuous.aestronglyMeasurable a.bound
    (ae_of_all _ a.bounded)

def derivativeMultiplier (i : I) : L2 H I →L[ℂ] L2 H I :=
  realL2Multiplier (a.gradient i) (a.gradient_continuous i).aestronglyMeasurable
    a.derivativeBound (ae_of_all _ (a.derivative_bounded i))

omit [CompleteSpace H] in
theorem weighted_memLp (u : L2 H I) : MemLp (fun x => a.weight x • u x) 2 volume := by
  apply (Lp.memLp u).of_le_mul (c := a.bound)
    (a.smooth.continuous.aestronglyMeasurable.smul (Lp.aestronglyMeasurable u))
  exact ae_of_all _ fun x => by
    simpa only [Pi.smul_apply', norm_smul, Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_right (a.bounded x) (norm_nonneg (u x))

omit [CompleteSpace H] in
theorem derivative_weighted_memLp (i : I) (u : L2 H I) :
    MemLp (fun x => a.gradient i x • u x) 2 volume := by
  apply (Lp.memLp u).of_le_mul (c := a.derivativeBound)
    ((a.gradient_continuous i).aestronglyMeasurable.smul (Lp.aestronglyMeasurable u))
  exact ae_of_all _ fun x => by
    simpa only [Pi.smul_apply', norm_smul, Real.norm_eq_abs, gradient] using
      mul_le_mul_of_nonneg_right (a.derivative_bounded i x) (norm_nonneg (u x))

def multiply (u : H1 H I) : H1 H I :=
  ofFunctions (fun x => a.weight x • value u x)
    (fun i x => a.weight x • derivative i u x + a.gradient i x • value u x)
    (a.weighted_memLp (value u))
    (fun i => (a.weighted_memLp (derivative i u)).add (a.derivative_weighted_memLp i (value u)))
    (Repair.weakH1Local_smooth_real_smul (weak u) a.smooth)

theorem value_multiply (u : H1 H I) : value (a.multiply u) = a.multiplier (value u) := by
  apply Lp.ext
  exact (a.weighted_memLp (value u)).coeFn_toLp.trans
    (realL2Multiplier_apply a.weight a.smooth.continuous.aestronglyMeasurable a.bound
      (ae_of_all _ a.bounded) (value u)).symm

theorem derivative_multiply (i : I) (u : H1 H I) :
    derivative i (a.multiply u) = a.multiplier (derivative i u) + a.derivativeMultiplier i (value u) := by
  apply Lp.ext
  have hrep := ((a.weighted_memLp (derivative i u)).add
    (a.derivative_weighted_memLp i (value u))).coeFn_toLp
  filter_upwards [hrep,
    realL2Multiplier_apply a.weight a.smooth.continuous.aestronglyMeasurable a.bound
      (ae_of_all _ a.bounded) (derivative i u),
    realL2Multiplier_apply (a.gradient i) (a.gradient_continuous i).aestronglyMeasurable
      a.derivativeBound (ae_of_all _ (a.derivative_bounded i)) (value u),
    Lp.coeFn_add (a.multiplier (derivative i u)) (a.derivativeMultiplier i (value u))]
    with x hx h₁ h₂ h₃
  exact hx.trans (h₃.trans (congrArg₂ (· + ·) h₁ h₂)).symm

omit [CompleteSpace H] in
private theorem realMultiplier_symmetric {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : X → ℝ) (hf : AEStronglyMeasurable f μ) (c : ℝ)
    (hc : ∀ᵐ x ∂μ, |f x| ≤ c) (u v : Lp H 2 μ) :
    ⟪u, realL2Multiplier f hf c hc v⟫_ℂ = ⟪realL2Multiplier f hf c hc u, v⟫_ℂ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [realL2Multiplier_apply f hf c hc u,
    realL2Multiplier_apply f hf c hc v] with x hu hv
  rw [hu, hv, inner_smul_left_eq_smul, inner_smul_right_eq_smul]

omit [CompleteSpace H] in
theorem multiplier_symmetric (u v : L2 H I) :
    ⟪u, a.multiplier v⟫_ℂ = ⟪a.multiplier u, v⟫_ℂ :=
  realMultiplier_symmetric _ _ _ _ u v

omit [CompleteSpace H] in
theorem derivativeMultiplier_symmetric (i : I) (u v : L2 H I) :
    ⟪u, a.derivativeMultiplier i v⟫_ℂ = ⟪a.derivativeMultiplier i u, v⟫_ℂ :=
  realMultiplier_symmetric _ _ _ _ u v

theorem weighted_integration_by_parts (u v : H1 H I) (i : I) :
    ⟪value u, a.multiplier (derivative i v)⟫_ℂ =
      -(⟪a.multiplier (derivative i u), value v⟫_ℂ +
        ⟪a.derivativeMultiplier i (value u), value v⟫_ℂ) := by
  have h := ElectronicH1Symmetry.integration_by_parts (a.multiply u) v i
  rw [a.value_multiply, a.derivative_multiply, inner_add_left] at h
  exact (a.multiplier_symmetric (value u) (derivative i v)).trans h

end SmoothMultiplier
end GptLean.ElectronicH1Multiplier
