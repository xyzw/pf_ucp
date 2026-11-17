import GptLean.ElectronicH1Symmetry
import GptLean.PhotonLocalizationLocalForms
import GptLean.Repair.WeakMultiplierProduct
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! Bounded differentiable multipliers preserve the actual weak H1 domain.
The derivative need only be measurable and bounded. This includes the
symmetric electronic localization branches at their zero sets. -/

noncomputable section

namespace GptLean.ElectronicH1Multiplier

open MeasureTheory ElectronicH1Space PhotonLocalization SymmetricLift
open scoped ENNReal ContDiff InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000

variable (I : Type*) [Fintype I] [DecidableEq I]

structure DifferentiableMultiplier where
  weight : EuclideanSpace ℝ I → ℝ
  differentiable : Differentiable ℝ weight
  bound : ℝ
  bounded : ∀ x, |weight x| ≤ bound
  derivativeBound : ℝ
  derivative_bounded : ∀ i x,
    |fderiv ℝ weight x (EuclideanSpace.single i 1)| ≤ derivativeBound

namespace DifferentiableMultiplier

variable {I} (a : DifferentiableMultiplier I)

def gradient (i : I) (x : EuclideanSpace ℝ I) : ℝ :=
  fderiv ℝ a.weight x (EuclideanSpace.single i 1)

theorem gradient_measurable (i : I) : Measurable (a.gradient i) :=
  measurable_fderiv_apply_const ℝ a.weight (EuclideanSpace.single i 1)

theorem weak_weight : HasWeakH1Local a.weight a.gradient := by
  have ha : AEStronglyMeasurable a.weight volume :=
    a.differentiable.continuous.aestronglyMeasurable
  have hb : ∀ᵐ x ∂volume, ‖a.weight x‖ ≤ a.bound :=
    ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using a.bounded x
  have hd (i : I) : ∀ᵐ x ∂volume, ‖a.gradient i x‖ ≤ a.derivativeBound :=
    ae_of_all _ fun x => by
      simpa only [Real.norm_eq_abs, gradient] using a.derivative_bounded i x
  refine ⟨?_, ?_, ?_⟩
  · intro K hK
    let : IsFiniteMeasure (volume.restrict K) :=
      isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
    exact MemLp.of_bound ha.restrict a.bound (ae_restrict_le hb)
  · intro i K hK
    let : IsFiniteMeasure (volume.restrict K) :=
      isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
    exact MemLp.of_bound (a.gradient_measurable i).aestronglyMeasurable.restrict
      a.derivativeBound (ae_restrict_le (hd i))
  · intro i φ hφ hs
    have hφi : Integrable φ volume := hφ.continuous.integrable_of_hasCompactSupport hs
    have hdi : Integrable (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) volume :=
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
        (hs.fderiv_apply ℝ _)
    exact integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
      (hdi.mul_bdd ha hb)
      (hφi.mul_bdd (a.gradient_measurable i).aestronglyMeasurable (hd i))
      (hφi.mul_bdd ha hb)
      (fun x _ => hφ.differentiable (by simp) x)
      (fun x _ => a.differentiable x)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def multiplier : L2 H I →L[ℂ] L2 H I :=
  realL2Multiplier a.weight a.differentiable.continuous.aestronglyMeasurable a.bound
    (ae_of_all _ a.bounded)

def derivativeMultiplier (i : I) : L2 H I →L[ℂ] L2 H I :=
  realL2Multiplier (a.gradient i) (a.gradient_measurable i).aestronglyMeasurable
    a.derivativeBound (ae_of_all _ (a.derivative_bounded i))

omit [CompleteSpace H] in
theorem weighted_memLp (u : L2 H I) : MemLp (fun x => a.weight x • u x) 2 volume := by
  apply (Lp.memLp u).of_le_mul (c := a.bound)
    (a.differentiable.continuous.aestronglyMeasurable.smul (Lp.aestronglyMeasurable u))
  exact ae_of_all _ fun x => by
    simpa only [Pi.smul_apply', norm_smul, Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_right (a.bounded x) (norm_nonneg (u x))

omit [CompleteSpace H] in
theorem derivative_weighted_memLp (i : I) (u : L2 H I) :
    MemLp (fun x => a.gradient i x • u x) 2 volume := by
  apply (Lp.memLp u).of_le_mul (c := a.derivativeBound)
    ((a.gradient_measurable i).aestronglyMeasurable.smul (Lp.aestronglyMeasurable u))
  exact ae_of_all _ fun x => by
    simpa only [Pi.smul_apply', norm_smul, Real.norm_eq_abs, gradient] using
      mul_le_mul_of_nonneg_right (a.derivative_bounded i x) (norm_nonneg (u x))

def multiply (u : H1 H I) : H1 H I :=
  ofFunctions (fun x => a.weight x • value u x)
    (fun i x => a.weight x • derivative i u x + a.gradient i x • value u x)
    (a.weighted_memLp (value u))
    (fun i => (a.weighted_memLp (derivative i u)).add (a.derivative_weighted_memLp i (value u)))
    (Repair.weakH1Local_real_smul_of_weighted a.weak_weight (weak u)
      (fun K _ => (a.weighted_memLp (value u)).restrict K)
      (fun i K _ => (a.weighted_memLp (derivative i u)).restrict K)
      (fun i K _ => (a.derivative_weighted_memLp i (value u)).restrict K))

theorem value_multiply (u : H1 H I) : value (a.multiply u) = a.multiplier (value u) := by
  apply Lp.ext
  exact (a.weighted_memLp (value u)).coeFn_toLp.trans
    (realL2Multiplier_apply a.weight a.differentiable.continuous.aestronglyMeasurable a.bound
      (ae_of_all _ a.bounded) (value u)).symm

theorem derivative_multiply (i : I) (u : H1 H I) :
    derivative i (a.multiply u) = a.multiplier (derivative i u) + a.derivativeMultiplier i (value u) := by
  apply Lp.ext
  have hrep := ((a.weighted_memLp (derivative i u)).add
    (a.derivative_weighted_memLp i (value u))).coeFn_toLp
  filter_upwards [hrep,
    realL2Multiplier_apply a.weight a.differentiable.continuous.aestronglyMeasurable a.bound
      (ae_of_all _ a.bounded) (derivative i u),
    realL2Multiplier_apply (a.gradient i) (a.gradient_measurable i).aestronglyMeasurable
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

end DifferentiableMultiplier
end GptLean.ElectronicH1Multiplier
