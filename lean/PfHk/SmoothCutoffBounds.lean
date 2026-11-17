import PfHk.PhysicalCutoffMultiplier
import GptLean.PhotonLocalizationFormBounds
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! Smooth scalar rescaling from compact derivative and Hessian bounds.
The theorem is universal over compactly supported smooth real functions.
The actual cutoff multiplier is constructed from the existing retained bump,
with its formula fixed below. -/

noncomputable section
namespace PfHk.SmoothCutoffBounds

open GptLean GptLean.ElectronicH1Multiplier GptLean.PhotonLocalizationKernelCutoffs
open PfHk.PhysicalCutoffCommutator

set_option maxHeartbeats 40000
set_option Elab.async false

def coordinateDerivative {I : Type} [Fintype I] [DecidableEq I]
    (f : EuclideanSpace ℝ I → ℝ) (i : I) (x : EuclideanSpace ℝ I) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.single i 1)

def scaled {I : Type} [Fintype I] (f : EuclideanSpace ℝ I → ℝ)
    (x₀ : EuclideanSpace ℝ I) (r : ℝ) (x : EuclideanSpace ℝ I) : ℝ :=
  f (r⁻¹ • (x - x₀))

/-- Standard compact-Hessian boundedness and the ordinary chain rule under
translations and positive dilations, quantified independently of the model. -/
def StandardSmoothRescaling : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (f : EuclideanSpace ℝ I → ℝ),
    ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
    ∃ B₁ B₂ : ℝ, 0 ≤ B₁ ∧ 0 ≤ B₂ ∧
      ∀ (x₀ : EuclideanSpace ℝ I) (r : ℝ), 0 < r →
        (∀ i x, |coordinateDerivative (scaled f x₀ r) i x| ≤ B₁ / r) ∧
        (∀ i j x, |coordinateDerivative (coordinateDerivative (scaled f x₀ r) i) j x| ≤ B₂ / r ^ 2)

private theorem coordinateDerivative_scaled {I : Type} [Fintype I] [DecidableEq I]
    {f : EuclideanSpace ℝ I → ℝ} (hf : Differentiable ℝ f)
    (x₀ : EuclideanSpace ℝ I) (r : ℝ) (i : I) (x : EuclideanSpace ℝ I) :
    coordinateDerivative (scaled f x₀ r) i x =
      r⁻¹ * coordinateDerivative f i (r⁻¹ • (x - x₀)) := by
  have hT := ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const x₀).const_smul r⁻¹
  have hc := (hf (r⁻¹ • (x - x₀))).hasFDerivAt.comp x hT
  change (fderiv ℝ (fun y : EuclideanSpace ℝ I => f (r⁻¹ • (y - x₀))) x)
      (EuclideanSpace.single i 1) =
    r⁻¹ * (fderiv ℝ f (r⁻¹ • (x - x₀))) (EuclideanSpace.single i 1)
  simpa only [Function.comp_def, Pi.smul_apply,
    Pi.sub_apply, id_eq, ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul] using
      congrArg (fun T : EuclideanSpace ℝ I →L[ℝ] ℝ => T (EuclideanSpace.single i 1)) hc.fderiv

private theorem coordinateDerivative_const_mul {I : Type} [Fintype I] [DecidableEq I]
    {f : EuclideanSpace ℝ I → ℝ} (hf : Differentiable ℝ f)
    (c : ℝ) (i : I) (x : EuclideanSpace ℝ I) :
    coordinateDerivative (fun y => c * f y) i x = c * coordinateDerivative f i x := by
  unfold coordinateDerivative
  rw [((hf x).hasFDerivAt.const_mul c).fderiv]
  rfl

/-- Compactness bounds the first two derivatives of a fixed smooth
function. The chain rule supplies the exact inverse-radius powers. -/
theorem standardSmoothRescaling : StandardSmoothRescaling := by
  intro I _ _ f hf hs
  have hdf := (contDiff_infty_iff_fderiv.mp hf).2
  obtain ⟨B₁, hB₁⟩ := (hf.continuous_fderiv (by simp)).bounded_above_of_compact_support (hs.fderiv ℝ)
  obtain ⟨B₂, hB₂⟩ := (hdf.continuous_fderiv (by simp)).bounded_above_of_compact_support
    ((hs.fderiv ℝ).fderiv ℝ)
  have hB₁0 : 0 ≤ B₁ := (norm_nonneg _).trans (hB₁ 0)
  have hB₂0 : 0 ≤ B₂ := (norm_nonneg _).trans (hB₂ 0)
  have hfirst (i : I) (x : EuclideanSpace ℝ I) : |coordinateDerivative f i x| ≤ B₁ := by
    simpa only [coordinateDerivative, Real.norm_eq_abs, PiLp.norm_single, norm_one, mul_one] using
      (fderiv ℝ f x).le_of_opNorm_le (hB₁ x) (EuclideanSpace.single i 1)
  have hgs (i : I) : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative f i) :=
    hdf.clm_apply contDiff_const
  have hsecond (i j : I) (x : EuclideanSpace ℝ I) :
      |coordinateDerivative (coordinateDerivative f i) j x| ≤ B₂ := by
    have hid : coordinateDerivative (coordinateDerivative f i) j x =
        fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single j 1) (EuclideanSpace.single i 1) := by
      unfold coordinateDerivative
      rw [fderiv_clm_apply (hdf.differentiable (by simp) x) (differentiableAt_const _)]
      simp
    rw [hid, ← Real.norm_eq_abs]
    have hb : ‖fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single j 1)‖ ≤ B₂ := by
      simpa only [PiLp.norm_single, norm_one, mul_one] using
        (fderiv ℝ (fderiv ℝ f) x).le_of_opNorm_le (hB₂ x) (EuclideanSpace.single j 1)
    simpa only [PiLp.norm_single, norm_one, mul_one] using
      (fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single j 1)).le_of_opNorm_le hb
        (EuclideanSpace.single i 1)
  refine ⟨B₁, B₂, hB₁0, hB₂0, ?_⟩
  intro x₀ r hr
  have hc : 0 ≤ r⁻¹ := inv_nonneg.mpr hr.le
  constructor
  · intro i x
    rw [coordinateDerivative_scaled (hf.differentiable (by simp)), abs_mul, abs_of_nonneg hc]
    exact (mul_le_mul_of_nonneg_left (hfirst i _) hc).trans_eq (by ring)
  · intro i j x
    have hid : coordinateDerivative (scaled f x₀ r) i =
        fun y => r⁻¹ * scaled (coordinateDerivative f i) x₀ r y := by
      funext y
      exact coordinateDerivative_scaled (hf.differentiable (by simp)) x₀ r i y
    have hscaled : Differentiable ℝ (scaled (coordinateDerivative f i) x₀ r) :=
      (hgs i).differentiable (by simp) |>.comp
        ((differentiable_id.sub_const x₀).const_smul r⁻¹)
    rw [hid, coordinateDerivative_const_mul hscaled,
      coordinateDerivative_scaled ((hgs i).differentiable (by simp)),
      abs_mul, abs_mul, abs_of_nonneg hc]
    have hh := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hsecond i j (r⁻¹ • (x - x₀))) hc) hc
    exact hh.trans_eq (by rw [div_eq_mul_inv, ← inv_pow]; ring)

/-- Package the actual first derivatives as differentiable multipliers,
with second derivatives controlled by the proved uniform rescaling theorem. -/
theorem exists_twice_scaled (I : Type) [Fintype I] [DecidableEq I]
    (φ : EuclideanSpace ℝ I → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hs : HasCompactSupport φ) (hb : ∀ x, |φ x| ≤ 1) :
    ∃ B₁ B₂ : ℝ, 0 ≤ B₁ ∧ 0 ≤ B₂ ∧
      ∀ (x₀ : EuclideanSpace ℝ I) (r : ℝ), 0 < r →
        ∃ a : TwiceDifferentiableMultiplier I,
          a.scalar.weight = scaled φ x₀ r ∧
          (∀ i x, |a.scalar.gradient i x| ≤ B₁ / r) ∧
          (∀ i j x, |(a.derivative i).gradient j x| ≤ B₂ / r ^ 2) := by
  obtain ⟨B₁, B₂, hB₁, hB₂, hbounds⟩ := standardSmoothRescaling I φ hφ hs
  refine ⟨B₁, B₂, hB₁, hB₂, ?_⟩
  intro x₀ r hr
  let f := scaled φ x₀ r
  have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
    hφ.comp (ContDiff.const_smul r⁻¹ (contDiff_id.sub contDiff_const))
  obtain ⟨hfirst, hsecond⟩ := hbounds x₀ r hr
  have hfirstsmooth (i : I) : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative f i) :=
    (contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const
  let a : DifferentiableMultiplier I := {
    weight := f
    differentiable := hf.differentiable (by simp)
    bound := 1
    bounded := fun x => hb (r⁻¹ • (x - x₀))
    derivativeBound := B₁ / r
    derivative_bounded := hfirst }
  let da : I → DifferentiableMultiplier I := fun i => {
    weight := coordinateDerivative f i
    differentiable := (hfirstsmooth i).differentiable (by simp)
    bound := B₁ / r
    bounded := hfirst i
    derivativeBound := B₂ / r ^ 2
    derivative_bounded := hsecond i }
  exact ⟨⟨a, da, fun _ => rfl⟩, rfl, hfirst, hsecond⟩

theorem exists_retained_twice (I : Type) [Fintype I] [DecidableEq I] :
    ∃ B₁ B₂ : ℝ, 0 ≤ B₁ ∧ 0 ≤ B₂ ∧
      ∀ (x₀ : EuclideanSpace ℝ I) (r : ℝ), 0 < r →
        ∃ a : TwiceDifferentiableMultiplier I,
          a.scalar.weight = (fun x => retained r (x - x₀)) ∧
          (∀ i x, |a.scalar.gradient i x| ≤ B₁ / r) ∧
          (∀ i j x, |(a.derivative i).gradient j x| ≤ B₂ / r ^ 2) := by
  obtain ⟨B₁, B₂, hB₁, hB₂, hfamily⟩ := exists_twice_scaled I (retained 1)
    (retained_smooth 1) PhotonLocalizationFormBounds.retained_hasCompactSupport
    (retained_abs_le_one 1)
  refine ⟨B₁, B₂, hB₁, hB₂, ?_⟩
  intro x₀ r hr
  obtain ⟨a, ha, hfirst, hsecond⟩ := hfamily x₀ r hr
  refine ⟨a, ha.trans ?_, hfirst, hsecond⟩
  funext x
  simp only [scaled, retained, inv_one, one_smul]

/-- Margins inside the annulus avoid any boundary differentiation issue.
After rescaling, all derivatives are zero near radii at most `r` or at least
`2r`, while the transition stays between `5r/4` and `7r/4`. -/
def bufferedBump (I : Type) [Fintype I] : ContDiffBump (0 : EuclideanSpace ℝ I) :=
  ⟨5 / 4, 7 / 4, by norm_num, by norm_num⟩

theorem exists_buffered_twice (I : Type) [Fintype I] [DecidableEq I] :
    ∃ B₁ B₂ : ℝ, 0 ≤ B₁ ∧ 0 ≤ B₂ ∧
      ∀ (x₀ : EuclideanSpace ℝ I) (r : ℝ), 0 < r →
        ∃ a : TwiceDifferentiableMultiplier I,
          a.scalar.weight = scaled (bufferedBump I) x₀ r ∧
          (∀ i x, |a.scalar.gradient i x| ≤ B₁ / r) ∧
          (∀ i j x, |(a.derivative i).gradient j x| ≤ B₂ / r ^ 2) := by
  apply exists_twice_scaled I (bufferedBump I) (bufferedBump I).contDiff
    (bufferedBump I).hasCompactSupport
  intro x
  rw [abs_of_nonneg (bufferedBump I).nonneg]
  exact (bufferedBump I).le_one

end PfHk.SmoothCutoffBounds
