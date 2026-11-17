import GptLean.SymmetricLift.SmoothGluing
import GptLean.SymmetricLift.SupportedGluing
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! The genuine Frechet derivative of the direct-sum construction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace GptLean.SymmetricLift
open WithLp Filter
open scoped Topology ContDiff BigOperators

variable {X H K : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  {ι : Type*} [Fintype ι]

local instance gluingDerivativeRealH : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ ℂ H
local instance gluingDerivativeRealK : NormedSpace ℝ K := NormedSpace.restrictScalars ℝ ℂ K

def smoothGlueVectorDerivative (P : H →L[ℂ] H) (χ : ι → ℝ)
    (dχ : ι → X →L[ℝ] ℝ) (V : ι → H →L[ℂ] K)
    (dV : ι → X →L[ℝ] (H →L[ℂ] K)) (u : H) : X →L[ℝ] GlueTarget H K ι :=
  ((prodContinuousLinearEquiv 2 ℂ H (PiLp 2 (fun _ : ι => K))).symm.toContinuousLinearMap.restrictScalars ℝ).comp
    ((0 : X →L[ℝ] H).prod
      (((PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => K)).symm.toContinuousLinearMap.restrictScalars ℝ).comp
        (ContinuousLinearMap.pi fun a =>
          χ a • (((ContinuousLinearMap.apply ℂ K (u - P u)).restrictScalars ℝ).comp (dV a)) +
            (dχ a).smulRight (V a (u - P u)))))

theorem smoothGlueVectorDerivative_apply (P : H →L[ℂ] H) (χ : ι → ℝ)
    (dχ : ι → X →L[ℝ] ℝ) (V : ι → H →L[ℂ] K)
    (dV : ι → X →L[ℝ] (H →L[ℂ] K)) (u : H) (d : X) :
    smoothGlueVectorDerivative P χ dχ V dV u d =
      glueDerivative P.toLinearMap χ (fun a => dχ a d)
        (fun a => (V a).toLinearMap) (fun a => (dV a d).toLinearMap) u := by
  apply (WithLp.ext_iff 2).mpr
  apply Prod.ext
  · rfl
  · apply (WithLp.ext_iff 2).mpr
    funext a
    simp [smoothGlueVectorDerivative, glueDerivative, Complex.coe_smul, add_comm]

theorem hasFDerivAt_smoothGlue_vector (P : H →L[ℂ] H)
    {χ : ι → X → ℝ} {V : ι → X → H →L[ℂ] K} {x : X}
    {dχ : ι → X →L[ℝ] ℝ} {dV : ι → X →L[ℝ] (H →L[ℂ] K)}
    (hχ : ∀ a, HasFDerivAt (χ a) (dχ a) x)
    (hV : ∀ a, HasFDerivAt (V a) (dV a) x) (u : H) :
    HasFDerivAt (fun y => smoothGlue P (fun a => χ a y) (fun a => V a y) u)
      (smoothGlueVectorDerivative P (fun a => χ a x) dχ (fun a => V a x) dV u) x := by
  have hlocal := fun a => (hχ a).smul (hasFDerivAt_operator_apply (hV a) (u - P u))
  have hpi := ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => K)).symm.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp x
    (hasFDerivAt_pi.mpr hlocal)
  exact ((prodContinuousLinearEquiv 2 ℂ H (PiLp 2 (fun _ : ι => K))).symm.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp x
    ((hasFDerivAt_const (P u) x).prodMk hpi)

theorem fderiv_smoothGlue_vector (P : H →L[ℂ] H)
    {χ : ι → X → ℝ} {V : ι → X → H →L[ℂ] K} {x : X}
    (hχ : ∀ a, DifferentiableAt ℝ (χ a) x)
    (hV : ∀ a, DifferentiableAt ℝ (V a) x) (u : H) (d : X) :
    fderiv ℝ (fun y => smoothGlue P (fun a => χ a y) (fun a => V a y) u) x d =
      glueDerivative P.toLinearMap (fun a => χ a x) (fun a => fderiv ℝ (χ a) x d)
        (fun a => (V a x).toLinearMap) (fun a => (fderiv ℝ (V a) x d).toLinearMap) u := by
  rw [(hasFDerivAt_smoothGlue_vector P (fun a => (hχ a).hasFDerivAt)
    (fun a => (hV a).hasFDerivAt) u).fderiv]
  exact smoothGlueVectorDerivative_apply _ _ _ _ _ _ _

/-- The product rule remains valid at points outside the chart because the
weight is identically zero on a neighborhood there. No regularity of `V`
outside its chart is required. -/
theorem hasFDerivAt_weighted_of_support {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {O : Set X} {χ : X → ℝ} {V : X → E} {x : X}
    (hχ : DifferentiableAt ℝ χ x) (hsupport : x ∈ tsupport χ → x ∈ O)
    (hV : x ∈ O → DifferentiableAt ℝ V x) :
    HasFDerivAt (fun y => χ y • V y)
      (χ x • fderiv ℝ V x + (fderiv ℝ χ x).smulRight (V x)) x := by
  by_cases hx : x ∈ O
  · exact hχ.hasFDerivAt.smul (hV hx).hasFDerivAt
  · have hs : x ∉ tsupport χ := fun h => hx (hsupport h)
    have hz : χ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hs
    have hχzero : χ x = 0 := hz.self_of_nhds
    have hdχ : fderiv ℝ χ x = 0 := by
      rw [hz.fderiv_eq]
      exact fderiv_const_apply _
    have heq : (fun y => χ y • V y) =ᶠ[𝓝 x] fun _ => (0 : E) := by
      filter_upwards [hz] with y hy
      simp [hy]
    simp only [hχzero, hdχ, zero_smul, ContinuousLinearMap.zero_smulRight, add_zero]
    exact (hasFDerivAt_const (0 : E) x).congr_of_eventuallyEq heq

theorem smoothGlue_actual_flat (P : H →L[ℂ] H)
    {χ : ι → X → ℝ} {V : ι → X → H →L[ℂ] K} {x : X}
    (hχ : ∀ a, DifferentiableAt ℝ (χ a) x)
    (hV : ∀ a, DifferentiableAt ℝ (V a) x)
    (hpartition : ∀ d, ∑ a, χ a x * fderiv ℝ (χ a) x d = 0)
    (hiso : ∀ a u v, inner ℂ (V a x u) (V a x v) = inner ℂ u v)
    (hflat : ∀ d a u v, inner ℂ (V a x u) (fderiv ℝ (V a) x d v) = 0)
    (u v : H) (d : X) :
    inner ℂ (smoothGlue P (fun a => χ a x) (fun a => V a x) u)
      (fderiv ℝ (fun y => smoothGlue P (fun a => χ a y) (fun a => V a y) v) x d) = 0 := by
  rw [fderiv_smoothGlue_vector P hχ hV v d, smoothGlue_apply]
  exact glue_flat _ _ _ _ _ (hpartition d) hiso (hflat d) u v

theorem smoothGlue_actual_metric (P : H →L[ℂ] H)
    {χ : ι → X → ℝ} {V : ι → X → H →L[ℂ] K} {x : X}
    (hχ : ∀ a, DifferentiableAt ℝ (χ a) x)
    (hV : ∀ a, DifferentiableAt ℝ (V a) x)
    (hiso : ∀ a u, ‖V a x u‖ = ‖u‖)
    (hflat : ∀ d a u v, inner ℂ (V a x u) (fderiv ℝ (V a) x d v) = 0)
    (hfixed : ∀ d a u, fderiv ℝ (V a) x d (P u) = 0)
    (u : H) (d : X) :
    ‖fderiv ℝ (fun y => smoothGlue P (fun a => χ a y) (fun a => V a y) u) x d‖ ^ 2 =
      (∑ a, (fderiv ℝ (χ a) x d) ^ 2) * ‖u - P u‖ ^ 2 +
        ∑ a, (χ a x) ^ 2 * ‖fderiv ℝ (V a) x d u‖ ^ 2 := by
  rw [fderiv_smoothGlue_vector P hχ hV u d]
  exact glueDerivative_metric _ _ _ _ _ hiso (hflat d) (hfixed d) u

/-- Genuine derivative formula with chart-local differentiability. -/
theorem fderiv_smoothGlue_vector_supported (P : H →L[ℂ] H)
    {χ : ι → X → ℝ} {V : ι → X → H →L[ℂ] K} {x : X}
    (O : ι → Set X) (hχ : ∀ a, DifferentiableAt ℝ (χ a) x)
    (hsupport : ∀ a, x ∈ tsupport (χ a) → x ∈ O a)
    (hV : ∀ a, x ∈ O a → DifferentiableAt ℝ (V a) x) (u : H) (d : X) :
    fderiv ℝ (fun y => smoothGlue P (fun a => χ a y) (fun a => V a y) u) x d =
      glueDerivative P.toLinearMap (fun a => χ a x) (fun a => fderiv ℝ (χ a) x d)
        (fun a => (V a x).toLinearMap) (fun a => (fderiv ℝ (V a) x d).toLinearMap) u := by
  have hlocal (a : ι) : HasFDerivAt (fun y => χ a y • V a y (u - P u))
      (χ a x • (((ContinuousLinearMap.apply ℂ K (u - P u)).restrictScalars ℝ).comp (fderiv ℝ (V a) x)) +
        (fderiv ℝ (χ a) x).smulRight (V a x (u - P u))) x := by
    have h := hasFDerivAt_operator_apply
      (hasFDerivAt_weighted_of_support (hχ a) (hsupport a) (hV a)) (u - P u)
    convert h using 1 <;> ext z <;> simp [smul_sub]
  have hpi := ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => K)).symm.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp x
    (hasFDerivAt_pi.mpr hlocal)
  have hh := ((prodContinuousLinearEquiv 2 ℂ H (PiLp 2 (fun _ : ι => K))).symm.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp x
    ((hasFDerivAt_const (P u) x).prodMk hpi)
  have hf : HasFDerivAt
      (fun y => smoothGlue P (fun a => χ a y) (fun a => V a y) u)
      (smoothGlueVectorDerivative P (fun a => χ a x) (fun a => fderiv ℝ (χ a) x)
        (fun a => V a x) (fun a => fderiv ℝ (V a) x) u) x := hh
  rw [hf.fderiv]
  exact smoothGlueVectorDerivative_apply _ _ _ _ _ _ _

theorem weight_zero_outside_chart {χ : X → ℝ} {x : X} {O : Set X}
    (hsupport : x ∈ tsupport χ → x ∈ O) (hx : x ∉ O) :
    χ x = 0 ∧ fderiv ℝ χ x = 0 := by
  have hz : χ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp (fun hs => hx (hsupport hs))
  exact ⟨hz.self_of_nhds, by rw [hz.fderiv_eq]; exact fderiv_const_apply _⟩

theorem smoothGlue_actual_flat_supported (P : H →L[ℂ] H)
    {χ : ι → X → ℝ} {V : ι → X → H →L[ℂ] K} {x : X}
    (O : ι → Set X) (hχ : ∀ a, DifferentiableAt ℝ (χ a) x)
    (hsupport : ∀ a, x ∈ tsupport (χ a) → x ∈ O a)
    (hV : ∀ a, x ∈ O a → DifferentiableAt ℝ (V a) x)
    (hpartition : ∀ d, ∑ a, χ a x * fderiv ℝ (χ a) x d = 0)
    (hiso : ∀ a, x ∈ O a → ∀ u v, inner ℂ (V a x u) (V a x v) = inner ℂ u v)
    (hflat : ∀ d a, x ∈ O a → ∀ u v, inner ℂ (V a x u) (fderiv ℝ (V a) x d v) = 0)
    (u v : H) (d : X) :
    inner ℂ (smoothGlue P (fun a => χ a x) (fun a => V a x) u)
      (fderiv ℝ (fun y => smoothGlue P (fun a => χ a y) (fun a => V a y) v) x d) = 0 := by
  rw [fderiv_smoothGlue_vector_supported P O hχ hsupport hV v d, smoothGlue_apply]
  exact glue_flat_supported _ _ _ _ _ (fun a => x ∈ O a) (hpartition d)
    (fun a ha => (weight_zero_outside_chart (hsupport a) ha).1) hiso (hflat d) u v

theorem smoothGlue_actual_metric_supported (P : H →L[ℂ] H)
    {χ : ι → X → ℝ} {V : ι → X → H →L[ℂ] K} {x : X}
    (O : ι → Set X) (hχ : ∀ a, DifferentiableAt ℝ (χ a) x)
    (hsupport : ∀ a, x ∈ tsupport (χ a) → x ∈ O a)
    (hV : ∀ a, x ∈ O a → DifferentiableAt ℝ (V a) x)
    (hiso : ∀ a, x ∈ O a → ∀ u, ‖V a x u‖ = ‖u‖)
    (hflat : ∀ d a, x ∈ O a → ∀ u v, inner ℂ (V a x u) (fderiv ℝ (V a) x d v) = 0)
    (hfixed : ∀ d a, x ∈ O a → ∀ u, fderiv ℝ (V a) x d (P u) = 0)
    (u : H) (d : X) :
    ‖fderiv ℝ (fun y => smoothGlue P (fun a => χ a y) (fun a => V a y) u) x d‖ ^ 2 =
      (∑ a, (fderiv ℝ (χ a) x d) ^ 2) * ‖u - P u‖ ^ 2 +
        ∑ a, (χ a x) ^ 2 * ‖fderiv ℝ (V a) x d u‖ ^ 2 := by
  rw [fderiv_smoothGlue_vector_supported P O hχ hsupport hV u d]
  exact glue_metric_supported _ _ _ _ _ (fun a => x ∈ O a)
    (fun a ha => (weight_zero_outside_chart (hsupport a) ha).1)
    (fun a ha => by rw [(weight_zero_outside_chart (hsupport a) ha).2]; rfl)
    hiso (hflat d) (hfixed d) u

theorem fderiv_operator_apply {U : X → H →L[ℂ] K} {x : X}
    (hU : DifferentiableAt ℝ U x) (u : H) (d : X) :
    fderiv ℝ (fun y => U y u) x d = fderiv ℝ U x d u := by
  rw [(hasFDerivAt_operator_apply hU.hasFDerivAt u).fderiv]
  rfl

end GptLean.SymmetricLift
