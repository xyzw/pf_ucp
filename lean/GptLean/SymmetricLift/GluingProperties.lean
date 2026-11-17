import GptLean.SymmetricLift.GluingDerivative

/-! Operator-valued conclusions for smooth gluing on supported local charts. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace GptLean.SymmetricLift
open WithLp Filter
open scoped BigOperators ContDiff Topology

variable {X H K ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [Fintype ι]
local instance gluingPropertiesRealH : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ ℂ H
local instance gluingPropertiesRealK : NormedSpace ℝ K := NormedSpace.restrictScalars ℝ ℂ K

theorem smoothGlue_norm_supported (P : H →L[ℂ] H) (χ : ι → ℝ)
    (V : ι → H →L[ℂ] K) (active : ι → Prop)
    (horth : ∀ u v, inner ℂ (P u) (v - P v) = 0)
    (hpartition : ∑ a, χ a ^ 2 = 1)
    (hzero : ∀ a, ¬ active a → χ a = 0)
    (hiso : ∀ a, active a → ∀ u, ‖V a u‖ = ‖u‖) (u : H) :
    ‖smoothGlue P χ V u‖ = ‖u‖ := by
  have hi (a : ι) (ha : active a) (v w : H) : inner ℂ (V a v) (V a w) = inner ℂ v w :=
    (show H →ₗᵢ[ℂ] K from ⟨(V a).toLinearMap, hiso a ha⟩).inner_map_map v w
  rw [smoothGlue_apply]
  have hs : ‖glue P.toLinearMap χ (fun a => (V a).toLinearMap) u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ),
      glue_inner_supported _ _ _ active horth hpartition hzero hi]
  nlinarith [norm_nonneg (glue P.toLinearMap χ (fun a => (V a).toLinearMap) u), norm_nonneg u]

theorem smoothGlue_fixed (P : H →L[ℂ] H) (χ : ι → ℝ) (V : ι → H →L[ℂ] K)
    (hP : ∀ u, P (P u) = P u) (u : H) :
    smoothGlue P χ V (P u) = toLp 2 (P u, (0 : PiLp 2 (fun _ : ι => K))) := by
  rw [smoothGlue_apply]
  exact glue_fixed _ _ _ hP u

theorem smoothGlue_equivariant_supported (P R : H →L[ℂ] H) (χ χ' : ι → ℝ)
    (V V' : ι → H →L[ℂ] K) (active : ι → Prop) (hχ : χ' = χ)
    (hPR : ∀ u, P (R u) = P u) (hRP : ∀ u, R (P u) = P u)
    (hzero : ∀ a, ¬ active a → χ a = 0)
    (hV : ∀ a, active a → ∀ u, V' a (R u) = V a u) (u : H) :
    smoothGlue P χ' V' (R u) = smoothGlue P χ V u := by
  simp only [smoothGlue_apply]
  exact glue_equivariant_supported _ _ _ _ _ _ active hχ hPR hRP hzero hV u

theorem smoothGlue_operator_flat_supported (P : H →L[ℂ] H)
    {χ : ι → X → ℝ} {V : ι → X → H →L[ℂ] K} {x : X}
    (O : ι → Set X) (hχ : ∀ a, DifferentiableAt ℝ (χ a) x)
    (hsupport : ∀ a, x ∈ tsupport (χ a) → x ∈ O a)
    (hV : ∀ a, x ∈ O a → DifferentiableAt ℝ (V a) x)
    (hU : DifferentiableAt ℝ (fun y => smoothGlue P (fun a => χ a y) (fun a => V a y)) x)
    (hpartition : ∀ d, ∑ a, χ a x * fderiv ℝ (χ a) x d = 0)
    (hiso : ∀ a, x ∈ O a → ∀ u, ‖V a x u‖ = ‖u‖)
    (hflat : ∀ d a, x ∈ O a → ∀ u v, inner ℂ (V a x u) (fderiv ℝ (V a) x d v) = 0)
    (u v : H) (d : X) :
    inner ℂ (smoothGlue P (fun a => χ a x) (fun a => V a x) u)
      (fderiv ℝ (fun y => smoothGlue P (fun a => χ a y) (fun a => V a y)) x d v) = 0 := by
  rw [← fderiv_operator_apply hU v d]
  apply smoothGlue_actual_flat_supported P O hχ hsupport hV hpartition _ hflat u v d
  intro a ha z w
  exact (show H →ₗᵢ[ℂ] K from ⟨(V a x).toLinearMap, hiso a ha⟩).inner_map_map z w

theorem smoothGlue_operator_coordinate_metric {δ : Type*} [Fintype δ]
    (P : H →L[ℂ] H) (direction : δ → X)
    {χ : ι → X → ℝ} {V : ι → X → H →L[ℂ] K} {x : X}
    (O : ι → Set X) (hχ : ∀ a, DifferentiableAt ℝ (χ a) x)
    (hsupport : ∀ a, x ∈ tsupport (χ a) → x ∈ O a)
    (hV : ∀ a, x ∈ O a → DifferentiableAt ℝ (V a) x)
    (hU : DifferentiableAt ℝ (fun y => smoothGlue P (fun a => χ a y) (fun a => V a y)) x)
    (hiso : ∀ a, x ∈ O a → ∀ u, ‖V a x u‖ = ‖u‖)
    (hflat : ∀ d a, x ∈ O a → ∀ u v, inner ℂ (V a x u) (fderiv ℝ (V a) x d v) = 0)
    (hfixed : ∀ d a, x ∈ O a → ∀ u, fderiv ℝ (V a) x d (P u) = 0)
    (u : H) :
    (∑ q, ‖fderiv ℝ (fun y => smoothGlue P (fun a => χ a y) (fun a => V a y)) x (direction q) u‖ ^ 2) =
      (∑ q, ∑ a, (fderiv ℝ (χ a) x (direction q)) ^ 2) * ‖u - P u‖ ^ 2 +
        ∑ a, (χ a x) ^ 2 * ∑ q, ‖fderiv ℝ (V a) x (direction q) u‖ ^ 2 := by
  simp_rw [← fderiv_operator_apply hU u,
    smoothGlue_actual_metric_supported P O hχ hsupport hV hiso hflat hfixed u]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum]

/-- A local constant action on the projected subspace has zero derivative. -/
theorem derivative_fixed_on_open {O : Set X} (hO : IsOpen O)
    {U : X → H →L[ℂ] K} {x : X} (hx : x ∈ O)
    (hU : DifferentiableAt ℝ U x) (P : H →L[ℂ] H) (C : H →L[ℂ] K)
    (hfixed : ∀ y ∈ O, ∀ u, U y (P u) = C u) (d : X) (u : H) :
    fderiv ℝ U x d (P u) = 0 := by
  rw [← fderiv_operator_apply hU (P u) d]
  have heq : (fun y => U y (P u)) =ᶠ[𝓝 x] fun _ => C u := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact hfixed y hy u
  rw [heq.fderiv_eq, fderiv_const_apply]
  rfl

end GptLean.SymmetricLift
