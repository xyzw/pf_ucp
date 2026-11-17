import PfHk.CounterexampleMagneticField

/-! The bounded cylindrical magnetic field for the spinful counterexample. -/

noncomputable section
namespace PfHk.SpinfulCounterexampleField

open MeasureTheory Filter
open scoped InnerProductSpace ContDiff

set_option Elab.async false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types true

abbrev Space := CounterexampleField.Space
local instance spaceAddCommGroup : AddCommGroup Space :=
  (inferInstance : NormedAddCommGroup Space).toAddCommGroup
local instance spaceModule : Module ℝ Space :=
  (inferInstance : NormedSpace ℝ Space).toModule
local instance spaceTopology : TopologicalSpace Space :=
  (inferInstance : PseudoMetricSpace Space).toUniformSpace.toTopologicalSpace
abbrev rotation := CounterexampleField.rotation
abbrev curl := CounterexampleField.curl
abbrev divergence := CounterexampleField.divergence

def projectionLinear : Space →ₗ[ℝ] Space where
  toFun x := WithLp.toLp 2 ![x 0, x 1, 0]
  map_add' x y := by ext j; fin_cases j <;> simp
  map_smul' t x := by ext j; fin_cases j <;> simp

def projection : Space →L[ℝ] Space := projectionLinear.toContinuousLinearMap

@[simp] theorem projection_zero (x : Space) : projection x 0 = x 0 := rfl
@[simp] theorem projection_one (x : Space) : projection x 1 = x 1 := rfl
@[simp] theorem projection_two (x : Space) : projection x 2 = 0 := rfl

@[simp] theorem rotation_projection (x : Space) : rotation (projection x) = rotation x := by
  ext j
  fin_cases j <;> rfl

def denominator (x : Space) : ℝ := 1 + ‖projection x‖ ^ 2

theorem denominator_coordinates (x : Space) :
    denominator x = 1 + (x 0)^2 + (x 1)^2 := by
  simp [denominator, EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
  ring

theorem denominator_pos (x : Space) : 0 < denominator x := by
  unfold denominator
  positivity

theorem one_le_denominator (x : Space) : 1 ≤ denominator x := by
  unfold denominator
  linarith [sq_nonneg ‖projection x‖]

def weight (x : Space) : ℝ := (denominator x)⁻¹

theorem weight_pos (x : Space) : 0 < weight x := inv_pos.mpr (denominator_pos x)
theorem weight_le_one (x : Space) : weight x ≤ 1 := by
  unfold weight
  exact inv_le_one_of_one_le₀ (one_le_denominator x)

def field (x : Space) : Space := CounterexampleField.field (projection x)

theorem field_eq_weight_rotation (x : Space) : field x = weight x • rotation x := by
  simp [field, CounterexampleField.field, CounterexampleField.denominator, denominator, weight]

theorem field_norm_le_half (x : Space) : ‖field x‖ ≤ 1 / 2 :=
  CounterexampleField.field_norm_le_half (projection x)

theorem field_components (x : Space) :
    field x 0 = -x 1 / (1 + (x 0)^2 + (x 1)^2) ∧
    field x 1 = x 0 / (1 + (x 0)^2 + (x 1)^2) ∧ field x 2 = 0 := by
  rw [field_eq_weight_rotation]
  simp [weight, denominator_coordinates, div_eq_mul_inv, mul_comm]

theorem field_tangent (x : Space) : inner ℝ (field x) x = 0 := by
  rw [field_eq_weight_rotation, real_inner_smul_left]
  have h : inner ℝ (rotation x) x = 0 := by
    simp [PiLp.inner_apply, Fin.sum_univ_succ]
    ring
  rw [h, mul_zero]

theorem contDiff_field : ContDiff ℝ ∞ field :=
  CounterexampleMagneticField.contDiff_field.comp projection.contDiff

theorem differentiable_field : Differentiable ℝ field := contDiff_field.differentiable (by simp)

theorem contDiff_denominator : ContDiff ℝ ∞ denominator :=
  contDiff_const.add ((contDiff_norm_sq ℝ).comp projection.contDiff)

theorem contDiff_weight : ContDiff ℝ ∞ weight :=
  contDiff_denominator.inv (fun x => (denominator_pos x).ne')

theorem field_memLp_top : MemLp field ⊤ volume :=
  memLp_top_of_bound contDiff_field.continuous.aestronglyMeasurable
    (1 / 2) (ae_of_all _ field_norm_le_half)

theorem weight_memLp_top : MemLp weight ⊤ volume :=
  memLp_top_of_bound contDiff_weight.continuous.aestronglyMeasurable 1
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_pos (weight_pos x)]; exact weight_le_one x)

theorem hasFDerivAt_field (x : Space) :
    HasFDerivAt field
      (((denominator x)⁻¹ • rotation +
        ((-(denominator x ^ 2)⁻¹) • (2 • innerSL ℝ (projection x))).smulRight
          (rotation x)).comp projection) x := by
  convert (CounterexampleField.hasFDerivAt_field (projection x)).comp x
    projection.hasFDerivAt using 1 <;> try rfl

theorem divergence_field (x : Space) : divergence field x = 0 := by
  unfold divergence CounterexampleField.divergence
  rw [(hasFDerivAt_field x).fderiv]
  simp [Fin.sum_univ_succ, ContinuousLinearMap.smulRight_apply,
    PiLp.inner_apply, projection, projectionLinear,
    CounterexampleField.rotation, CounterexampleField.rotationLinear]
  ring

theorem curl_field (x : Space) :
    curl field x = (2 * weight x ^ 2) • EuclideanSpace.single 2 1 := by
  have hd := (denominator_pos x).ne'
  ext j
  fin_cases j
  all_goals
    simp [curl, CounterexampleField.curl, (hasFDerivAt_field x).fderiv,
      ContinuousLinearMap.smulRight_apply, PiLp.inner_apply, weight,
      projection, projectionLinear,
      CounterexampleField.rotation, CounterexampleField.rotationLinear,
      Fin.sum_univ_succ]
  simp [denominator, EuclideanSpace.norm_sq_eq, projection, projectionLinear,
    Fin.sum_univ_succ] at hd ⊢
  field_simp
  ring

theorem curl_field_third_pos (x : Space) : 0 < curl field x 2 := by
  rw [curl_field]
  simpa using (mul_pos (by norm_num : (0 : ℝ) < 2) (sq_pos_of_pos (weight_pos x)))

theorem curl_field_ne_zero (x : Space) : curl field x ≠ 0 := by
  intro h
  have hz := congrArg (fun y : Space => y 2) h
  exact (ne_of_gt (curl_field_third_pos x)) hz

def vectorPotential (t : ℝ) (x : Space) : Space := t • field x

theorem vectorPotential_norm_le (t : ℝ) (x : Space) :
    ‖vectorPotential t x‖ ≤ |t| / 2 := by
  rw [vectorPotential, norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (field_norm_le_half x) (abs_nonneg t)).trans_eq (by ring)

theorem contDiff_vectorPotential (t : ℝ) : ContDiff ℝ ∞ (vectorPotential t) :=
  contDiff_field.const_smul t

theorem curl_vectorPotential (t : ℝ) (x : Space) :
    curl (vectorPotential t) x = t • curl field x := by
  have hd : fderiv ℝ (vectorPotential t) x = t • fderiv ℝ field x :=
    ((differentiable_field x).hasFDerivAt.const_smul t).fderiv
  ext j
  fin_cases j <;> simp [curl, CounterexampleField.curl, hd, mul_sub]

theorem magnetic_field (t : ℝ) (x : Space) :
    curl (vectorPotential t) x = (2 * t * weight x ^ 2) • EuclideanSpace.single 2 1 := by
  rw [curl_vectorPotential, curl_field, smul_smul]
  congr 1
  ring

theorem distinct_curls_at {s t : ℝ} (hst : s ≠ t) (x : Space) :
    curl (vectorPotential s) x ≠ curl (vectorPotential t) x := by
  rw [curl_vectorPotential, curl_vectorPotential]
  intro h
  have hz : (s - t) • curl field x = 0 := by rw [sub_smul, h, sub_self]
  exact hst (sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right (curl_field_ne_zero x)))

theorem distinct_magnetic_fields {s t : ℝ} (hst : s ≠ t) :
    curl (vectorPotential s) ≠ curl (vectorPotential t) := by
  intro h
  exact distinct_curls_at hst 0 (congrFun h 0)

def scalarPotential (Z t : ℝ) (x : Space) : ℝ :=
  -Z / ‖x‖ - t ^ 2 / 2 * ‖field x‖ ^ 2 + t * weight x ^ 2

theorem shifted_scalar_cancel (Z t : ℝ) (x : Space) :
    scalarPotential Z t x + ‖vectorPotential t x‖ ^ 2 / 2 =
      -Z / ‖x‖ + t * weight x ^ 2 := by
  simp only [scalarPotential, vectorPotential, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem not_distributional_gauge_equivalent {s t : ℝ} (hst : s ≠ t) :
    ¬ CounterexampleMagneticField.IsDistributionalGradient
      (fun x => vectorPotential t x - vectorPotential s x) := by
  intro hg
  have he : (fun x => vectorPotential t x - vectorPotential s x) = vectorPotential (t - s) := by
    funext x
    simp [vectorPotential, sub_smul]
  rw [he] at hg
  have hz := CounterexampleMagneticField.curl_zero_of_distributional_gradient _
    (contDiff_vectorPotential (t - s)) hg
  obtain ⟨x, hx⟩ := hz.exists
  change curl (vectorPotential (t - s)) x = 0 at hx
  rw [curl_vectorPotential] at hx
  exact hst ((sub_eq_zero.mp ((smul_eq_zero.mp hx).resolve_right (curl_field_ne_zero x))).symm)

private def coordinateDerivative (f : Space → ℝ) (j : Fin 3) (x : Space) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.single j 1)

private theorem partial_contDiff {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (j : Fin 3) :
    ContDiff ℝ ∞ (coordinateDerivative f j) :=
  (contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const

private theorem integral_partial_mul {f : Space → ℝ} (hf : ContDiff ℝ ∞ f)
    {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) (j : Fin 3) :
    (∫ x, coordinateDerivative f j x * φ x) = -(∫ x, f x * coordinateDerivative φ j x) := by
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure Space))
    (((partial_contDiff hf j).continuous.mul hφ.continuous).integrable_of_hasCompactSupport
      hs.mul_left)
    ((hf.continuous.mul (partial_contDiff hφ j).continuous).integrable_of_hasCompactSupport
      (hs.fderiv_apply ℝ (EuclideanSpace.single j 1)).mul_left)
    ((hf.continuous.mul hφ.continuous).integrable_of_hasCompactSupport hs.mul_left)
    (fun x _ => hf.differentiable (by simp) x)
    (fun x _ => hφ.differentiable (by simp) x)
  change (∫ x, f x * coordinateDerivative φ j x) = -(∫ x, coordinateDerivative f j x * φ x) at h
  linarith

/-- The classical divergence of the smooth field is also its distributional
divergence. This gives the local regularity used in the HK hypotheses. -/
theorem weakDivergence_vectorPotential (t : ℝ) :
    FriedrichsDivergenceBackground.WeakDivergence
      (fun j x => vectorPotential t x j) (fun _ => 0) := by
  intro φ hφ hs
  have hcoord (j : Fin 3) : ContDiff ℝ ∞ (fun x => vectorPotential t x j) :=
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff.comp (contDiff_vectorPotential t)
  have hpart (j : Fin 3) (x : Space) :
      coordinateDerivative (fun y => vectorPotential t y j) j x =
        fderiv ℝ (vectorPotential t) x (EuclideanSpace.single j 1) j := by
    exact congrArg (fun L : Space →L[ℝ] ℝ => L (EuclideanSpace.single j 1))
      ((((EuclideanSpace.proj j : Space →L[ℝ] ℝ)).hasFDerivAt.comp x
        ((contDiff_vectorPotential t).differentiable (by simp) x).hasFDerivAt).fderiv)
  have hd (x : Space) : ∑ j : Fin 3, coordinateDerivative (fun y => vectorPotential t y j) j x = 0 := by
    have hdt : fderiv ℝ (vectorPotential t) x = t • fderiv ℝ field x :=
      ((differentiable_field x).hasFDerivAt.const_smul t).fderiv
    simp_rw [hpart, hdt]
    change ∑ j : Fin 3, t * fderiv ℝ field x (EuclideanSpace.single j 1) j = 0
    rw [← Finset.mul_sum]
    change t * divergence field x = 0
    rw [divergence_field, mul_zero]
  have hi (j : Fin 3) : Integrable
      (fun x => coordinateDerivative (fun y => vectorPotential t y j) j x * φ x) volume :=
    (((partial_contDiff (hcoord j) j).continuous).mul hφ.continuous).integrable_of_hasCompactSupport
      hs.mul_left
  have he : (∑ j : Fin 3, ∫ x, vectorPotential t x j * coordinateDerivative φ j x) = 0 := by
    have hh (j : Fin 3) := integral_partial_mul (hcoord j) hφ hs j
    have hj (j : Fin 3) : (∫ x, vectorPotential t x j * coordinateDerivative φ j x) =
        -(∫ x, coordinateDerivative (fun y => vectorPotential t y j) j x * φ x) := by linarith [hh j]
    simp_rw [hj]
    rw [Finset.sum_neg_distrib, ← integral_finsetSum]
    · simp_rw [← Finset.sum_mul, hd, zero_mul]
      simp
    · exact fun j _ => hi j
  change (∫ x, (0 : ℝ) * φ x) =
    -(∑ j : Fin 3, ∫ x, vectorPotential t x j * coordinateDerivative φ j x)
  rw [he]
  simp


end PfHk.SpinfulCounterexampleField
