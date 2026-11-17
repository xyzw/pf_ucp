import GptLean.ElectronicH1Complex
import GptLean.SymmetricLift.WeakDerivativeClosure
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Function.L2Space

/-!
Electronic dilations on the actual H1 graph.

For `r > 0` and `d = card I`, the map `(S_r v)(x) = r^{d/2} v(r x)` is a
complex-linear isometry of electronic L², with inverse `S_{1/r}`. It
preserves the weak H1 graph, and the weak derivatives scale by `r`:

`∂ᵢ (S_r u) = r S_r (∂ᵢ u)`.

The proof moves the test function by `x ↦ x / r` with the Haar change of
variables. This is the electronic part of `prop-dilation-covariance`.
-/

noncomputable section

namespace GptLean.TransformationsDilation

open MeasureTheory ElectronicH1Space SymmetricLift Module
open scoped ENNReal ContDiff InnerProductSpace

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The normalization `r^{d/2}`. -/
def factor (I : Type*) [Fintype I] (r : ℝ) : ℝ := r ^ ((Fintype.card I : ℝ) / 2)

theorem finrank_euclidean : finrank ℝ (EuclideanSpace ℝ I) = Fintype.card I := finrank_euclideanSpace

theorem factor_sq {r : ℝ} (hr : 0 < r) : factor I r ^ 2 = r ^ (Fintype.card I) := by
  unfold factor
  rw [← Real.rpow_natCast (r ^ _) 2, ← Real.rpow_mul hr.le]
  norm_num

theorem factor_pos {r : ℝ} (hr : 0 < r) : 0 < factor I r := Real.rpow_pos_of_pos hr _

theorem factor_inv_mul {r : ℝ} (hr : 0 < r) : factor I r⁻¹ * factor I r = 1 := by
  unfold factor
  rw [Real.inv_rpow hr.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hr _).ne']

section General

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem comp_smul_aestronglyMeasurable {r : ℝ} (hr : 0 < r) (v : L2 F I) :
    AEStronglyMeasurable (fun x => v (r • x)) volume :=
  (Lp.aestronglyMeasurable v).comp_quasiMeasurePreserving
    (Measure.quasiMeasurePreserving_smul volume hr.ne')

theorem dilation_memLp {r : ℝ} (hr : 0 < r) (v : L2 F I) :
    MemLp (fun x => (factor I r : ℂ) • v (r • x)) 2 volume := by
  have hm : AEStronglyMeasurable (fun x => (factor I r : ℂ) • v (r • x)) volume :=
    aestronglyMeasurable_const.smul (comp_smul_aestronglyMeasurable hr v)
  refine (memLp_two_iff_integrable_sq_norm hm).mpr ?_
  have hi : Integrable (fun x => ‖v x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v)
  refine ((hi.comp_smul hr.ne').const_mul (factor I r ^ 2)).congr (ae_of_all _ fun x => ?_)
  simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

/-- The dilation `S_r` as a linear map of vector-valued electronic L². -/
def dilationLinear {r : ℝ} (hr : 0 < r) : L2 F I →ₗ[ℂ] L2 F I where
  toFun v := (dilation_memLp hr v).toLp _
  map_add' v w := by
    apply Lp.ext
    have hs := (Measure.quasiMeasurePreserving_smul volume hr.ne').ae_eq_comp (Lp.coeFn_add v w)
    filter_upwards [(dilation_memLp hr (v + w)).coeFn_toLp, (dilation_memLp hr v).coeFn_toLp,
      (dilation_memLp hr w).coeFn_toLp, hs,
      Lp.coeFn_add ((dilation_memLp hr v).toLp _) ((dilation_memLp hr w).toLp _)]
      with x h₁ h₂ h₃ h₄ h₅
    rw [h₁, h₅, Pi.add_apply, h₂, h₃]
    simp only [Function.comp_apply, Pi.add_apply] at h₄
    rw [h₄, smul_add]
  map_smul' c v := by
    apply Lp.ext
    have hs := (Measure.quasiMeasurePreserving_smul volume hr.ne').ae_eq_comp (Lp.coeFn_smul c v)
    filter_upwards [(dilation_memLp hr (c • v)).coeFn_toLp, (dilation_memLp hr v).coeFn_toLp, hs,
      Lp.coeFn_smul c ((dilation_memLp hr v).toLp _)] with x h₁ h₂ h₃ h₄
    rw [h₁, RingHom.id_apply, h₄, Pi.smul_apply, h₂]
    simp only [Function.comp_apply, Pi.smul_apply] at h₃
    rw [h₃, smul_comm]

theorem dilationLinear_ae {r : ℝ} (hr : 0 < r) (v : L2 F I) :
    dilationLinear hr v =ᵐ[volume] fun x => (factor I r : ℂ) • v (r • x) :=
  (dilation_memLp hr v).coeFn_toLp

theorem dilationLinear_inv {r : ℝ} (hr : 0 < r) (v : L2 F I) :
    dilationLinear (inv_pos.mpr hr) (dilationLinear hr v) = v := by
  apply Lp.ext
  have hs := (Measure.quasiMeasurePreserving_smul volume (inv_pos.mpr hr).ne').ae_eq_comp
    (dilationLinear_ae hr v)
  filter_upwards [dilationLinear_ae (inv_pos.mpr hr) (dilationLinear hr v), hs] with x h₁ h₂
  simp only [Function.comp_apply] at h₂
  rw [h₁, h₂, smul_smul, smul_smul, mul_inv_cancel₀ hr.ne', one_smul, ← Complex.ofReal_mul,
    factor_inv_mul hr, Complex.ofReal_one, one_smul]

end General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem l2_norm_sq (v : L2 E I) : ‖v‖ ^ 2 = ∫ x, ‖v x‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ) v, L2.inner_def,
    ← integral_re (L2.integrable_inner (𝕜 := ℂ) v v)]
  congr 1
  funext x
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) (v x)).symm

theorem norm_dilationLinear {r : ℝ} (hr : 0 < r) (v : L2 E I) :
    ‖dilationLinear hr v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [l2_norm_sq, l2_norm_sq]
  calc (∫ x, ‖dilationLinear hr v x‖ ^ 2) = ∫ x, factor I r ^ 2 * ‖v (r • x)‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [dilationLinear_ae hr v] with x hx
        rw [hx, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    _ = factor I r ^ 2 * ∫ x, ‖v (r • x)‖ ^ 2 := integral_const_mul _ _
    _ = ∫ x, ‖v x‖ ^ 2 := by
        rw [Measure.integral_comp_smul (volume : Measure (EuclideanSpace ℝ I)) (fun x => ‖v x‖ ^ 2) r,
          finrank_euclidean, factor_sq hr, smul_eq_mul, ← mul_assoc,
          abs_of_pos (inv_pos.mpr (pow_pos hr _)), mul_inv_cancel₀ (pow_pos hr _).ne', one_mul]

/-- The dilation `S_r` as a linear isometry. -/
def dilation {r : ℝ} (hr : 0 < r) : L2 E I →ₗᵢ[ℂ] L2 E I :=
  { dilationLinear hr with norm_map' := norm_dilationLinear hr }

theorem dilation_ae {r : ℝ} (hr : 0 < r) (v : L2 E I) :
    dilation hr v =ᵐ[volume] fun x => (factor I r : ℂ) • v (r • x) :=
  dilationLinear_ae hr v

theorem dilation_inv {r : ℝ} (hr : 0 < r) (v : L2 E I) :
    dilation (inv_pos.mpr hr) (dilation hr v) = v := by
  apply Lp.ext
  have hs := (Measure.quasiMeasurePreserving_smul volume (inv_pos.mpr hr).ne').ae_eq_comp
    (dilation_ae hr v)
  filter_upwards [dilation_ae (inv_pos.mpr hr) (dilation hr v), hs] with x h₁ h₂
  simp only [Function.comp_apply] at h₂
  rw [h₁, h₂, smul_smul, smul_smul, mul_inv_cancel₀ hr.ne', one_smul, ← Complex.ofReal_mul,
    factor_inv_mul hr, Complex.ofReal_one, one_smul]

/-- The scaled derivative family of the dilated vector. -/
def dilatedDerivative {r : ℝ} (hr : 0 < r) (u : H1 E I) (i : I) : L2 E I :=
  r • dilation hr (derivative i u)

theorem test_integral {r : ℝ} (hr : 0 < r) (v : L2 E I) (φ : EuclideanSpace ℝ I → ℝ) :
    (∫ x, φ x • dilation hr v x) =
      (factor I r * (r ^ Fintype.card I)⁻¹) • ∫ y, φ (r⁻¹ • y) • v y := by
  calc (∫ x, φ x • dilation hr v x) = ∫ x, (factor I r : ℂ) • (φ (r⁻¹ • (r • x)) • v (r • x)) := by
        apply integral_congr_ae
        filter_upwards [dilation_ae hr v] with x hx
        rw [hx, inv_smul_smul₀ hr.ne', smul_comm]
    _ = (factor I r : ℂ) • ∫ x, φ (r⁻¹ • (r • x)) • v (r • x) := integral_smul _ _
    _ = (factor I r : ℂ) • ((r ^ Fintype.card I)⁻¹ • ∫ y, φ (r⁻¹ • y) • v y) := by
        rw [Measure.integral_comp_smul (volume : Measure (EuclideanSpace ℝ I))
          (fun y => φ (r⁻¹ • y) • v y) r, finrank_euclidean,
          abs_of_pos (inv_pos.mpr (pow_pos hr _))]
    _ = _ := by
        rw [Complex.coe_smul, smul_smul]

theorem test_fderiv {r : ℝ} (φ : EuclideanSpace ℝ I → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (y w : EuclideanSpace ℝ I) :
    fderiv ℝ (fun z => φ (r⁻¹ • z)) y w = r⁻¹ * fderiv ℝ φ (r⁻¹ • y) w := by
  have h1 : HasFDerivAt (fun z : EuclideanSpace ℝ I => r⁻¹ • z)
      (r⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ I)) y :=
    (hasFDerivAt_id y).const_smul r⁻¹
  have h2 := (hφ.differentiable (by simp) (r⁻¹ • y)).hasFDerivAt.comp y h1
  change fderiv ℝ (φ ∘ fun z : EuclideanSpace ℝ I => r⁻¹ • z) y w = _
  rw [h2.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]

theorem weak_dilation {r : ℝ} (hr : 0 < r) (u : H1 E I) :
    HasWeakH1Local (dilation hr (value u)) (fun i => dilatedDerivative hr u i) := by
  refine ⟨fun K _ => (Lp.memLp _).restrict K, fun i K _ => (Lp.memLp _).restrict K, ?_⟩
  intro i φ hφ hs
  have hψ : ContDiff ℝ ∞ (fun y => φ (r⁻¹ • y)) := hφ.comp (contDiff_id.const_smul r⁻¹)
  have hψs : HasCompactSupport (fun y => φ (r⁻¹ • y)) :=
    hs.comp_homeomorph (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))
  have hw := (weak u).weak i (fun y => φ (r⁻¹ • y)) hψ hψs
  have hL : (∫ x, φ x • dilatedDerivative hr u i x) =
      r • ∫ x, φ x • dilation hr (derivative i u) x := by
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul r (dilation hr (derivative i u))] with x hx
    change φ x • (r • dilation hr (derivative i u) : L2 E I) x =
      r • (φ x • dilation hr (derivative i u) x)
    rw [hx, Pi.smul_apply, smul_comm]
  have hD : (∫ y, (fderiv ℝ (fun z => φ (r⁻¹ • z)) y (EuclideanSpace.single i 1)) • value u y) =
      r⁻¹ • ∫ y, (fderiv ℝ φ (r⁻¹ • y) (EuclideanSpace.single i 1)) • value u y := by
    rw [← integral_smul]
    apply integral_congr_ae
    refine ae_of_all _ fun y => ?_
    dsimp only
    rw [test_fderiv φ hφ y, mul_smul]
  rw [hL, test_integral hr, hw, hD, test_integral hr, smul_neg, smul_neg]
  congr 1
  rw [smul_comm r (factor I r * (r ^ Fintype.card I)⁻¹), smul_smul r r⁻¹, mul_inv_cancel₀ hr.ne',
    one_smul]

/-- The dilation on the complex electronic H1 graph. -/
def dilationH1 {r : ℝ} (hr : 0 < r) (u : ElectronicH1Complex.ComplexH1 E I) :
    ElectronicH1Complex.ComplexH1 E I :=
  ⟨(dilation hr (ElectronicH1Complex.value u),
      fun i => r • dilation hr (ElectronicH1Complex.derivative i u)),
    weak_dilation hr (ElectronicH1Complex.realEquiv u)⟩

@[simp] theorem value_dilationH1 {r : ℝ} (hr : 0 < r) (u : ElectronicH1Complex.ComplexH1 E I) :
    ElectronicH1Complex.value (dilationH1 hr u) = dilation hr (ElectronicH1Complex.value u) := rfl

@[simp] theorem derivative_dilationH1 {r : ℝ} (hr : 0 < r) (i : I)
    (u : ElectronicH1Complex.ComplexH1 E I) :
    ElectronicH1Complex.derivative i (dilationH1 hr u) =
      r • dilation hr (ElectronicH1Complex.derivative i u) := rfl

/-- The electronic kinetic energy scales quadratically. -/
theorem derivative_norm_dilationH1 {r : ℝ} (hr : 0 < r) (i : I)
    (u : ElectronicH1Complex.ComplexH1 E I) :
    ‖ElectronicH1Complex.derivative i (dilationH1 hr u)‖ ^ 2 =
      r ^ 2 * ‖ElectronicH1Complex.derivative i u‖ ^ 2 := by
  rw [derivative_dilationH1, norm_smul, LinearIsometry.norm_map, Real.norm_eq_abs, mul_pow,
    sq_abs]

end GptLean.TransformationsDilation
