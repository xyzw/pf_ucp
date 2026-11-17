import GptLean.Gaussian.SpatialFieldIntegrability
import GptLean.Gaussian.SpatialFieldSmooth

/-!
Assembly of the spatial Gaussian field from actual cutoff kernels and the
standard first-chaos map. The only extra analytic background consists of
deterministic smooth-test density and deterministic local Sobolev embedding.
Joint representatives, samplewise local L² bounds, weak identities and the
common measurable smooth reconstruction are derived.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace GptLean.Gaussian

open MeasureTheory Filter GptLean.SymmetricLift
open scoped ENNReal Topology ContDiff

private theorem spatial_test_integrable {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : FieldSpace → E)
    (hf : ∀ K, IsCompact K → MemLp f 2 (volume.restrict K))
    (φ : FieldSpace → ℝ) (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Integrable (fun x => φ x • f x) volume :=
  integrable_smul_of_memLp_on_support
    ((hφ.memLp_of_hasCompactSupport hc).restrict (tsupport φ))
    (hf _ hc) (fun _x hx => image_eq_zero_of_notMem_tsupport hx)

/-- The Gaussian weak identities are proved simultaneously for all orders
and all compact smooth tests from the Bochner identities and joint versions. -/
theorem joint_field_hasWeakH1Local
    {Q : Type*} [MeasurableSpace Q] {μ : Measure Q} [IsFiniteMeasure μ]
    (core : CountableSpatialTestCore)
    (F : List (Fin 3) → FieldSpace → Lp ℝ 2 μ)
    (hF : ∀ ds, HasWeakH1Local (F ds) (fun j => F (j :: ds)))
    (field : List (Fin 3) → FieldSpace → Q → ℝ)
    (hm : ∀ ds, Measurable (Function.uncurry (field ds)))
    (heq : ∀ ds x, field ds x =ᵐ[μ] (F ds x : Q → ℝ))
    (C : List (Fin 3) → ℝ) (hC : ∀ ds, 0 ≤ C ds)
    (hbound : ∀ ds x, ‖F ds x‖ ≤ C ds) :
    ∀ᵐ q ∂μ, ∀ ds,
      HasWeakH1Local (fun x => field ds x q) (fun j x => field (j :: ds) x q) := by
  apply simultaneous_weakH1Local_of_countable_tests core field
  · exact ae_all_iff.mpr (fun ds => joint_L2_locally_memLp_ae
      (F ds) (field ds) (hm ds) (heq ds) (C ds) (hC ds) (hbound ds))
  · intro ds j n
    let φ := core.test n
    let δφ := fun x => fderiv ℝ φ x (EuclideanSpace.single j 1)
    have hφ : Continuous φ := (core.smooth n).continuous
    have hc : HasCompactSupport φ := core.compact n
    have hdφ : Continuous δφ :=
      ((core.smooth n).continuous_fderiv (by simp)).clm_apply continuous_const
    have hdc : HasCompactSupport δφ := hc.fderiv_apply ℝ _
    exact weak_identity_of_L2_identity (F ds) (F (j :: ds))
      (field ds) (field (j :: ds)) φ δφ
      (spatial_test_integrable _ (hF ds).function_memLp δφ hdφ hdc)
      (spatial_test_integrable _ (hF (j :: ds)).function_memLp φ hφ hc)
      (integrable_joint_test_of_uniform_L2 (F ds) (field ds) (hm ds) (heq ds)
        (C ds) (hC ds) (hbound ds) δφ (hdφ.integrable_of_hasCompactSupport hdc))
      (integrable_joint_test_of_uniform_L2 (F (j :: ds)) (field (j :: ds))
        (hm (j :: ds)) (heq (j :: ds)) (C (j :: ds)) (hC (j :: ds))
          (hbound (j :: ds)) φ (hφ.integrable_of_hasCompactSupport hc))
      (heq ds) (heq (j :: ds)) ((hF ds).weak j φ (core.smooth n) hc)

/-- A smooth spatial version remains a modification at every fixed spatial
point. This uses L² convergence of the same mollifiers and an almost
everywhere convergent subsequence, rather than evaluating an L² class. -/
theorem smooth_version_eq_L2_at_point
    {Q : Type*} [MeasurableSpace Q] {μ : Measure Q} [IsFiniteMeasure μ]
    (F : FieldSpace → Lp ℝ 2 μ) (hF : Continuous F)
    (field smooth : FieldSpace → Q → ℝ)
    (hm : Measurable (Function.uncurry field))
    (heq : ∀ x, field x =ᵐ[μ] (F x : Q → ℝ))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, ‖F x‖ ≤ C)
    (hgood : ∀ᵐ q ∂μ, Continuous (fun x => smooth x q) ∧
      (fun x => field x q) =ᵐ[volume] (fun x => smooth x q))
    (x : FieldSpace) : smooth x =ᵐ[μ] (F x : Q → ℝ) := by
  have hmol (n : ℕ) :
      (fun q => boundedMollification (fun y => field y q) n x) =ᵐ[μ]
        ((boundedMollification F n x : Lp ℝ 2 μ) : Q → ℝ) := by
    let φ := fun y : FieldSpace => (approximationBump 3 n).normed volume (x - y)
    have hφ : Continuous φ :=
      (approximationBump 3 n).continuous_normed.comp (continuous_const.sub continuous_id)
    have hc : HasCompactSupport φ :=
      (approximationBump 3 n).hasCompactSupport_normed.comp_homeomorph (Homeomorph.subLeft x)
    have hFi : Integrable (fun y => φ y • F y) volume :=
      (hφ.smul hF).integrable_of_hasCompactSupport hc.smul_right
    have hfeq (y : FieldSpace) : (fun q => φ y * field y q) =ᵐ[μ]
        (φ y • F y : Lp ℝ 2 μ) := by
      filter_upwards [heq y, Lp.coeFn_smul (φ y) (F y)] with q hq hs
      simpa [hq] using hs.symm
    exact integral_joint_L2_representative _ hFi (fun y q => φ y * field y q)
      (integrable_joint_test_of_uniform_L2 F field hm heq C hC hbound φ
        (hφ.integrable_of_hasCompactSupport hc)) hfeq
  have hlim : Tendsto (fun n => boundedMollification F n x) atTop (𝓝 (F x)) := by
    have h := ContDiffBump.convolution_tendsto_right_of_continuous
      (μ := volume) (approximationBump_rOut_tendsto 3) hF x
    simpa only [boundedMollification, smoothMollify, convolution_flip] using h
  obtain ⟨index, hindex, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  filter_upwards [hgood, hae, ae_all_iff.mpr hmol] with q hq hseq hmoll
  have hs : Tendsto (fun n => boundedMollification (fun y => field y q) n x)
      atTop (𝓝 (smooth x q)) := by
    have h := boundedMollification_tendsto_of_continuous hq.1 x
    exact h.congr (fun n => (boundedMollification_eq_of_ae_eq hq.2 n x).symm)
  exact tendsto_nhds_unique (hs.comp hindex.tendsto_atTop)
    (hseq.congr (fun n => (hmoll (index n)).symm))

/-- Actual cutoff Fourier kernels have a common jointly measurable smooth
Gaussian realization under the standard deterministic Sobolev background.
The output includes the original joint first-chaos versions and their
spatial almost-everywhere identification with the smooth version. -/
theorem exists_smooth_soft_field
    {Q Ω : Type*} [MeasurableSpace Q] [MeasurableSpace Ω]
    {μ : Measure Q} {ν : Measure Ω} [IsFiniteMeasure μ] [SFinite ν] [IsSeparable ν]
    (core : CountableSpatialTestCore) (sobolev : SmoothSobolevBackground)
    (T : Lp ℂ 2 ν →L[ℝ] Lp ℝ 2 μ)
    (momentum : Ω → FieldSpace) (hm : Measurable momentum)
    {k : ℝ} (hk : 0 ≤ k) (g : Ω → ℂ) (hg : Measurable g)
    (hbase : Integrable (fun y => ‖g y‖ ^ 2) ν) :
    ∃ field smooth : List (Fin 3) → FieldSpace → Q → ℝ,
      (∀ ds, Measurable (Function.uncurry (field ds))) ∧
      (∀ ds, Measurable (Function.uncurry (smooth ds))) ∧
      (∀ ds x, field ds x =ᵐ[μ]
        (T (softKernelL2 momentum hm ds hk g hg hbase x) : Q → ℝ)) ∧
      (∀ ds x, smooth ds x =ᵐ[μ]
        (T (softKernelL2 momentum hm ds hk g hg hbase x) : Q → ℝ)) ∧
      (∀ᵐ q ∂μ,
        (∀ ds, ContDiff ℝ ∞ (fun x => smooth ds x q)) ∧
        (∀ ds, (fun x => field ds x q) =ᵐ[volume] (fun x => smooth ds x q)) ∧
        (∀ ds j x, HasLineDerivAt ℝ (fun x => smooth ds x q)
          (smooth (j :: ds) x q) x (EuclideanSpace.single j 1))) := by
  obtain ⟨field, hmeas, heq⟩ := exists_joint_soft_field_representatives
    T momentum hm hk g hg hbase
  let F := fun ds x => T (softKernelL2 momentum hm ds hk g hg hbase x)
  let C := fun ds : List (Fin 3) => ‖T‖ * (k ^ ds.length *
    Real.sqrt (∫ y, ‖softBase momentum k g y‖ ^ 2 ∂ν))
  have hC : ∀ ds, 0 ≤ C ds := by intro ds; dsimp [C]; positivity
  have hbound : ∀ ds x, ‖F ds x‖ ≤ C ds := by
    intro ds x
    exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (norm_softKernelL2_le momentum hm ds hk g hg hbase x) (norm_nonneg _))
  have hweak := joint_field_hasWeakH1Local core F
    (fun ds => firstChaos_soft_field_hasWeakH1Local T momentum hm ds hk g hg hbase)
    field hmeas heq C hC hbound
  have hsmooth := smooth_spatial_representative_of_weak sobolev field hweak
  have hmod : ∀ ds x, smoothSpatialRepresentative field ds x =ᵐ[μ] (F ds x : Q → ℝ) := by
    intro ds x
    apply smooth_version_eq_L2_at_point (F ds)
      (T.continuous.comp (continuous_softKernelL2 momentum hm ds hk g hg hbase))
      (field ds) (smoothSpatialRepresentative field ds) (hmeas ds) (heq ds)
      (C ds) (hC ds) (hbound ds) _ x
    filter_upwards [hsmooth] with q hq
    exact ⟨(hq.1 ds).continuous, hq.2.1 ds⟩
  exact ⟨field, smoothSpatialRepresentative field, hmeas,
    jointly_measurable_smoothSpatialRepresentative field hmeas, heq, hmod, hsmooth⟩

end GptLean.Gaussian
