import GptLean.Gaussian.SpatialField

/-! Product integrability and almost-everywhere local L² regularity of
the constructed joint representatives, derived from uniform L² bounds. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace GptLean.Gaussian

open MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace

variable {X Q : Type*} [MeasurableSpace X] [MeasurableSpace Q]
  {σ : Measure X} {μ : Measure Q} [SFinite σ] [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in
theorem integral_sq_joint_L2_representative (v : Lp ℝ 2 μ) (f : Q → ℝ)
    (heq : f =ᵐ[μ] (v : Q → ℝ)) :
    Integrable (fun q => f q ^ 2) μ ∧ (∫ q, f q ^ 2 ∂μ) = ‖v‖ ^ 2 := by
  have hf : MemLp f 2 μ := (Lp.memLp v).ae_eq heq.symm
  refine ⟨by simpa only [Real.norm_eq_abs, sq_abs] using
    (memLp_two_iff_integrable_sq_norm hf.1).mp hf, ?_⟩
  calc
    _ = ∫ q, inner ℝ (v q) (v q) ∂μ := by
      apply integral_congr_ae
      filter_upwards [heq] with q hq
      simp [hq, Real.norm_eq_abs, sq_abs]
    _ = inner ℝ v v := (L2.inner_def v v).symm
    _ = _ := real_inner_self_eq_norm_sq v

omit [SFinite σ] in
/-- A compactly supported spatial test is integrable against a joint field
once its Gaussian L² norms are uniformly bounded. More generally an L¹
spatial test suffices. -/
theorem integrable_joint_test_of_uniform_L2
    (F : X → Lp ℝ 2 μ) (f : X → Q → ℝ)
    (hm : Measurable (Function.uncurry f))
    (heq : ∀ x, f x =ᵐ[μ] (F x : Q → ℝ))
    (C : ℝ) (_hC : 0 ≤ C) (hbound : ∀ x, ‖F x‖ ≤ C)
    (φ : X → ℝ) (hφ : Integrable φ σ) :
    Integrable (fun z : X × Q => φ z.1 * f z.1 z.2) (σ.prod μ) := by
  have hfi (x : X) : Integrable (f x) μ :=
    ((Lp.memLp (F x)).integrable (by norm_num)).congr (heq x).symm
  have hnorm (x : X) : (∫ q, ‖f x q‖ ∂μ) ≤ μ.real Set.univ + C ^ 2 := by
    obtain ⟨hi, he⟩ := integral_sq_joint_L2_representative (F x) (f x) (heq x)
    calc
      _ ≤ ∫ q, 1 + f x q ^ 2 ∂μ := by
        apply integral_mono (hfi x).norm ((integrable_const (1 : ℝ)).add hi)
        intro q
        change ‖f x q‖ ≤ 1 + f x q ^ 2
        rw [Real.norm_eq_abs]
        nlinarith [sq_nonneg (|f x q| - 1), sq_abs (f x q)]
      _ = μ.real Set.univ + ‖F x‖ ^ 2 := by
        rw [integral_add (integrable_const _) hi, integral_const, he]
        simp
      _ ≤ _ := add_le_add le_rfl (pow_le_pow_left₀ (norm_nonneg _) (hbound x) 2)
  have hmeas : AEStronglyMeasurable
      (fun z : X × Q => φ z.1 * f z.1 z.2) (σ.prod μ) :=
    hφ.1.comp_fst.mul hm.stronglyMeasurable.aestronglyMeasurable
  apply (integrable_prod_iff hmeas).mpr
  refine ⟨Eventually.of_forall (fun x => (hfi x).const_mul (φ x)), ?_⟩
  apply (hφ.norm.mul_const (μ.real Set.univ + C ^ 2)).mono'
    hmeas.norm.integral_prod_right'
  filter_upwards with x
  have he : (∫ q, ‖φ x * f x q‖ ∂μ) = ‖φ x‖ * ∫ q, ‖f x q‖ ∂μ := by
    simp only [norm_mul]
    exact integral_const_mul _ _
  rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _)), he]
  exact mul_le_mul_of_nonneg_left (hnorm x) (norm_nonneg _)

/-- Uniform pointwise Gaussian L² bounds imply local L² regularity of
almost every spatial sample, with a single null set for all compact sets. -/
theorem joint_L2_locally_memLp_ae
    (F : FieldSpace → Lp ℝ 2 μ) (f : FieldSpace → Q → ℝ)
    (hm : Measurable (Function.uncurry f))
    (heq : ∀ x, f x =ᵐ[μ] (F x : Q → ℝ))
    (C : ℝ) (_hC : 0 ≤ C) (hbound : ∀ x, ‖F x‖ ≤ C) :
    ∀ᵐ q ∂μ, ∀ K, IsCompact K →
      MemLp (fun x => f x q) 2 (volume.restrict K) := by
  have hball (n : ℕ) : ∀ᵐ q ∂μ,
      MemLp (fun x => f x q) 2
        (volume.restrict (Metric.ball (0 : FieldSpace) (n : ℝ))) := by
    let σn := volume.restrict (Metric.ball (0 : FieldSpace) (n : ℝ))
    let : IsFiniteMeasure σn := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    have hpoint (x : FieldSpace) := integral_sq_joint_L2_representative (F x) (f x) (heq x)
    obtain ⟨hi, _, _⟩ := spatial_moment_integrable_and_le (σ := σn) (μ := μ)
      (fun x q => f x q ^ 2) (B := C ^ 2) (sq_nonneg _)
      (hm.pow_const 2).stronglyMeasurable.aestronglyMeasurable
      (fun _ _ => sq_nonneg _) (fun x => (hpoint x).1) (fun x => by
        rw [(hpoint x).2]
        exact pow_le_pow_left₀ (norm_nonneg _) (hbound x) 2)
    filter_upwards [hi.prod_left_ae] with q hq
    apply (memLp_two_iff_integrable_sq_norm
      ((hm.comp (measurable_id.prodMk measurable_const)).stronglyMeasurable.aestronglyMeasurable)).mpr
    convert! hq using 1
    ext x
    simp [Function.uncurry, Real.norm_eq_abs, sq_abs]
  filter_upwards [ae_all_iff.mpr hball] with q hq K hK
  obtain ⟨r, hr⟩ := hK.isBounded.subset_ball (0 : FieldSpace)
  obtain ⟨n, hn⟩ := exists_nat_gt r
  exact (hq n).mono_measure (Measure.restrict_mono
    (hr.trans (Metric.ball_subset_ball hn.le)) le_rfl)

end GptLean.Gaussian
