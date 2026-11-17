import GptLean.Gaussian.SpatialFieldRealization

/-! Conditional source moments of the constructed smooth modification.
The hypotheses identify its fixed-point coordinates with the standard WIS
coordinates. Joint measurability is used only for the constructed version. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace GptLean.Gaussian

open MeasureTheory Filter
open scoped ENNReal Topology ContDiff

/-- Standard first-chaos/WIS identification transfers the constructed
smooth field to the WIS coordinates, simultaneously for a finite component
family. The first-chaos premise is an L² coordinate identity, with no spatial
regularity or moment conclusion hidden in it. -/
theorem exists_smooth_wis_fields
    {I Q H K G Ω : Type*} [Fintype I]
    [MeasurableSpace Q] [MeasurableSpace Ω]
    {μ : Measure Q} {ν : Measure Ω} [IsFiniteMeasure μ] [SFinite ν] [IsSeparable ν]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (W : WienerSegalData Q H K G μ)
    (core : CountableSpatialTestCore) (sobolev : SmoothSobolevBackground)
    (T : Lp ℂ 2 ν →L[ℝ] Lp ℝ 2 μ)
    (momentum : Ω → FieldSpace) (hm : Measurable momentum)
    {k : ℝ} (hk : 0 ≤ k) (base : I → Ω → ℂ) (hg : ∀ i, Measurable (base i))
    (hbase : ∀ i, Integrable (fun y => ‖base i y‖ ^ 2) ν)
    (label : I → List (Fin 3) → FieldSpace → G)
    (hfirst : ∀ i ds x,
      (T (softKernelL2 momentum hm ds hk (base i) (hg i) (hbase i) x) : Q → ℝ)
        =ᵐ[μ] W.coordinate (label i ds x)) :
    ∃ field : I → List (Fin 3) → FieldSpace → Q → ℝ,
      (∀ i ds, Measurable (Function.uncurry (field i ds))) ∧
      (∀ i ds x, field i ds x =ᵐ[μ] W.coordinate (label i ds x)) ∧
      (∀ᵐ q ∂μ, ∀ i,
        (∀ ds, ContDiff ℝ ∞ (fun x => field i ds x q)) ∧
        (∀ ds j x, HasLineDerivAt ℝ (fun x => field i ds x q)
          (field i (j :: ds) x q) x (EuclideanSpace.single j 1))) := by
  classical
  choose raw field hraw hmfield hrawEq hfieldEq hsmooth using
    (fun i => exists_smooth_soft_field core sobolev T momentum hm hk (base i) (hg i) (hbase i))
  refine ⟨field, hmfield, fun i ds x => (hfieldEq i ds x).trans (hfirst i ds x), ?_⟩
  exact ae_all_iff.mpr (fun i => (hsmooth i).mono (fun q hq => ⟨hq.1, hq.2.2⟩))

/-- Remove one measurable null superset of the exceptional set for all
components and derivative orders. The zero modification is jointly
measurable, preserves every fixed-point coordinate, and is smooth literally
at every Gaussian point. -/
theorem everywhere_smooth_modification
    {I Q : Type*} [MeasurableSpace Q] {μ : Measure Q}
    (field : I → List (Fin 3) → FieldSpace → Q → ℝ)
    (hm : ∀ i ds, Measurable (Function.uncurry (field i ds)))
    (hsmooth : ∀ᵐ q ∂μ, ∀ i,
      (∀ ds, ContDiff ℝ ∞ (fun x => field i ds x q)) ∧
      (∀ ds j x, HasLineDerivAt ℝ (fun x => field i ds x q)
        (field i (j :: ds) x q) x (EuclideanSpace.single j 1))) :
    ∃ good : I → List (Fin 3) → FieldSpace → Q → ℝ,
      (∀ i ds, Measurable (Function.uncurry (good i ds))) ∧
      (∀ i ds x, good i ds x =ᵐ[μ] field i ds x) ∧
      (∀ q i,
        (∀ ds, ContDiff ℝ ∞ (fun x => good i ds x q)) ∧
        (∀ ds j x, HasLineDerivAt ℝ (fun x => good i ds x q)
          (good i (j :: ds) x q) x (EuclideanSpace.single j 1))) := by
  classical
  let P := fun q => ∀ i,
    (∀ ds, ContDiff ℝ ∞ (fun x => field i ds x q)) ∧
    (∀ ds j x, HasLineDerivAt ℝ (fun x => field i ds x q)
      (field i (j :: ds) x q) x (EuclideanSpace.single j 1))
  obtain ⟨N, hsub, hN, hnull⟩ := exists_measurable_superset_of_null
    (show μ {q | ¬ P q} = 0 from hsmooth)
  let good := fun i ds x q => if q ∈ N then (0 : ℝ) else field i ds x q
  refine ⟨good, ?_, ?_, ?_⟩
  · intro i ds
    exact measurable_const.ite (hN.preimage measurable_snd) (hm i ds)
  · intro i ds x
    filter_upwards [show ∀ᵐ q ∂μ, q ∉ N by
      rw [ae_iff]
      convert hnull using 1
      congr 1
      ext q
      simp] with q hq
    simp only [good, ite_eq_right hq]
  · intro q i
    by_cases hq : q ∈ N
    · refine ⟨?_, ?_⟩
      · intro ds
        simpa only [good, ite_eq_left hq] using (contDiff_const : ContDiff ℝ ∞ (fun _ : FieldSpace => (0 : ℝ)))
      · intro ds j x
        simpa only [good, ite_eq_left hq, HasLineDerivAt] using
          (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    · have hp : P q := by
        by_contra hn
        exact hq (hsub hn)
      simpa only [good, ite_eq_right hq] using hp i

/-! The all-point version used in measurable channel and phase formulas. -/

theorem exists_smooth_wis_fields_everywhere
    {I Q H K G Ω : Type*} [Fintype I]
    [MeasurableSpace Q] [MeasurableSpace Ω]
    {μ : Measure Q} {ν : Measure Ω} [IsFiniteMeasure μ] [SFinite ν] [IsSeparable ν]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (W : WienerSegalData Q H K G μ)
    (core : CountableSpatialTestCore) (sobolev : SmoothSobolevBackground)
    (T : Lp ℂ 2 ν →L[ℝ] Lp ℝ 2 μ)
    (momentum : Ω → FieldSpace) (hm : Measurable momentum)
    {k : ℝ} (hk : 0 ≤ k) (base : I → Ω → ℂ) (hg : ∀ i, Measurable (base i))
    (hbase : ∀ i, Integrable (fun y => ‖base i y‖ ^ 2) ν)
    (label : I → List (Fin 3) → FieldSpace → G)
    (hfirst : ∀ i ds x,
      (T (softKernelL2 momentum hm ds hk (base i) (hg i) (hbase i) x) : Q → ℝ)
        =ᵐ[μ] W.coordinate (label i ds x)) :
    ∃ field : I → List (Fin 3) → FieldSpace → Q → ℝ,
      (∀ i ds, Measurable (Function.uncurry (field i ds))) ∧
      (∀ i ds x, field i ds x =ᵐ[μ] W.coordinate (label i ds x)) ∧
      (∀ q i,
        (∀ ds, ContDiff ℝ ∞ (fun x => field i ds x q)) ∧
        (∀ ds j x, HasLineDerivAt ℝ (fun x => field i ds x q)
          (field i (j :: ds) x q) x (EuclideanSpace.single j 1))) := by
  obtain ⟨field, hmfield, hmod, hsmooth⟩ := exists_smooth_wis_fields W core sobolev
    T momentum hm hk base hg hbase label hfirst
  obtain ⟨good, hmgood, heq, hgood⟩ := everywhere_smooth_modification field hmfield hsmooth
  exact ⟨good, hmgood, fun i ds x => (heq i ds x).trans (hmod i ds x), hgood⟩

/-- The derivative labels are the ordinary Fréchet derivative coordinates. -/
theorem fderiv_coordinate_of_smooth_field
    (field : List (Fin 3) → FieldSpace → ℝ)
    (hs : ∀ ds, ContDiff ℝ ∞ (field ds))
    (hd : ∀ ds j x, HasLineDerivAt ℝ (field ds) (field (j :: ds) x)
      x (EuclideanSpace.single j 1)) (ds : List (Fin 3)) (j : Fin 3) (x : FieldSpace) :
    fderiv ℝ (field ds) x (EuclideanSpace.single j 1) = field (j :: ds) x :=
  (((hs ds).differentiable (by simp) x).hasFDerivAt.hasLineDerivAt _).unique (hd ds j x)

namespace KernelFieldData

variable {Q H K G Ω : Type*} [MeasurableSpace Q] [MeasurableSpace Ω]
  {μ : Measure Q} {ν : Measure Ω} [SFinite μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [NormedSpace ℝ K]
  {W : WienerSegalData Q H K G μ} {w : Ω → ℝ} (D : KernelFieldData ν W w)

omit [SFinite μ] in
/-- A fixed-point modification inherits the conditional second moment.
There is no spatial regularity or integrated-moment hypothesis. -/
theorem derivative_source_moment_of_modification
    (momentum : Ω → FieldSpace) (ds : List (Fin 3))
    {k : ℝ} (hk : 0 ≤ k) (x : FieldSpace) (base : Ω → ℂ) (g : G)
    (hkernel : D.kernel g = softDerivativeKernel momentum ds k x base)
    (hbaseA : Integrable (fun y => w y * ‖softBase momentum k base y‖ ^ 2) ν)
    (hbaseB : Integrable (fun y => ‖softBase momentum k base y‖ ^ 2) ν)
    (hmA : AEStronglyMeasurable (fun y => w y * ‖D.kernel g y‖ ^ 2) ν)
    (hmB : AEStronglyMeasurable (fun y => ‖D.kernel g y‖ ^ 2) ν)
    (ψ : ℕ → H) (hdom : ∀ n, D.radiationDomain (ψ n))
    (hE : Summable (fun n => ‖D.radiation (ψ n)‖ ^ 2))
    (hP : Summable (fun n => ‖ψ n‖ ^ 2))
    (f : Q → ℝ) (hf : f =ᵐ[μ] W.coordinate g) :
    Integrable (fun q => W.sourceMass ψ q * f q ^ 2) μ ∧
    (∫ q, W.sourceMass ψ q * f q ^ 2 ∂μ) ≤
      k ^ (2 * ds.length) * D.cutoffSourceCoefficient momentum k base ψ := by
  obtain ⟨hi, hb⟩ := D.derivative_source_moment_le momentum ds hk x base g
    hkernel hbaseA hbaseB hmA hmB ψ hdom hE hP
  have he : (fun q => W.sourceMass ψ q * f q ^ 2) =ᵐ[μ]
      (fun q => W.sourceMass ψ q * (W.coordinate g q) ^ 2) :=
    hf.mono (fun q hq => congrArg (fun a : ℝ => W.sourceMass ψ q * a ^ 2) hq)
  exact ⟨hi.congr he.symm, (integral_congr_ae he).trans_le hb⟩

/-- The derivative ball moment applies to the common smooth modification,
even if independently chosen WIS coordinates were not jointly measurable. -/
theorem derivative_ball_moment_of_modification
    (momentum : Ω → FieldSpace) (ds : List (Fin 3))
    {k L R : ℝ} (hk : 0 ≤ k) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (centre : FieldSpace) (base : Ω → ℂ) (label : FieldSpace → G)
    (hkernel : ∀ x, D.kernel (label x) = softDerivativeKernel momentum ds k x base)
    (hbaseA : Integrable (fun y => w y * ‖softBase momentum k base y‖ ^ 2) ν)
    (hbaseB : Integrable (fun y => ‖softBase momentum k base y‖ ^ 2) ν)
    (hmA : ∀ x, AEStronglyMeasurable (fun y => w y * ‖D.kernel (label x) y‖ ^ 2) ν)
    (hmB : ∀ x, AEStronglyMeasurable (fun y => ‖D.kernel (label x) y‖ ^ 2) ν)
    (ψ : ℕ → H) (hdom : ∀ n, D.radiationDomain (ψ n))
    (hE : Summable (fun n => ‖D.radiation (ψ n)‖ ^ 2))
    (hP : Summable (fun n => ‖ψ n‖ ^ 2))
    (f : FieldSpace → Q → ℝ) (hm : Measurable (Function.uncurry f))
    (heq : ∀ x, f x =ᵐ[μ] W.coordinate (label x)) :
    Integrable (fun q => ∫ x in Metric.ball centre (L * R),
      W.sourceMass ψ q * f x q ^ 2) μ ∧
    (∫ q, (∫ x in Metric.ball centre (L * R),
      W.sourceMass ψ q * f x q ^ 2) ∂μ) ≤
        R ^ (3 : ℤ) * k ^ (2 * ds.length) *
          ((Real.pi * 4 / 3) * L ^ 3 * D.cutoffSourceCoefficient momentum k base ψ) := by
  let σ : Measure FieldSpace := volume.restrict (Metric.ball centre (L * R))
  let : IsFiniteMeasure σ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hpoint (x : FieldSpace) := D.derivative_source_moment_of_modification
    momentum ds hk x base (label x) (hkernel x) hbaseA hbaseB (hmA x) (hmB x)
      ψ hdom hE hP (f x) (heq x)
  have hcoef := D.cutoffSourceCoefficient_nonneg momentum k base ψ
  obtain ⟨_, hi, hb⟩ := spatial_moment_integrable_and_le (σ := σ) (μ := μ)
    (fun x q => W.sourceMass ψ q * f x q ^ 2)
    (B := k ^ (2 * ds.length) * D.cutoffSourceCoefficient momentum k base ψ)
    (mul_nonneg (pow_nonneg hk _) hcoef)
    (by
      exact (W.sourceMass_integrable hP).aestronglyMeasurable.comp_snd.mul
        (hm.pow_const 2).stronglyMeasurable.aestronglyMeasurable)
    (fun _ q => mul_nonneg (W.sourceMass_nonneg ψ q) (sq_nonneg _))
    (fun x => (hpoint x).1) (fun x => (hpoint x).2)
  refine ⟨hi, hb.trans_eq ?_⟩
  dsimp [σ]
  rw [field_ball_volume centre hL hR]
  ring

end KernelFieldData

end GptLean.Gaussian
