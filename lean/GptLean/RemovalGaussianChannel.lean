import GptLean.RemovalPhysicalChannel
import GptLean.Gaussian.SpatialSingleSource
import GptLean.RemovalSourceSupport

/-!
The local channel moment is derived on the same WIS model as the source.
The Gaussian field is an actual joint smooth modification constructed
from the first-chaos map. Its cluster size is the measurable dense-ball
supremum, with a constant uniform in the source and localization cell.
-/

noncomputable section

namespace GptLean.RemovalEnergy

open MeasureTheory Filter Repair SymmetricLift RemovalGeometry RemovalState Gaussian
open scoped ContDiff ENNReal

variable {Q G : Type*} [MeasurableSpace Q] {μ : Measure Q}

/-- A spatial realization of the WIS coordinates, including all derivative
labels. The constructor below proves every property from first chaos. -/
structure SpatialWISField (coordinate : G → Q → ℝ)
    (label : Fin 3 → List (Fin 3) → FieldSpace → G) where
  field : Fin 3 → List (Fin 3) → FieldSpace → Q → ℝ
  measurable : ∀ i ds, Measurable (Function.uncurry (field i ds))
  modification : ∀ i ds x, field i ds x =ᵐ[μ] coordinate (label i ds x)
  smooth : ∀ q i,
    (∀ ds, ContDiff ℝ ∞ (fun x => field i ds x q)) ∧
    (∀ ds j x, HasLineDerivAt ℝ (fun x => field i ds x q)
      (field i (j :: ds) x q) x (EuclideanSpace.single j 1))

def SpatialWISField.ofFirstChaos
    {Hs K Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsFiniteMeasure μ] [SFinite ν] [IsSeparable ν]
    [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (W : WienerSegalData Q Hs K G μ)
    (core : CountableSpatialTestCore) (sobolev : SmoothSobolevBackground)
    (firstChaos : Lp ℂ 2 ν →L[ℝ] Lp ℝ 2 μ)
    (momentum : Ω → FieldSpace) (hm : Measurable momentum)
    {k : ℝ} (hk : 0 ≤ k) (base : Fin 3 → Ω → ℂ) (hg : ∀ i, Measurable (base i))
    (hbase : ∀ i, Integrable (fun y => ‖base i y‖ ^ 2) ν)
    (label : Fin 3 → List (Fin 3) → FieldSpace → G)
    (hfirst : ∀ i ds x,
      (firstChaos (softKernelL2 momentum hm ds hk (base i) (hg i) (hbase i) x) : Q → ℝ)
        =ᵐ[μ] W.coordinate (label i ds x)) : SpatialWISField (μ := μ) W.coordinate label := by
  let h := exists_smooth_wis_fields_everywhere W core sobolev
    firstChaos momentum hm hk base hg hbase label hfirst
  exact ⟨Classical.choose h, (Classical.choose_spec h).1,
    (Classical.choose_spec h).2.1, (Classical.choose_spec h).2.2⟩

variable {H F Hs Ω T ι : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
  [IsProbabilityMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {N : ℕ}

local instance (G : SimpleGraph (Fin N)) : DecidableEq G.ConnectedComponent := Classical.decEq _
local instance (G : SimpleGraph (Fin N)) : Fintype G.ConnectedComponent := Fintype.ofFinite _

def clusterGaussianConstant (N : ℕ) (C : ℝ) : ℝ :=
  72 * C * (117 * (N : ℝ)) ^ 2 * ((Real.pi * 4 / 3) * (6 + 12 * (N : ℝ)) ^ 3)

theorem clusterGaussianConstant_nonneg (N : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ clusterGaussianConstant N C := by unfold clusterGaussianConstant; positivity

def physicalFieldSize
    (field : Fin 3 → List (Fin 3) → FieldSpace → Q → ℝ)
    (c : ℕ → Fin N → ClusterSpace) (R : ℝ) (n : ℕ) : Q → ℝ :=
  clusterFieldSize field (physicalClusterCentre (c n) R) (clusterRadius N R)

theorem clusterComponent_card_le (c : Fin N → ClusterSpace) (R : ℝ) :
    Fintype.card (clusterGraph c R).ConnectedComponent ≤ N := by
  simpa only [Fintype.card_fin] using
    Fintype.card_le_of_surjective (clusterGraph c R).connectedComponentMk Quot.mk_surjective

/-- The source moment and norm identifications are the ordinary WIS and
radiation identities for the original vectors, before any repair. -/
structure GaussianSourceData
    (S : ConditionedSource μ (volume : Measure (Configuration N)) (Fin N × Fin 3) H F)
    (W : WienerSegalData Q Hs (Lp H 2 (volume : Measure (Configuration N))) G μ)
    {weight : Ω → ℝ} (D : KernelFieldData ν W weight) where
  vector : ℕ → Hs
  domain : ∀ n, D.radiationDomain (vector n)
  norm : ∀ n, ‖vector n‖ ^ 2 = ‖S.source n‖ ^ 2
  soft : ∀ n, ‖D.radiation (vector n)‖ ^ 2 = S.soft n
  mass : ∀ n, sourceMass (ν := volume) (S.source n) =ᵐ[μ]
    (fun q => ‖W.toFiber (vector n) q‖ ^ 2)

/-- Construct the common source identities from a single WIS unitary and
the usual Fubini representative identity. No conditional mass identity is
an additional hypothesis. -/
def GaussianSourceData.ofUnitary
    (S : ConditionedSource μ (volume : Measure (Configuration N)) (Fin N × Fin 3) H F)
    (W : WienerSegalData Q Hs (Lp H 2 (volume : Measure (Configuration N))) G μ)
    {weight : Ω → ℝ} (D : KernelFieldData ν W weight)
    (U : Hs ≃ₗᵢ[ℂ] Lp H 2 (μ.prod (volume : Measure (Configuration N))))
    (Fubini : Lp H 2 (μ.prod (volume : Measure (Configuration N))) ≃ₗᵢ[ℂ]
      Lp (Lp H 2 (volume : Measure (Configuration N))) 2 μ)
    (hrep : ∀ v : Lp H 2 (μ.prod (volume : Measure (Configuration N))), ∀ᵐ q ∂μ,
      (fun x => v (q, x)) =ᵐ[volume] (fun x => Fubini v q x))
    (hW : ∀ v, W.toFiber v =ᵐ[μ] (fun q => Fubini (U v) q))
    (hdom : ∀ n, D.radiationDomain (U.symm (S.source n)))
    (hrad : ∀ n, ‖D.radiation (U.symm (S.source n))‖ ^ 2 = S.soft n) :
    GaussianSourceData S W D where
  vector n := U.symm (S.source n)
  domain := hdom
  norm n := by rw [U.symm.norm_map]
  soft := hrad
  mass n := by
    filter_upwards [RemovalSource.product_sourceMass_fubini Fubini hrep (S.source n),
      hW (U.symm (S.source n))] with q hq hw
    simp only [U.apply_symm_apply] at hw
    exact hq.trans (congrArg (fun v => ‖v‖ ^ 2) hw.symm)

/-- Kernel moments produce the exact two source-moment inputs of the
physical channel, with one constant for every localization cell. -/
theorem GaussianSourceData.physical_moments
    {S : ConditionedSource μ (volume : Measure (Configuration N)) (Fin N × Fin 3) H F}
    {W : WienerSegalData Q Hs (Lp H 2 (volume : Measure (Configuration N))) G μ}
    {weight : Ω → ℝ} {D : KernelFieldData ν W weight}
    (src : GaussianSourceData S W D)
    (momentum : Ω → FieldSpace) {k R C : ℝ} (acut bcut : ℝ)
    (hk : 0 ≤ k) (hR : 0 < R) (hC : 0 ≤ C) (hkR : k * R ≤ 1)
    (sobolev : ScaledGradientSobolevBackground (6 + 12 * (N : ℝ)) C)
    (c : ℕ → Fin N → ClusterSpace) (base : Fin 3 → Ω → ℂ)
    (label : Fin 3 → List (Fin 3) → FieldSpace → G)
    (hkernel : ∀ i ds x,
      D.kernel (label i ds x) = softDerivativeKernel momentum ds k x (base i))
    (hbaseA : ∀ i, Integrable (fun y => weight y * ‖softBase momentum k (base i) y‖ ^ 2) ν)
    (hbaseB : ∀ i, Integrable (fun y => ‖softBase momentum k (base i) y‖ ^ 2) ν)
    (hmA : ∀ i ds x, AEStronglyMeasurable
      (fun y => weight y * ‖D.kernel (label i ds x) y‖ ^ 2) ν)
    (hmB : ∀ i ds x, AEStronglyMeasurable (fun y => ‖D.kernel (label i ds x) y‖ ^ 2) ν)
    (hcutA : ∀ i, (∫ y, weight y * ‖softBase momentum k (base i) y‖ ^ 2 ∂ν) ≤ acut ^ 2)
    (hcutB : ∀ i, (∫ y, ‖softBase momentum k (base i) y‖ ^ 2 ∂ν) ≤ bcut ^ 2)
    (hdom0 : D.radiationDomain 0) (hrad0 : D.radiation 0 = 0)
    (field : SpatialWISField (μ := μ) W.coordinate label) (n : ℕ) :
    Integrable (fun q => sourceMass (ν := volume) (S.source n) q *
      physicalFieldSize field.field c R n q ^ 2) μ ∧
    (∫ q, sourceMass (ν := volume) (S.source n) q * physicalFieldSize field.field c R n q ^ 2 ∂μ) ≤
      clusterGaussianConstant N C * k ^ 2 * (acut ^ 2 * S.soft n + bcut ^ 2 * ‖S.source n‖ ^ 2) := by
  obtain ⟨hi, hb⟩ := D.single_clusterFieldSize_moment_from_kernels momentum acut bcut N
    (clusterComponent_card_le (c n) R) hk hR hC hkR sobolev
    (physicalClusterCentre (c n) R) base label hkernel hbaseA hbaseB hmA hmB hcutA hcutB
    (src.vector n) (src.domain n) hdom0 hrad0 field.field field.measurable field.modification field.smooth
  have he : (fun q => sourceMass (ν := volume) (S.source n) q *
      physicalFieldSize field.field c R n q ^ 2) =ᵐ[μ]
      (fun q => ‖W.toFiber (src.vector n) q‖ ^ 2 * physicalFieldSize field.field c R n q ^ 2) :=
    (src.mass n).mono (fun q hq => congrArg
      (fun t : ℝ => t * physicalFieldSize field.field c R n q ^ 2) hq)
  refine ⟨hi.congr he.symm, ?_⟩
  rw [integral_congr_ae he]
  simpa only [physicalFieldSize, clusterRadius, clusterGaussianConstant, src.soft, src.norm] using hb

/-- Primitive cutoff-kernel data. All estimates concern one-photon
kernels, independently of any source state or removal construction. -/
structure RemovalKernelData
    (W : WienerSegalData Q Hs (Lp H 2 (volume : Measure (Configuration N))) G μ)
    {weight : Ω → ℝ} (D : KernelFieldData ν W weight)
    (momentum : Ω → FieldSpace) (k acut bcut : ℝ)
    (label : Fin 3 → List (Fin 3) → FieldSpace → G) where
  base : Fin 3 → Ω → ℂ
  kernel : ∀ i ds x, D.kernel (label i ds x) = softDerivativeKernel momentum ds k x (base i)
  weighted_integrable : ∀ i, Integrable (fun y => weight y * ‖softBase momentum k (base i) y‖ ^ 2) ν
  square_integrable : ∀ i, Integrable (fun y => ‖softBase momentum k (base i) y‖ ^ 2) ν
  weighted_measurable : ∀ i ds x, AEStronglyMeasurable
    (fun y => weight y * ‖D.kernel (label i ds x) y‖ ^ 2) ν
  square_measurable : ∀ i ds x, AEStronglyMeasurable (fun y => ‖D.kernel (label i ds x) y‖ ^ 2) ν
  cutoff_weighted : ∀ i, (∫ y, weight y * ‖softBase momentum k (base i) y‖ ^ 2 ∂ν) ≤ acut ^ 2
  cutoff_square : ∀ i, (∫ y, ‖softBase momentum k (base i) y‖ ^ 2 ∂ν) ≤ bcut ^ 2
  zero_domain : D.radiationDomain 0
  radiation_zero : D.radiation 0 = 0

/-- The common physical channel, now with its source-weighted Gaussian
moment derived from the actual cutoff kernels. The fields supplied by
`SpatialWISField.ofFirstChaos` and the source supplied by
`localizedConditionedSource` are used without replacement. -/
def physicalChannel_from_kernels
    (S : ConditionedSource μ (volume : Measure (Configuration N)) (Fin N × Fin 3) H F)
    (W : WienerSegalData Q Hs (Lp H 2 (volume : Measure (Configuration N))) G μ)
    {weight : Ω → ℝ} (D : KernelFieldData ν W weight)
    (src : GaussianSourceData S W D)
    (momentum : Ω → FieldSpace) {k R e C : ℝ} (acut bcut : ℝ)
    (hk : 0 ≤ k) (hR : 0 < R) (he : 0 ≤ e) (hC : 0 ≤ C) (hkR : k * R ≤ 1)
    (sobolev : ScaledGradientSobolevBackground (6 + 12 * (N : ℝ)) C)
    (c : ℕ → Fin N → ClusterSpace)
    (label : Fin 3 → List (Fin 3) → FieldSpace → G)
    (kernels : RemovalKernelData W D momentum k acut bcut label)
    (field : SpatialWISField (μ := μ) W.coordinate label)
    (B₀ : TensorBackground SixTag) (B₁ : TensorMultilinearData B₀)
    (basis : HilbertBasis ι ℂ (recursiveLiftCandidate B₀ N).target) (index : ι ↪ ℕ)
    (Rrad : H →ₗ.[ℂ] H) (A : (Fin N × Fin 3) → Configuration N → H →ₗ.[ℂ] H)
    (B : Configuration N → H →ₗ.[ℂ] F)
    (R₁ : Gaussian.RankOneData (Lp H 2 (volume : Measure (Configuration N))) T)
    (Tr : PositiveTraceData T) (E : PositiveForm Tr)
    (P : S.PFData Rrad A B e (physicalSoftField (vectorField field.field [])))
    (hform : HasPFFormEvaluation Rrad A B e (fun v => E.expectation (R₁.rankOne v)))
    (hsupport : ∀ n, ∀ᵐ qx ∂μ.prod volume, S.source n qx ≠ 0 →
      ∀ i : Fin N, ∃ j, dist (particle qx.2 i) (c n j) ≤ 4 * R)
    (hpositive : R₁.positive ⊆ Tr.positive) (htrace : R₁.trace = Tr.trace) :
    ChannelData (J := Fin N × Fin 3) (F := F) countableTargetBasis R₁ Tr E μ
      (clusterRepairMetricConstant N) (clusterGaussianConstant N C) e k R acut bcut := by
  have hmom (n : ℕ) := src.physical_moments momentum acut bcut hk hR hC hkR sobolev c
    kernels.base label kernels.kernel kernels.weighted_integrable kernels.square_integrable
    kernels.weighted_measurable kernels.square_measurable kernels.cutoff_weighted kernels.cutoff_square
    kernels.zero_domain kernels.radiation_zero field n
  have hfield (q : Q) (i : Fin 3) := field.smooth q i
  have hbound (n : ℕ) (q : Q) (s : (clusterGraph (c n) R).ConnectedComponent)
      (y : ClusterSpace) (hy : y ∈ Metric.ball (physicalClusterCentre (c n) R s) (clusterRadius N R)) :
      ‖fderiv ℝ (vectorField field.field [] q) y‖ ≤ physicalFieldSize field.field c R n q := by
    apply vectorField_fderiv_le_clusterFieldSize field.field q
      (fun i => (hfield q i).1) (fun i => (hfield q i).2)
      (physicalClusterCentre (c n) R) (by dsimp [clusterRadius]; positivity) s y
    exact Metric.mem_closedBall.mpr (Metric.mem_ball.mp hy).le
  exact cluster_physicalChannelData S B₀ B₁ basis index Rrad A B R₁ Tr E
    (clusterGaussianConstant N C) k acut bcut hR he c (vectorField field.field []) P hform
    (vectorField_jointly_measurable field.field field.measurable []).stronglyMeasurable
    (fun q => vectorField_contDiff field.field q [] (fun i => (hfield q i).1 []))
    (fun j => (vectorField_derivative_jointly_measurable field.field field.measurable
      (fun q i => (hfield q i).1) (fun q i => (hfield q i).2) [] j).stronglyMeasurable)
    (physicalFieldSize field.field c R)
    (fun n => clusterFieldSize_measurable field.field field.measurable _ _)
    (fun n q => clusterFieldSize_nonneg field.field _ _ q) hbound hsupport
    (fun n => (hmom n).1) (fun n => (hmom n).2) hpositive htrace

end GptLean.RemovalEnergy
