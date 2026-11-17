import GptLean.RemovalGaussianChannel
import GptLean.RemovalPhysicalLink

/-! The kernel-based channel and the canonical current proof use the same
source, phase and coordinate derivatives. -/

noncomputable section
namespace GptLean.RemovalEnergy
open MeasureTheory Filter Repair SymmetricLift RemovalGeometry RemovalState Gaussian
open scoped ContDiff ENNReal

variable {Q G H F Hs Ω T ι : Type*} [MeasurableSpace Q] [MeasurableSpace Ω]
  {μ : Measure Q} {ν : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {N : ℕ}
local instance (G : SimpleGraph (Fin N)) : DecidableEq G.ConnectedComponent := Classical.decEq _
local instance (G : SimpleGraph (Fin N)) : Fintype G.ConnectedComponent := Fintype.ofFinite _

def physicalSourceLink_from_kernels
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
    PhysicalSourceLink S
      (physicalChannel_from_kernels S W D src momentum acut bcut hk hR he hC hkR
        sobolev c label kernels field B₀ B₁ basis index Rrad A B R₁ Tr E P hform
        hsupport hpositive htrace) (physicalSoftField (vectorField field.field [])) := by
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
  exact cluster_physicalSourceLink S B₀ B₁ basis index Rrad A B R₁ Tr E
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
