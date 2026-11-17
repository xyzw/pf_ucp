import GptLean.RemovalGaussianChannel
import GptLean.RemovalPhysicalLink
import GptLean.RemovalGaussianLink
import GptLean.RemovalCharacterOutput

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

theorem physicalChannel_character_from_kernels
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
    (hpositive : R₁.positive ⊆ Tr.positive) (htrace : R₁.trace = Tr.trace)
    (χ : Equiv.Perm (Fin N) → ℂ)
    (hsource : ∀ n, ∀ᵐ q ∂μ, HasElectronicCharacter (fun π => permuteConfiguration π) χ
      (fun x => S.source n (q, x))) :
    ∀ n, ∀ᵐ q ∂μ, ∀ j, HasElectronicCharacter (fun π => permuteConfiguration π) χ
      (((physicalChannel_from_kernels S W D src momentum acut bcut hk hR he hC hkR
        sobolev c label kernels field B₀ B₁ basis index Rrad A B R₁ Tr E P hform
        hsupport hpositive htrace).momentData.vectorData (clusterRepairMetricConstant_nonneg N)
        (clusterGaussianConstant_nonneg N hC) he hk).vector n j q) := by
  let channel := physicalChannel_from_kernels S W D src momentum acut bcut hk hR he hC hkR
        sobolev c label kernels field B₀ B₁ basis index Rrad A B R₁ Tr E P hform
        hsupport hpositive htrace
  let link := physicalSourceLink_from_kernels S W D src momentum acut bcut hk hR he hC hkR
        sobolev c label kernels field B₀ B₁ basis index Rrad A B R₁ Tr E P hform
        hsupport hpositive htrace
  have hzinv (n : ℕ) (π : Equiv.Perm (Fin N)) : ∀ᵐ x ∂volume, ∀ q,
      channel.z n (q, permuteConfiguration π x) = channel.z n (q, x) :=
    clusterChannelLift_permutation_ae B₀ basis index (c n) R e
      (physicalFieldSize field.field c R n) (vectorField field.field []) π
  have hphase (n : ℕ) (π : Equiv.Perm (Fin N)) (q : Q) (x : Configuration N) :
      link.phase n q (permuteConfiguration π x) = link.phase n q x :=
    configurationClusterPhase_permute (c n) R e (vectorField field.field [] q) π x
  exact link.channel_character χ hsource hzinv hphase
    (clusterRepairMetricConstant_nonneg N) (clusterGaussianConstant_nonneg N hC) he hk

end GptLean.RemovalEnergy
