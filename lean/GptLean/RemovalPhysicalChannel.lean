import GptLean.RemovalPhysicalSource
import GptLean.RemovalClusterChannel
import GptLean.RemovalClusterPhase

/-!
One physical channel is assembled from the same conditioned source,
cluster field, phase, measured tensor lift, and PF form. The lift and its
derivatives are constructed here. No target-domain, target-energy,
normalization, connection, or lift-metric premise is used.
-/

noncomputable section

namespace GptLean.RemovalEnergy

open MeasureTheory Filter Repair SymmetricLift RemovalGeometry RemovalState
open scoped ContDiff ENNReal

variable {Q H F T ι : Type*} [MeasurableSpace Q] {μ : Measure Q}
  [IsProbabilityMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {N : ℕ}

def physicalSoftField (a : Q → ClusterSpace → ClusterSpace)
    (_n : ℕ) (j : Fin N × Fin 3) (qx : Q × Configuration N) : ℝ :=
  a qx.1 (particle qx.2 j.1) j.2

def physicalResidual (c : ℕ → Fin N → ClusterSpace) (R e : ℝ)
    (a : Q → ClusterSpace → ClusterSpace)
    (n : ℕ) (j : Fin N × Fin 3) (qx : Q × Configuration N) : ℝ :=
  clusterResidual (c n) R e (a qx.1) (particle qx.2 j.1) j.2

theorem physicalResidual_stronglyMeasurable
    (c : ℕ → Fin N → ClusterSpace) (R e : ℝ)
    {a : Q → ClusterSpace → ClusterSpace} (ha : StronglyMeasurable (Function.uncurry a))
    (n : ℕ) (j : Fin N × Fin 3) : StronglyMeasurable (physicalResidual c R e a n j) :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j.2).continuous.comp_stronglyMeasurable
    ((clusterResidual_jointly_stronglyMeasurable (c n) R e ha).comp_measurable
      (measurable_fst.prodMk
        ((particleLinear j.1).toContinuousLinearMap.continuous.measurable.comp measurable_snd)))

/-- Construct the physical analytic channel. The remaining second-moment
inputs refer only to the original source and Gaussian field size and are
provided by the kernel moment construction. -/
def cluster_physicalChannelData
    (S : ConditionedSource μ (volume : Measure (Configuration N)) (Fin N × Fin 3) H F)
    (B₀ : TensorBackground SixTag) (B₁ : TensorMultilinearData B₀)
    (basis : HilbertBasis ι ℂ (recursiveLiftCandidate B₀ N).target) (index : ι ↪ ℕ)
    (Rrad : H →ₗ.[ℂ] H) (A : (Fin N × Fin 3) → Configuration N → H →ₗ.[ℂ] H)
    (B : Configuration N → H →ₗ.[ℂ] F)
    (R₁ : Gaussian.RankOneData (Lp H 2 (volume : Measure (Configuration N))) T)
    (Tr : PositiveTraceData T) (E : PositiveForm Tr)
    {R e : ℝ} (CZ k acut bcut : ℝ) (hR : 0 < R) (he : 0 ≤ e)
    (c : ℕ → Fin N → ClusterSpace) (a : Q → ClusterSpace → ClusterSpace)
    (P : S.PFData Rrad A B e (physicalSoftField a))
    (hform : HasPFFormEvaluation Rrad A B e (fun v => E.expectation (R₁.rankOne v)))
    (ha : StronglyMeasurable (Function.uncurry a)) (hd : ∀ q, ContDiff ℝ ∞ (a q))
    (hda : ∀ j : Fin 3, StronglyMeasurable (fun qx : Q × ClusterSpace =>
      fderiv ℝ (a qx.1) qx.2 (EuclideanSpace.single j 1)))
    (Z : ℕ → Q → ℝ) (hZmeas : ∀ n, Measurable (Z n)) (hZ : ∀ n q, 0 ≤ Z n q)
    (hbound : ∀ n q s, ∀ y ∈ Metric.ball (physicalClusterCentre (c n) R s) (clusterRadius N R),
      ‖fderiv ℝ (a q) y‖ ≤ Z n q)
    (hsupport : ∀ n, ∀ᵐ qx ∂μ.prod volume, S.source n qx ≠ 0 →
      ∀ i : Fin N, ∃ j, dist (particle qx.2 i) (c n j) ≤ 4 * R)
    (hsecond : ∀ n, Integrable
      (fun q => sourceMass (ν := volume) (S.source n) q * Z n q ^ 2) μ)
    (hsecond_bound : ∀ n, (∫ q, sourceMass (ν := volume) (S.source n) q * Z n q ^ 2 ∂μ) ≤
      CZ * k ^ 2 * (acut ^ 2 * S.soft n + bcut ^ 2 * ‖S.source n‖ ^ 2))
    (hpositive : R₁.positive ⊆ Tr.positive) (htrace : R₁.trace = Tr.trace) :
    ChannelData (J := Fin N × Fin 3) (F := F) countableTargetBasis R₁ Tr E μ
      (clusterRepairMetricConstant N) CZ e k R acut bcut := by
  let z := fun n => Function.uncurry (clusterChannelLift B₀ basis index (c n) R e (Z n) a)
  let dz := fun n j => Function.uncurry (clusterChannelGradient B₀ basis index (c n) R e (Z n) a j)
  let φ := fun n q => configurationClusterPhase (c n) R e (a q)
  let w := fun n (qx : Q × Configuration N) => gaugePhase (φ n qx.1) qx.2
  let s := physicalResidual c R e a
  have hp (n : ℕ) := clusterChannel_properties B₀ B₁ basis index (c n) hR he μ
    (hZmeas n) (hZ n) ha hd hda (hbound n)
  have hw (n : ℕ) : StronglyMeasurable (w n) := by
    have hm := configurationClusterPhase_jointly_stronglyMeasurable (c n) R e ha
    exact ((Complex.continuous_exp.comp
      (Complex.continuous_ofReal.mul continuous_const)).comp_stronglyMeasurable hm)
  have hcancel (n : ℕ) (j : Fin N × Fin 3) :
      ∀ᵐ qx ∂μ.prod volume, S.source n qx ≠ 0 →
        fderiv ℝ (φ n qx.1) qx.2 (EuclideanSpace.single j 1) + s n j qx =
          -e * physicalSoftField a n j qx := by
    filter_upwards [hsupport n] with qx hx
    intro hn
    exact configurationClusterPhase_cancellation (c n) hR e (a qx.1) qx.2 j (hx hn j.1)
  have hweak (n : ℕ) : ∀ᵐ q ∂μ, HasWeakH1Local (fun x => z n (q, x))
      (fun j x => dz n j (q, x)) := Eventually.of_forall (hp n).2.2.1
  have hunit (n : ℕ) : ∀ᵐ qx ∂μ.prod volume, ‖z n qx‖ ≤ 1 :=
    (hp n).2.2.2.1.mono (fun _ h => h.le)
  have hφbound (n : ℕ) (q : Q) : ∃ C : ℝ, ∀ j x,
      |fderiv ℝ (φ n q) x (EuclideanSpace.single j 1)| ≤ C := by
    obtain ⟨C, _, hC⟩ := configurationClusterPhase_exists_derivative_bound (c n) hR e (a q)
    exact ⟨C, hC⟩
  exact S.channelData countableTargetBasis R₁ Tr E (clusterRepairMetricConstant N) CZ e k R acut bcut
    z dz w s (fun n => (hp n).1) (fun n j => ((hp n).2.1 j).aestronglyMeasurable)
    hw (fun n qx => gaugePhase_norm (φ n qx.1) qx.2)
    (fun n j => (physicalResidual_stronglyMeasurable c R e ha n j).aestronglyMeasurable)
    (fun n => (hp n).2.2.2.1) (fun n => (hp n).2.2.2.2.1)
    Z hZ (fun n => (hZmeas n).aestronglyMeasurable)
    (fun n => (hp n).2.2.2.2.2) hsecond hsecond_bound
    (P.rankOne_form R₁ Tr E hform countableTargetBasis z dz φ s hweak hunit
      (fun n q => configurationClusterPhase_contDiff (c n) R e (a q)) hφbound hcancel
      (fun n q => 2 * clusterRepairMetricConstant N * (e ^ 2 * R ^ 2 * Z n q ^ 2 + e * Z n q))
      (fun n => (hp n).2.2.2.2.2)) hpositive htrace

end GptLean.RemovalEnergy
