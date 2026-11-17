import GptLean.RemovalPhysicalCurrentSource
import GptLean.RemovalCurrentTests

/-!
The physical source link records only how a channel was constructed from
its source and phase. Its current evaluation follows from universal PF
current evaluation and the channel's own weak derivative and metric.
-/

noncomputable section

namespace GptLean.RemovalEnergy

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

open MeasureTheory Filter Repair SymmetricLift RemovalState RemovalConstraints RemovalPhysicalCurrent
open scoped ContDiff Topology

variable {Q I H F T V Test : Type*} [MeasurableSpace Q] {μ : Measure Q}
  [IsProbabilityMeasure μ] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  {basis : HilbertBasis ℕ ℂ V}
  {R₁ : Gaussian.RankOneData (Lp H 2 (volume : Measure (SourceSpace I))) T}
  {Tr : PositiveTraceData T} {E : PositiveForm Tr} {C CZ e k L a b : ℝ}

structure PhysicalSourceLink
    (S : ConditionedSource μ (volume : Measure (SourceSpace I)) I H F)
    (D : ChannelData (J := I) (F := F) basis R₁ Tr E μ C CZ e k L a b)
    (softField : ℕ → I → Q × SourceSpace I → ℝ) where
  phase : ℕ → Q → SourceSpace I → ℝ
  phase_measurable : ∀ n, StronglyMeasurable
    (fun qx : Q × SourceSpace I => gaugePhase (phase n qx.1) qx.2)
  phase_smooth : ∀ n q, ContDiff ℝ ∞ (phase n q)
  phase_bound : ∀ n q, ∃ M : ℝ, ∀ j x,
    |fderiv ℝ (phase n q) x (EuclideanSpace.single j 1)| ≤ M
  source : D.ψ = S.phasedSource (fun n qx => gaugePhase (phase n qx.1) qx.2)
  covariant : D.u = S.phasedHardDerivative
    (fun n qx => gaugePhase (phase n qx.1) qx.2) D.s
  input : D.input = S.input
  soft : D.soft = S.soft
  weak : ∀ n, ∀ᵐ q ∂μ, HasWeakH1Local (fun x => D.z n (q, x))
    (fun j x => D.dz n j (q, x))
  cancellation : ∀ n j, ∀ᵐ qx ∂μ.prod volume, S.source n qx ≠ 0 →
    fderiv ℝ (phase n qx.1) qx.2 (EuclideanSpace.single j 1) + D.s n j qx =
      -e * softField n j qx

variable {S : ConditionedSource μ (volume : Measure (SourceSpace I)) I H F}
  {D : ChannelData (J := I) (F := F) basis R₁ Tr E μ C CZ e k L a b}
  {softField : ℕ → I → Q × SourceSpace I → ℝ}

theorem PhysicalSourceLink.current_rankOne (link : PhysicalSourceLink S D softField)
    {Rrad : H →ₗ.[ℂ] H} {A : I → SourceSpace I → H →ₗ.[ℂ] H}
    {B : SourceSpace I → H →ₗ.[ℂ] F}
    (P : S.PFData Rrad A B e softField)
    (current : Test → FormObservable E)
    (weight : Test → SourceSpace I → ℝ) (direction : Test → I)
    (hcanonical : CanonicalCurrent R₁ Rrad A e current weight direction)
    (hC : 0 ≤ C) (hCZ : 0 ≤ CZ) (he : 0 ≤ e) (hk : 0 ≤ k) :
    ∀ t n, ∀ᵐ q ∂μ, ∀ j,
      Tendsto (fun m => (current t).approximation m
        (R₁.rankOne ((D.momentData.vectorData hC hCZ he hk).vector n j q))) atTop
        (𝓝 ((D.constraintRealization hC hCZ he hk).currentVector
          (fun n q x => (weight t x : ℂ) • D.dz n (direction t) (q, x))
          (fun n q x => (weight t x : ℂ) • D.u n (direction t) (q, x)) n j q)) := by
  have hu (n : ℕ) : ∀ᵐ qx ∂μ.prod volume, ‖D.z n qx‖ ≤ 1 :=
    (D.unit n).mono (fun _ h => h.le)
  have hc := P.current_rankOne R₁ current weight direction hcanonical basis D.z D.dz
    link.phase D.s link.weak hu link.phase_smooth link.phase_bound link.cancellation
    (fun n q => 2 * C * (e ^ 2 * L ^ 2 * D.fieldSize n q ^ 2 + e * D.fieldSize n q)) D.metric
  intro t n
  filter_upwards [ae_all_iff.mpr (hc t n)] with q hq
  intro j
  change Tendsto (fun m => (current t).approximation m
    (R₁.rankOne (channelSection (ν := volume) basis (D.z n) (D.ψ n) j q))) atTop
      (𝓝 ((∫ x, inner ℂ
        (channelValue basis (fun y => D.z n (q, y)) (fun y => D.ψ n (q, y)) j x)
        (channelDerivative basis (fun y => D.z n (q, y))
          (fun y => (weight t y : ℂ) • D.dz n (direction t) (q, y))
          (fun y => (weight t y : ℂ) • D.u n (direction t) (q, y))
          (fun y => D.ψ n (q, y)) j x) ∂volume).re))
  rw [link.source, link.covariant]
  exact hq j

end GptLean.RemovalEnergy
