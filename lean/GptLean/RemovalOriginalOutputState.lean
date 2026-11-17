import GptLean.RemovalOriginalOutput

/- The exact endpoint uses the very prepared channel output. -/

noncomputable section

namespace GptLean.RemovalEnergy

open MeasureTheory Filter Repair RemovalState RemovalConstruction RemovalConstraints RemovalSource
open scoped ENNReal Topology

variable {Q I Ho H Hr F Hs V T Hfull Tfull Marginal HardMarginal DensityTest CurrentTest : Type*}
  [MeasurableSpace Q] {μ : Measure Q} [IsProbabilityMeasure μ] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Ho] [InnerProductSpace ℂ Ho]
  [NormedAddCommGroup Hr] [InnerProductSpace ℂ Hr]
  [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  [NormedAddCommGroup Hfull] [InnerProductSpace ℂ Hfull]
  [NormedAddCommGroup Tfull] [NormedSpace ℝ Tfull] [CompleteSpace Tfull]
  [NormedAddCommGroup Marginal] [NormedSpace ℝ Marginal] [CompleteSpace Marginal]
  [NormedAddCommGroup HardMarginal] [NormedSpace ℝ HardMarginal] [CompleteSpace HardMarginal]
  {basis : HilbertBasis ℕ ℂ V}
  {R : Gaussian.RankOneData (Lp H 2 (volume : Measure (SourceSpace I))) T}
  {Tr : PositiveTraceData T} {E : PositiveForm Tr}
  {Rfull : Gaussian.RankOneData Hfull Tfull} {Trfull : PositiveTraceData Tfull}
  {Efull : PositiveForm Trfull} {Cims C CZ Cv e k L a b : ℝ}
  (original : OriginalSource μ (volume : Measure (SourceSpace I)) I Ho H Hr F Hs)
  (D : ChannelData (J := I) (F := F) basis R Tr E μ C CZ e k L a b)
  {softField : ℕ → I → Q × SourceSpace I → ℝ}
  (link : PhysicalSourceLink original.conditionedSource D softField)

theorem ChannelData.exactOutput_original_state
    (hCims : 0 ≤ Cims) (hC : 0 ≤ C) (hCZ : 0 ≤ CZ) (hCv : 0 ≤ Cv)
    (he : 0 ≤ e) (hk : 0 ≤ k)
    {Rrad : H →ₗ.[ℂ] H} {A : I → SourceSpace I → H →ₗ.[ℂ] H}
    {B : SourceSpace I → H →ₗ.[ℂ] F}
    (P : original.conditionedSource.PFData Rrad A B e softField)
    (vacuum : Lp H 2 (volume : Measure (SourceSpace I)) →ₗᵢ[ℂ] Hfull)
    (hpositive : Rfull.positive ⊆ Trfull.positive) (htrace : Rfull.trace = Trfull.trace)
    (henergy : ∀ v, E.expectation (R.rankOne v) < ⊤ →
      Efull.expectation (Rfull.rankOne (vacuum v)) ≤ E.expectation (R.rankOne v) +
        ENNReal.ofReal ((Cv * e ^ 2 * b ^ 2) * ‖v‖ ^ 2))
    (m : Efull.State)
    (densityHard : DensityTest → T →L[ℝ] ℝ) (currentHard : CurrentTest → FormObservable E)
    (density : DensityTest → Tfull →L[ℝ] ℝ) (current : CurrentTest → FormObservable Efull)
    (hardMarginal : T →L[ℝ] HardMarginal) (prepareMarginal : HardMarginal →L[ℝ] Marginal)
    (marginal : Tfull →L[ℝ] Marginal) (hardTarget : HardMarginal)
    (tests : OriginalSourceTests original.wis original.vector original.covariant R hardMarginal
      (fun t => density t m.val) (fun t => (current t).value m.val) hardTarget)
    (density_rankOne : ∀ t (v : Lp H 2 (volume : Measure (SourceSpace I))),
      densityHard t (R.rankOne v) = ∫ x, (tests.density t).weight x * ‖v x‖ ^ 2)
    (hcanonical : RemovalPhysicalCurrent.CanonicalCurrent R Rrad A e currentHard
      (fun t => (tests.current t).weight) tests.direction)
    (currentBound : CurrentTest → ℝ) (currentBound_nonneg : ∀ t, 0 ≤ currentBound t)
    (current_bound : ∀ t n x, x ∈ Tr.positive → E.expectation x < ⊤ →
      ‖(currentHard t).approximation n x‖ ≤
        currentBound t * (Tr.trace x + (E.expectation x).toReal))
    (marginalTests : ℕ → Marginal →L[ℝ] ℂ) (W : ℕ → H →L[ℂ] H)
    (separate : ∀ x y : Marginal, (∀ t, marginalTests t x = marginalTests t y) → x = y)
    (marginal_rankOne : ∀ t (v : Lp H 2 (volume : Measure (SourceSpace I))),
      marginalTests t (prepareMarginal (hardMarginal (R.rankOne v))) =
        ∫ x, inner ℂ (v x) (W t (v x)))
    (density_vacuum : ∀ t v, density t (Rfull.rankOne (vacuum v)) = densityHard t (R.rankOne v))
    (current_vacuum : ∀ t v, E.expectation (R.rankOne v) < ⊤ →
      (current t).value (Rfull.rankOne (vacuum v)) = (currentHard t).value (R.rankOne v))
    (marginal_vacuum : ∀ v, marginal (Rfull.rankOne (vacuum v)) =
      prepareMarginal (hardMarginal (R.rankOne v)))
    (fullCurrentBound : CurrentTest → ℝ) (fullCurrentBound_nonneg : ∀ t, 0 ≤ fullCurrentBound t)
    (full_current_bound : ∀ t n x, x ∈ Trfull.positive → Efull.expectation x < ⊤ →
      ‖(current t).approximation n x‖ ≤
        fullCurrentBound t * (Trfull.trace x + (Efull.expectation x).toReal))
    (original_energy : original.energy = (Efull.expectation m.val).toReal)
    (localization_cost : (1 / 2 : ℝ) * ∑ j, original.metric j ≤ Cims * (L ^ 2)⁻¹)
    (softForm : PositiveForm Trfull)
    (vacuum_zero : ∀ v, softForm.expectation (Rfull.rankOne (vacuum v)) = 0) :
    (ChannelData.exactOutput_original original D link hCims hC hCZ hCv he hk P vacuum
        hpositive htrace henergy m densityHard currentHard density current hardMarginal prepareMarginal
        marginal hardTarget tests density_rankOne hcanonical currentBound currentBound_nonneg current_bound
        marginalTests W separate marginal_rankOne density_vacuum current_vacuum marginal_vacuum
        fullCurrentBound fullCurrentBound_nonneg full_current_bound original_energy localization_cost
        softForm vacuum_zero).val.state.val =
      (RemovalVacuum.prepareVectorData (D.momentData.vectorData hC hCZ he hk) vacuum
        hpositive htrace (mul_nonneg (mul_nonneg hCv (sq_nonneg e)) (sq_nonneg b)) henergy).output := rfl

end GptLean.RemovalEnergy
