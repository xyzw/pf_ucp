import GptLean.RemovalOriginalSource
import GptLean.RemovalSourceLink
import GptLean.RemovalExactConstraints

/-!
Exact same-state removal from original spectral source data. The source
normalization, IMS sum, density, current and marginal series are derived.
The current uses the same PF source and weak derivative as the energy.
-/

noncomputable section

namespace GptLean.RemovalEnergy

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

open MeasureTheory MeasureTheory.Measure Filter Repair RemovalState RemovalConstruction RemovalConstraints RemovalSource
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

/-- This endpoint has no localized source sum, output current formula,
independent current derivative, or output-domain premise. -/
def ChannelData.exactOutput_original
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
    {out : SoftRemoval.LocalizedOutput (VectorData.model (testedPair density current)) m
      (fun s => marginal s.val) (prepareMarginal hardTarget) (∑' n, ‖original.soft n‖ ^ 2)
      (removalConstant Cims C CZ Cv) e k L a b // softForm.expectation out.state.val = 0} := by
  let w := fun n (qx : Q × SourceSpace I) => gaugePhase (link.phase n qx.1) qx.2
  have hw : ∀ n qx, ‖w n qx‖ = 1 := fun n qx => gaugePhase_norm _ _
  have hden (t : DensityTest) := original.density_source tests w hw t
  have hcur (t : CurrentTest) := original.current_source tests w D.s hw t
  have hmar := original.marginal_source tests w link.phase_measurable hw
  have hmarginal : HasSum
      (fun i => ∫ q, prepareMarginal (hardMarginal
        (R.rankOne ((D.constraintRealization hC hCZ he hk).sourceVector i q))) ∂μ)
      (prepareMarginal hardTarget) := by
    apply (prepareMarginal.hasSum hmar).congr_fun
    intro i
    have hm : MemLp (D.ψ i) 2 (μ.prod volume) :=
      (memLp_two_iff_integrable_sq_norm (D.ψ_measurable i).aestronglyMeasurable).mpr
        (D.mass_integrable i)
    have hφ := D.ψ_measurable i
    rw [link.source] at hm hφ
    change (∫ q, prepareMarginal (hardMarginal
      (R.rankOne (productSourceSection (ν := volume) (D.ψ i) q))) ∂μ) = _
    rw [link.source]
    exact prepareMarginal.integral_comp_comm
      (hardMarginal.integrable_comp (productSource_rankOne_integrable R hφ hm))
  have hims : (∑' i, D.input i) ≤ (Efull.expectation m.val).toReal + Cims * (L ^ 2)⁻¹ := by
    rw [link.input]
    exact original.input_bound.trans (by rw [original_energy]; exact add_le_add le_rfl localization_cost)
  have hsoft : (∑' i, D.soft i) = ∑' n, ‖original.soft n‖ ^ 2 := by
    rw [link.soft]
    exact original.soft_hasSum.tsum_eq
  apply D.exactOutput_of_source hC hCZ he hk hCims hCv vacuum hpositive htrace henergy m
    densityHard currentHard density current hardMarginal prepareMarginal marginal hardTarget
    (fun t => (tests.density t).weight) (fun t => (tests.density t).bound)
    (fun t => (tests.density t).weight_measurable) (fun t => (tests.density t).bound_nonneg)
    (fun t => (tests.density t).weight_bounded) density_rankOne
    (fun t n q x => ((tests.current t).weight x : ℂ) • D.dz n (tests.direction t) (q, x))
    (fun t n q x => ((tests.current t).weight x : ℂ) • D.u n (tests.direction t) (q, x))
    (fun t n q x => (tests.current t).weight x * D.s n (tests.direction t) (q, x))
    ?_ ?_ ?_ ?_ currentBound currentBound_nonneg current_bound
    (link.current_rankOne P currentHard (fun t => (tests.current t).weight) tests.direction
      hcanonical hC hCZ he hk) marginalTests W separate marginal_rankOne
    ?_ ?_ hmarginal density_vacuum current_vacuum marginal_vacuum
    fullCurrentBound fullCurrentBound_nonneg full_current_bound hsoft hims softForm vacuum_zero
  · intro t i
    filter_upwards [(D.dz_measurable i (tests.direction t)).prodMk_left] with q hq
    exact (Complex.continuous_ofReal.comp_aestronglyMeasurable (tests.current t).weight_measurable).smul hq
  · intro t i
    filter_upwards [(D.u_measurable i (tests.direction t)).prodMk_left] with q hq
    exact (Complex.continuous_ofReal.comp_aestronglyMeasurable (tests.current t).weight_measurable).smul hq
  · intro t i
    filter_upwards [ae_ae_of_ae_prod (D.connection i (tests.direction t))] with q hq
    exact hq.mono fun x hx => weighted_current_connection _ _ _ _ hx
  · intro t i
    exact D.weighted_current_kinetic_integrable (tests.current t).weight
      (tests.current t).weight_measurable (tests.current t).weight_bounded i (tests.direction t)
  · intro t
    change HasSum (fun i => ∫ q, ∫ x, (tests.density t).weight x * ‖D.ψ i (q, x)‖ ^ 2 ∂volume ∂μ) _
    rw [link.source]
    exact hden t
  · intro t
    change HasSum (fun i => ∫ q, (∫ x, inner ℂ (D.ψ i (q, x))
      (((tests.current t).weight x : ℂ) • D.u i (tests.direction t) (q, x)) +
        (((tests.current t).weight x * D.s i (tests.direction t) (q, x) : ℝ) : ℂ) *
        ‖D.ψ i (q, x)‖ ^ 2 ∂volume).re ∂μ) _
    rw [link.source, link.covariant]
    exact hcur t

end GptLean.RemovalEnergy
