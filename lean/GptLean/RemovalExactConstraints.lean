import GptLean.RemovalRealization
import GptLean.RemovalChannelConstraints

/-!
Exact removal from primitive source tests. The constraint data is built
from the very channel representatives used by the energy construction,
then transported through vacuum insertion. The output marginal is the
prepared hard marginal and its soft energy is zero.
-/

namespace GptLean.RemovalEnergy

open MeasureTheory Filter RemovalState RemovalConstruction RemovalConstraints
open scoped ENNReal Topology

variable {Q X J V H F T Hfull Tfull Marginal HardMarginal DensityTest CurrentTest : Type*}
  [MeasurableSpace Q] [MeasurableSpace X] {μ : Measure Q} {ν : Measure X}
  [IsProbabilityMeasure μ] [SFinite ν] [IsSeparable ν] [Fintype J]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  [NormedAddCommGroup Hfull] [InnerProductSpace ℂ Hfull]
  [NormedAddCommGroup Tfull] [NormedSpace ℝ Tfull] [CompleteSpace Tfull]
  [NormedAddCommGroup Marginal] [NormedSpace ℝ Marginal] [CompleteSpace Marginal]
  [NormedAddCommGroup HardMarginal] [NormedSpace ℝ HardMarginal]
  {basis : HilbertBasis ℕ ℂ V}
  {R : Gaussian.RankOneData (Lp H 2 ν) T} {Tr : PositiveTraceData T} {E : PositiveForm Tr}
  {Rfull : Gaussian.RankOneData Hfull Tfull} {Trfull : PositiveTraceData Tfull}
  {Efull : PositiveForm Trfull}
  {Cims C CZ Cv e k L a b Esoft : ℝ}
  (D : ChannelData (J := J) (F := F) basis R Tr E μ C CZ e k L a b)
  (hC : 0 ≤ C) (hCZ : 0 ≤ CZ) (he : 0 ≤ e) (hk : 0 ≤ k)

local notation "sourceData" => D.constraintRealization hC hCZ he hk
local notation "hardData" => D.momentData.vectorData hC hCZ he hk

/-- No final or conditional-output constraint is a premise. The local
Parseval/current series and the complete constraint data are constructed
inside this endpoint from rank-one forms and the original source sums. -/
noncomputable def ChannelData.exactOutput_of_source
    (hCims : 0 ≤ Cims) (hCv : 0 ≤ Cv)
    (vacuum : Lp H 2 ν →ₗᵢ[ℂ] Hfull)
    (hpositive : Rfull.positive ⊆ Trfull.positive) (htrace : Rfull.trace = Trfull.trace)
    (henergy : ∀ v, E.expectation (R.rankOne v) < ⊤ →
      Efull.expectation (Rfull.rankOne (vacuum v)) ≤ E.expectation (R.rankOne v) +
        ENNReal.ofReal ((Cv * e ^ 2 * b ^ 2) * ‖v‖ ^ 2))
    (m : Efull.State)
    (densityHard : DensityTest → T →L[ℝ] ℝ) (currentHard : CurrentTest → FormObservable E)
    (density : DensityTest → Tfull →L[ℝ] ℝ) (current : CurrentTest → FormObservable Efull)
    (hardMarginal : T →L[ℝ] HardMarginal) (prepareMarginal : HardMarginal →L[ℝ] Marginal)
    (marginal : Tfull →L[ℝ] Marginal) (hardTarget : HardMarginal)
    (weight : DensityTest → X → ℝ) (weightBound : DensityTest → ℝ)
    (weight_measurable : ∀ t, AEStronglyMeasurable (weight t) ν)
    (weightBound_nonneg : ∀ t, 0 ≤ weightBound t)
    (weight_bounded : ∀ t, ∀ᵐ x ∂ν, ‖weight t x‖ ≤ weightBound t)
    (density_rankOne : ∀ t (v : Lp H 2 ν), densityHard t (R.rankOne v) =
      ∫ x, weight t x * ‖v x‖ ^ 2 ∂ν)
    (dz : CurrentTest → ℕ → Q → X → V) (u : CurrentTest → ℕ → Q → X → H)
    (s : CurrentTest → ℕ → Q → X → ℝ)
    (dz_measurable : ∀ t i, ∀ᵐ q ∂μ, AEStronglyMeasurable (dz t i q) ν)
    (u_measurable : ∀ t i, ∀ᵐ q ∂μ, AEStronglyMeasurable (u t i q) ν)
    (connection : ∀ t i, ∀ᵐ q ∂μ, ∀ᵐ x ∂ν,
      inner ℂ ((sourceData).z i q x) (dz t i q x) = Complex.I * s t i q x)
    (kinetic_integrable : ∀ t i, ∀ᵐ q ∂μ, Integrable (fun x => ‖u t i q x‖ ^ 2 +
      2 * s t i q x * (inner ℂ (u t i q x) ((sourceData).source i q x)).re +
        ‖dz t i q x‖ ^ 2 * ‖(sourceData).source i q x‖ ^ 2) ν)
    (currentBound : CurrentTest → ℝ) (currentBound_nonneg : ∀ t, 0 ≤ currentBound t)
    (current_bound : ∀ t n x, x ∈ Tr.positive → E.expectation x < ⊤ →
      ‖(currentHard t).approximation n x‖ ≤
        currentBound t * (Tr.trace x + (E.expectation x).toReal))
    (current_rankOne : ∀ t i, ∀ᵐ q ∂μ, ∀ j,
      Tendsto (fun n => (currentHard t).approximation n (R.rankOne ((hardData).vector i j q)))
        atTop (𝓝 ((sourceData).currentVector (dz t) (u t) i j q)))
    (tests : ℕ → Marginal →L[ℝ] ℂ) (W : ℕ → H →L[ℂ] H)
    (separate : ∀ x y : Marginal, (∀ t, tests t x = tests t y) → x = y)
    (marginal_rankOne : ∀ t (v : Lp H 2 ν), tests t (prepareMarginal (hardMarginal (R.rankOne v))) =
      ∫ x, inner ℂ (v x) (W t (v x)) ∂ν)
    (density_source : ∀ t, HasSum
      (fun i => ∫ q, ∫ x, weight t x * ‖(sourceData).source i q x‖ ^ 2 ∂ν ∂μ)
      (density t m.val))
    (current_source : ∀ t, HasSum
      (fun i => ∫ q, (sourceData).currentSource (u t) (s t) i q ∂μ) ((current t).value m.val))
    (marginal_source : HasSum
      (fun i => ∫ q, prepareMarginal (hardMarginal (R.rankOne ((sourceData).sourceVector i q))) ∂μ)
      (prepareMarginal hardTarget))
    (density_vacuum : ∀ t v, density t (Rfull.rankOne (vacuum v)) = densityHard t (R.rankOne v))
    (current_vacuum : ∀ t v, E.expectation (R.rankOne v) < ⊤ →
      (current t).value (Rfull.rankOne (vacuum v)) = (currentHard t).value (R.rankOne v))
    (marginal_vacuum : ∀ v, marginal (Rfull.rankOne (vacuum v)) =
      prepareMarginal (hardMarginal (R.rankOne v)))
    (fullCurrentBound : CurrentTest → ℝ) (fullCurrentBound_nonneg : ∀ t, 0 ≤ fullCurrentBound t)
    (full_current_bound : ∀ t n x, x ∈ Trfull.positive → Efull.expectation x < ⊤ →
      ‖(current t).approximation n x‖ ≤
        fullCurrentBound t * (Trfull.trace x + (Efull.expectation x).toReal))
    (hsoft : ∑' i, D.soft i = Esoft)
    (hims : ∑' i, D.input i ≤ (Efull.expectation m.val).toReal + Cims * (L ^ 2)⁻¹)
    (softForm : PositiveForm Trfull)
    (vacuum_zero : ∀ v, softForm.expectation (Rfull.rankOne (vacuum v)) = 0) :
    {out : SoftRemoval.LocalizedOutput (VectorData.model (testedPair density current)) m
      (fun s => marginal s.val) (prepareMarginal hardTarget) Esoft
      (removalConstant Cims C CZ Cv) e k L a b // softForm.expectation out.state.val = 0} := by
  let A := (sourceData).constraintData densityHard currentHard (prepareMarginal.comp hardMarginal)
    weight weightBound weight_measurable weightBound_nonneg weight_bounded density_rankOne
    dz u s dz_measurable u_measurable connection kinetic_integrable
    currentBound currentBound_nonneg current_bound current_rankOne tests W separate marginal_rankOne
    (fun t => density t m.val) (fun t => (current t).value m.val) (prepareMarginal hardTarget)
    density_source current_source marginal_source
  have hc : 0 ≤ Cv * e ^ 2 * b ^ 2 :=
    mul_nonneg (mul_nonneg hCv (sq_nonneg e)) (sq_nonneg b)
  let prepared := A.prepare vacuum hpositive htrace hc henergy density current marginal
    density_vacuum current_vacuum marginal_vacuum fullCurrentBound fullCurrentBound_nonneg
    full_current_bound
  refine ⟨D.localizedOutput hCims hC hCZ hCv he hk vacuum hpositive htrace henergy m
    density current marginal (prepareMarginal hardTarget) prepared hsoft hims, ?_⟩
  exact RemovalVacuum.prepared_soft_energy_zero hardData vacuum hpositive htrace hc henergy
    softForm vacuum_zero

end GptLean.RemovalEnergy
