import GptLean.RemovalChannel
import GptLean.RemovalConstraints

/-!
Common-state endpoint for exact soft removal. The constructed coordinate
channel, its energy majorant, and soft-vacuum insertion are composed with
rank-one constraint assembly. One constant absorbs the independent IMS,
repair, field-moment and vacuum constants.

This endpoint still requires `ChannelData` for the physical source and
the standard rank-one vacuum form and constraint evaluations. It does not
replace their physical realization by an axiom or assert that it exists.
-/

namespace GptLean.RemovalEnergy

open MeasureTheory RemovalState RemovalConstruction RemovalConstraints

/-- This constant does not involve the state, infrared cutoff or cluster scale. -/
noncomputable def removalConstant (Cims C CZ Cv : ℝ) : ℝ :=
  max Cims (max (C * max CZ (Real.sqrt CZ)) Cv)

theorem removalConstant_nonneg {Cims C CZ Cv : ℝ} (hims : 0 ≤ Cims) :
    0 ≤ removalConstant Cims C CZ Cv := hims.trans (le_max_left _ _)

section Endpoint

variable {Q X J V H F T Hfull Tfull Marginal DensityTest CurrentTest : Type*}
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
  {basis : HilbertBasis ℕ ℂ V}
  {R : Gaussian.RankOneData (Lp H 2 ν) T} {Tr : PositiveTraceData T} {E : PositiveForm Tr}
  {Rfull : Gaussian.RankOneData Hfull Tfull} {Trfull : PositiveTraceData Tfull}
  {Efull : PositiveForm Trfull}
  {Cims C CZ Cv e k L a b Esoft : ℝ}

/-- All output-level conclusions of free-scale exact removal are proved
for one state. The energy hypotheses are original-source IMS and the
standard vacuum rank-one form bound, not a completed output estimate.
-/
noncomputable def ChannelData.localizedOutput
    (D : ChannelData (J := J) (F := F) basis R Tr E μ C CZ e k L a b)
    (hCims : 0 ≤ Cims) (hC : 0 ≤ C) (hCZ : 0 ≤ CZ) (hCv : 0 ≤ Cv)
    (he : 0 ≤ e) (hk : 0 ≤ k)
    (vacuum : Lp H 2 ν →ₗᵢ[ℂ] Hfull)
    (hpositive : Rfull.positive ⊆ Trfull.positive) (htrace : Rfull.trace = Trfull.trace)
    (henergy : ∀ v, E.expectation (R.rankOne v) < ⊤ →
      Efull.expectation (Rfull.rankOne (vacuum v)) ≤ E.expectation (R.rankOne v) +
        ENNReal.ofReal ((Cv * e ^ 2 * b ^ 2) * ‖v‖ ^ 2))
    (m : Efull.State)
    (density : DensityTest → Tfull →L[ℝ] ℝ)
    (current : CurrentTest → FormObservable Efull)
    (marginal : Tfull →L[ℝ] Marginal) (target : Marginal)
    (A : ConstraintData
      (RemovalVacuum.prepareVectorData (D.momentData.vectorData hC hCZ he hk) vacuum
        hpositive htrace (mul_nonneg (mul_nonneg hCv (sq_nonneg e)) (sq_nonneg b)) henergy)
      density current marginal (fun t => density t m.val)
        (fun t => (current t).value m.val) target)
    (hsoft : ∑' i, D.soft i = Esoft)
    (hims : ∑' i, D.input i ≤ (Efull.expectation m.val).toReal + Cims * (L ^ 2)⁻¹) :
    SoftRemoval.LocalizedOutput (VectorData.model (testedPair density current)) m
      (fun s => marginal s.val) target Esoft (removalConstant Cims C CZ Cv) e k L a b := by
  apply A.localizedOutput m D.soft_nonneg D.input_summable D.soft_summable hsoft
  · exact hims.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right
      (le_max_left Cims _) (inv_nonneg.mpr (sq_nonneg L))))
  · intro i
    exact D.momentData.cap_integral_add_vacuum hC hCZ he hk
      ((le_max_left _ Cv).trans (le_max_right Cims _))
      ((le_max_right _ Cv).trans (le_max_right Cims _)) i

/-- The common output has exactly the free-scale bound used in the paper. -/
theorem localizedOutput_energy_bound
    {M Pair Marginal : Type*} {B : DFT.StateModel M Pair} {m : M}
    {marginal : M → Marginal} {target : Marginal}
    (out : SoftRemoval.LocalizedOutput B m marginal target Esoft
      (removalConstant Cims C CZ Cv) e k L a b)
    (hCims : 0 ≤ Cims) (he : 0 ≤ e) (hk : 0 ≤ k) :
    B.density out.state = B.density m ∧ marginal out.state = target ∧
      B.energy out.state ≤ B.energy m - Esoft +
        removalConstant Cims C CZ Cv *
          RemovalEstimates.scaleError e k L b (a ^ 2 * Esoft + b ^ 2) :=
  ⟨out.pair_eq, out.marginal_eq,
    out.energy_bound (removalConstant_nonneg hCims) he hk⟩

end Endpoint
end GptLean.RemovalEnergy
