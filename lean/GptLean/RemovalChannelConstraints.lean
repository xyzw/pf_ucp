import GptLean.RemovalChannel
import GptLean.RemovalConstraints

/-!
The constraint realization belongs to the exact channel vectors used in
the energy construction. No separate output family or choice of L²
representatives is introduced for testing density and current.
-/

namespace GptLean.RemovalEnergy

open MeasureTheory MeasureTheory.Measure Filter RemovalState RemovalConstruction RemovalConstraints Repair
open scoped ENNReal

variable {Q X J V H F T : Type*}
  [MeasurableSpace Q] [MeasurableSpace X] {μ : Measure Q} {ν : Measure X}
  [IsProbabilityMeasure μ] [SFinite ν] [IsSeparable ν] [Fintype J]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {basis : HilbertBasis ℕ ℂ V}
  {R : Gaussian.RankOneData (Lp H 2 ν) T}
  {Tr : PositiveTraceData T} {E : PositiveForm Tr}
  {C CZ e k L a b : ℝ}

/-- The actual channel sections satisfy the representative hypotheses of
constraint assembly. Their exceptional-parameter zero convention is
removed only on the proved full-measure finite-mass set. -/
noncomputable def ChannelData.constraintRealization
    (D : ChannelData (J := J) (F := F) basis R Tr E μ C CZ e k L a b)
    (hC : 0 ≤ C) (hCZ : 0 ≤ CZ) (he : 0 ≤ e) (hk : 0 ≤ k) :
    ChannelRealization (D.momentData.vectorData hC hCZ he hk) basis where
  z i q x := D.z i (q, x)
  source i q x := D.ψ i (q, x)
  multiplier_measurable i q :=
    ((D.z_measurable i).comp_measurable
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  source_measurable i q :=
    ((D.ψ_measurable i).comp_measurable
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  unit i := ae_ae_of_ae_prod (D.unit i)
  source_integrable i := (D.mass_integrable i).prod_right_ae
  vector_rep i := by
    filter_upwards [ae_ae_of_ae_prod (D.unit i), (D.mass_integrable i).prod_right_ae]
      with q hunit hmass
    intro j
    have hz : AEStronglyMeasurable (fun x => D.z i (q, x)) ν :=
      ((D.z_measurable i).comp_measurable
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    have hψ : AEStronglyMeasurable (fun x => D.ψ i (q, x)) ν :=
      ((D.ψ_measurable i).comp_measurable
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    change (channelSection (ν := ν) basis (D.z i) (D.ψ i) j q : X → H) =ᵐ[ν]
      channelValue basis (fun x => D.z i (q, x)) (fun x => D.ψ i (q, x)) j
    rw [channelSection, toL2Section_eq
      (f := fun q x => coordinate basis (D.z i (q, x)) j • D.ψ i (q, x)) (q := q)
      (channelValue_memLp basis hz hψ hunit hmass j)]
    exact (channelValue_memLp basis hz hψ hunit hmass j).coeFn_toLp

end GptLean.RemovalEnergy
