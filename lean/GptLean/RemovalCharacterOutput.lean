import GptLean.RemovalSourceLink
import GptLean.RemovalClusterSymmetry
import GptLean.RemovalSubspace

/-! Electronic character passes from the source through the very channel
used for energy and constraints, then through vacuum preparation and the
trace-norm aggregate. -/

noncomputable section

namespace GptLean.RemovalEnergy

open MeasureTheory MeasureTheory.Measure Filter Repair SymmetricLift RemovalState RemovalConstruction

variable {Q H F T V : Type*} [MeasurableSpace Q] {μ : Measure Q}
  [IsProbabilityMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  {N : ℕ} {basis : HilbertBasis ℕ ℂ V}
  {R₁ : Gaussian.RankOneData (Lp H 2 (volume : Measure (Configuration N))) T}
  {Tr : PositiveTraceData T} {E : PositiveForm Tr} {C CZ e k L a b : ℝ}
  {S : ConditionedSource μ (volume : Measure (Configuration N)) (Fin N × Fin 3) H F}
  {D : ChannelData (J := Fin N × Fin 3) (F := F) basis R₁ Tr E μ C CZ e k L a b}
  {softField : ℕ → (Fin N × Fin 3) → Q × Configuration N → ℝ}

theorem PhysicalSourceLink.channel_character
    (link : PhysicalSourceLink S D softField)
    (χ : Equiv.Perm (Fin N) → ℂ)
    (hsource : ∀ n, ∀ᵐ q ∂μ, HasElectronicCharacter
      (fun π => permuteConfiguration π) χ (fun x => S.source n (q, x)))
    (hlift : ∀ n π, ∀ᵐ x ∂volume, ∀ q,
      D.z n (q, permuteConfiguration π x) = D.z n (q, x))
    (hphase : ∀ n π q x, link.phase n q (permuteConfiguration π x) = link.phase n q x)
    (hC : 0 ≤ C) (hCZ : 0 ≤ CZ) (he : 0 ≤ e) (hk : 0 ≤ k) :
    ∀ n, ∀ᵐ q ∂μ, ∀ j, HasElectronicCharacter (fun π => permuteConfiguration π) χ
      ((D.momentData.vectorData hC hCZ he hk).vector n j q) := by
  intro n
  filter_upwards [hsource n, ConditionedSource.lp_sections_memLp (S.source n),
    ae_ae_of_ae_prod (D.unit n)] with q hχ hψ hunit
  intro j
  change HasElectronicCharacter (fun π => permuteConfiguration π) χ
    (channelSection (ν := volume) basis (D.z n) (D.ψ n) j q)
  rw [link.source]
  apply phase_channelSection_character χ basis (D.z n) (link.phase n) (S.source n) q
    (((D.z_measurable n).comp_measurable
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable) hunit
  · intro π
    exact (hlift n π).mono (fun x hx => hx q)
  · exact (link.phase_smooth n q).continuous.aestronglyMeasurable
  · intro π
    exact Eventually.of_forall (hphase n π q)
  · exact hψ
  · exact hχ

end GptLean.RemovalEnergy

namespace GptLean.RemovalVacuum

open MeasureTheory Filter RemovalState RemovalConstruction
open scoped ENNReal

variable {Q K H T U : Type*} [MeasurableSpace Q] {μ : Measure Q}
  [IsProbabilityMeasure μ]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
  {R : Gaussian.RankOneData K T} {Tr : PositiveTraceData T} {E : PositiveForm Tr}
  {Rfull : Gaussian.RankOneData H U} {Trfull : PositiveTraceData U} {Efull : PositiveForm Trfull}

theorem prepared_output_fixed_of_vector_property
    (D : VectorData R Tr E μ) (vacuum : K →ₗᵢ[ℂ] H)
    (hpositive : Rfull.positive ⊆ Trfull.positive) (htrace : Rfull.trace = Trfull.trace)
    {c : ℝ} (hc : 0 ≤ c)
    (henergy : ∀ v, E.expectation (R.rankOne v) < ⊤ →
      Efull.expectation (Rfull.rankOne (vacuum v)) ≤
        E.expectation (R.rankOne v) + ENNReal.ofReal (c * ‖v‖ ^ 2))
    (property : K → Prop) (P : U →L[ℝ] U)
    (hcompression : ∀ v, property v → P (Rfull.rankOne (vacuum v)) = Rfull.rankOne (vacuum v))
    (hvector : ∀ n, ∀ᵐ q ∂μ, ∀ j, property (D.vector n j q)) :
    P (prepareVectorData D vacuum hpositive htrace hc henergy).output =
      (prepareVectorData D vacuum hpositive htrace hc henergy).output := by
  apply VectorData.output_fixed
  intro n
  exact (hvector n).mono (fun q hq j => hcompression _ (hq j))

end GptLean.RemovalVacuum
