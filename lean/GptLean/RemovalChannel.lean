import GptLean.RemovalEnergy
import GptLean.Repair.ParameterSections

/-!
Actual parameter-dependent coordinate channels for exact removal. Vectors
are the L² classes of the constructed scalar multipliers times the source
wavefunction, with the zero convention only at exceptional parameters.
The full rank-one energy is evaluated from covariant product derivatives
and the radiation/Coulomb form components. All channel energy estimates,
integrable majorants and countable cap summability are then derived.
-/

namespace GptLean.RemovalEnergy

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter RemovalState RemovalConstruction Repair
open scoped ENNReal

variable {Q X J V H F T : Type*}
  [MeasurableSpace Q] [MeasurableSpace X] {μ : Measure Q} {ν : Measure X}
  [IsProbabilityMeasure μ] [SFinite ν] [IsSeparable ν] [Fintype J]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]

noncomputable def channelSection (basis : HilbertBasis ℕ ℂ V)
    (z : Q × X → V) (ψ : Q × X → H) (j : ℕ) (q : Q) : Lp H 2 ν :=
  toL2Section (μ := ν) (fun q x => coordinate basis (z (q, x)) j • ψ (q, x)) q

def sourceMass (ψ : Q × X → H) (q : Q) : ℝ := ∫ x, ‖ψ (q, x)‖ ^ 2 ∂ν

def sourceKinetic (u : J → Q × X → H) (ψ : Q × X → H)
    (s : J → Q × X → ℝ) (q : Q) : ℝ :=
  ∫ x, localShiftedKinetic (fun j => u j (q, x)) (ψ (q, x))
    (fun j => s j (q, x)) ∂ν

def sourceRest (r : Q × X → F) (q : Q) : ℝ := ∫ x, ‖r (q, x)‖ ^ 2 ∂ν

noncomputable def outputKinetic (basis : HilbertBasis ℕ ℂ V)
    (z : Q × X → V) (dz : J → Q × X → V)
    (u : J → Q × X → H) (ψ : Q × X → H) (q : Q) : ℝ :=
  ∫ x, localChannelKinetic basis (z (q, x)) (fun j => dz j (q, x))
    (fun j => u j (q, x)) (ψ (q, x)) ∂ν

/-- The primitive fields of one conditional rank-one source. The remainder
`r` is the direct sum of the radiation and Coulomb square-root values.
It therefore transforms by the same scalar channel multiplier. -/
structure ChannelData (basis : HilbertBasis ℕ ℂ V)
    (R : Gaussian.RankOneData (Lp H 2 ν) T) (Tr : PositiveTraceData T)
    (E : PositiveForm Tr) (μ : Measure Q) (C CZ e k L a b : ℝ) where
  z : ℕ → Q × X → V
  dz : ℕ → J → Q × X → V
  u : ℕ → J → Q × X → H
  ψ : ℕ → Q × X → H
  s : ℕ → J → Q × X → ℝ
  rest : ℕ → Q × X → F
  z_measurable : ∀ i, StronglyMeasurable (z i)
  ψ_measurable : ∀ i, StronglyMeasurable (ψ i)
  dz_measurable : ∀ i j, AEStronglyMeasurable (dz i j) (μ.prod ν)
  u_measurable : ∀ i j, AEStronglyMeasurable (u i j) (μ.prod ν)
  s_measurable : ∀ i j, AEStronglyMeasurable (s i j) (μ.prod ν)
  rest_measurable : ∀ i, AEStronglyMeasurable (rest i) (μ.prod ν)
  unit : ∀ i, ∀ᵐ qx ∂μ.prod ν, ‖z i qx‖ = 1
  connection : ∀ i j, ∀ᵐ qx ∂μ.prod ν,
    inner ℂ (z i qx) (dz i j qx) = Complex.I * s i j qx
  source_integrable : ∀ i, Integrable (fun qx =>
    localShiftedKinetic (fun j => u i j qx) (ψ i qx) (fun j => s i j qx)) (μ.prod ν)
  mass_integrable : ∀ i, Integrable (fun qx => ‖ψ i qx‖ ^ 2) (μ.prod ν)
  rest_integrable : ∀ i, Integrable (fun qx => ‖rest i qx‖ ^ 2) (μ.prod ν)
  normalized : HasSum (fun i => ∫ q, sourceMass (ν := ν) (ψ i) q ∂μ) 1
  input : ℕ → ℝ
  soft : ℕ → ℝ
  soft_nonneg : ∀ i, 0 ≤ soft i
  input_summable : Summable input
  soft_summable : Summable soft
  source_energy : ∀ i,
    (∫ q, sourceKinetic (ν := ν) (u i) (ψ i) (s i) q + sourceRest (ν := ν) (rest i) q ∂μ) =
      input i - soft i
  fieldSize : ℕ → Q → ℝ
  field_nonneg : ∀ i q, 0 ≤ fieldSize i q
  field_measurable : ∀ i, AEStronglyMeasurable (fieldSize i) μ
  metric : ∀ i, ∀ᵐ qx ∂μ.prod ν, ∑ j, ‖dz i j qx‖ ^ 2 ≤
    2 * C * (e ^ 2 * L ^ 2 * fieldSize i qx.1 ^ 2 + e * fieldSize i qx.1)
  second_integrable : ∀ i, Integrable
    (fun q => sourceMass (ν := ν) (ψ i) q * fieldSize i q ^ 2) μ
  second_bound : ∀ i, (∫ q, sourceMass (ν := ν) (ψ i) q * fieldSize i q ^ 2 ∂μ) ≤
    CZ * k ^ 2 * (a ^ 2 * soft i + b ^ 2 * (∫ q, sourceMass (ν := ν) (ψ i) q ∂μ))
  rankOne_form : ∀ i j, ∀ᵐ q ∂μ,
    E.expectation (R.rankOne (channelSection (ν := ν) basis (z i) (ψ i) j q)) =
      ENNReal.ofReal ((∫ x, 1 / 2 * ∑ l,
        ‖channelDerivative basis (fun y => z i (q, y)) (fun y => dz i l (q, y))
          (fun y => u i l (q, y)) (fun y => ψ i (q, y)) j x‖ ^ 2 ∂ν) +
        (∫ x, ‖coordinate basis (z i (q, x)) j • rest i (q, x)‖ ^ 2 ∂ν))
  positive_compatible : R.positive ⊆ Tr.positive
  trace_compatible : R.trace = Tr.trace

namespace ChannelData

variable {basis : HilbertBasis ℕ ℂ V}
  {R : Gaussian.RankOneData (Lp H 2 ν) T} {Tr : PositiveTraceData T} {E : PositiveForm Tr}
  {C CZ e k L a b : ℝ} (D : ChannelData (J := J) (F := F) basis R Tr E μ C CZ e k L a b)

omit [IsProbabilityMeasure μ] [CompleteSpace H] [CompleteSpace T] in
theorem vector_measurable (i j : ℕ) :
    StronglyMeasurable (channelSection (ν := ν) basis (D.z i) (D.ψ i) j) := by
  exact stronglyMeasurable_toL2Section
    (((innerSL ℂ (basis j)).continuous.comp_stronglyMeasurable
      (D.z_measurable i)).smul (D.ψ_measurable i))

theorem mass_sum (i : ℕ) : ∀ᵐ q ∂μ,
    HasSum (fun j => ‖channelSection (ν := ν) basis (D.z i) (D.ψ i) j q‖ ^ 2)
      (sourceMass (ν := ν) (D.ψ i) q) := by
  filter_upwards [ae_ae_of_ae_prod (D.unit i), (D.mass_integrable i).prod_right_ae]
    with q hunit hmass
  have hz : AEStronglyMeasurable (fun x => D.z i (q, x)) ν :=
    ((D.z_measurable i).comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hψ : AEStronglyMeasurable (fun x => D.ψ i (q, x)) ν :=
    ((D.ψ_measurable i).comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  convert channelVector_mass basis hz hψ hunit hmass using 1
  · funext j
    rw [channelSection, toL2Section_eq
      (f := fun q x => coordinate basis (D.z i (q, x)) j • D.ψ i (q, x))
      (q := q) (channelValue_memLp basis hz hψ hunit hmass j)]
    rfl
  · rfl

omit [IsSeparable ν] [CompleteSpace H] [TopologicalSpace.SeparableSpace H] [CompleteSpace T] in
theorem local_energy (i : ℕ) : ∀ᵐ q ∂μ,
    Integrable (fun x => localChannelKinetic basis (D.z i (q, x))
      (fun j => D.dz i j (q, x)) (fun j => D.u i j (q, x)) (D.ψ i (q, x))) ν ∧
    outputKinetic (ν := ν) basis (D.z i) (D.dz i) (D.u i) (D.ψ i) q ≤
      localKineticMajorant (sourceKinetic (ν := ν) (D.u i) (D.ψ i) (D.s i))
        (sourceMass (ν := ν) (D.ψ i)) (D.fieldSize i) C e L q := by
  filter_upwards [ae_all_iff.mpr (fun j => (D.dz_measurable i j).prodMk_left),
    ae_all_iff.mpr (fun j => (D.u_measurable i j).prodMk_left),
    ae_all_iff.mpr (fun j => (D.s_measurable i j).prodMk_left),
    ae_ae_of_ae_prod (D.unit i),
    ae_all_iff.mpr (fun j => ae_ae_of_ae_prod (D.connection i j)),
    (D.source_integrable i).prod_right_ae, (D.mass_integrable i).prod_right_ae,
    ae_ae_of_ae_prod (D.metric i)] with q hdz hu hs hunit hc hsource hmass hm
  obtain ⟨hi, hb⟩ := localChannelKinetic_integrable_and_le basis hdz hu
    (((D.ψ_measurable i).comp_measurable
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable) hs hunit hc hsource hmass hm
  refine ⟨hi, hb.trans_eq ?_⟩
  dsimp [localKineticMajorant, sourceMass, sourceKinetic]
  ring

/-- No output energy series is assumed. It follows from the actual spatial
product derivatives and the scalar action on the other form components. -/
theorem form_series (i : ℕ) : ∀ᵐ q ∂μ,
    (∑' j, E.expectation (R.rankOne
      (channelSection (ν := ν) basis (D.z i) (D.ψ i) j q))) =
      ENNReal.ofReal (outputKinetic (ν := ν) basis (D.z i) (D.dz i) (D.u i) (D.ψ i) q +
        sourceRest (ν := ν) (D.rest i) q) := by
  filter_upwards [ae_all_iff.mpr (fun j => (D.dz_measurable i j).prodMk_left),
    ae_all_iff.mpr (fun j => (D.u_measurable i j).prodMk_left),
    (D.rest_measurable i).prodMk_left, ae_ae_of_ae_prod (D.unit i),
    ae_all_iff.mpr (fun j => ae_ae_of_ae_prod (D.connection i j)),
    D.local_energy i, (D.rest_integrable i).prod_right_ae,
    ae_all_iff.mpr (D.rankOne_form i)] with q hdz hu hr hunit hc hkin hrest hf
  exact channel_form_sum R E basis _
    (((D.z_measurable i).comp_measurable
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable) hdz hu
    (((D.ψ_measurable i).comp_measurable
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable) hr hunit hc hkin.1 hrest hf

/-- Construct the analytic ensemble interface from raw channel fields. -/
noncomputable def momentData : MomentData R Tr E μ C CZ e k L a b where
  vector i j := channelSection basis (D.z i) (D.ψ i) j
  measurable i j := (D.vector_measurable i j).aestronglyMeasurable
  mass i := sourceMass (D.ψ i)
  mass_nonneg _ _ := integral_nonneg (fun _ => sq_nonneg _)
  mass_sum := D.mass_sum
  mass_integrable i := (D.mass_integrable i).integral_prod_left
  normalized := D.normalized
  source i q := sourceKinetic (D.u i) (D.ψ i) (D.s i) q + sourceRest (D.rest i) q
  source_nonneg _ := Eventually.of_forall (fun _ =>
    add_nonneg (integral_nonneg (fun _ => localShiftedKinetic_nonneg _ _ _))
      (integral_nonneg (fun _ => sq_nonneg _)))
  source_integrable i := (D.source_integrable i).integral_prod_left.add
    (D.rest_integrable i).integral_prod_left
  input := D.input
  soft := D.soft
  soft_nonneg := D.soft_nonneg
  input_summable := D.input_summable
  soft_summable := D.soft_summable
  source_energy := D.source_energy
  fieldSize := D.fieldSize
  field_nonneg := D.field_nonneg
  field_measurable := D.field_measurable
  second_integrable := D.second_integrable
  second_bound := D.second_bound
  formEnergy i q := outputKinetic basis (D.z i) (D.dz i) (D.u i) (D.ψ i) q +
    sourceRest (D.rest i) q
  form_nonneg _ := Eventually.of_forall (fun _ =>
    add_nonneg (integral_nonneg (fun _ => localChannelKinetic_nonneg _ _ _ _ _))
      (integral_nonneg (fun _ => sq_nonneg _)))
  form_series := D.form_series
  kinetic_bound i := by
    filter_upwards [D.local_energy i] with q hq
    calc
      _ ≤ localKineticMajorant (sourceKinetic (D.u i) (D.ψ i) (D.s i))
          (sourceMass (D.ψ i)) (D.fieldSize i) C e L q + sourceRest (D.rest i) q :=
        add_le_add hq.2 le_rfl
      _ = _ := by dsimp [localKineticMajorant]; ring
  positive_compatible := D.positive_compatible
  trace_compatible := D.trace_compatible

end ChannelData
end
end GptLean.RemovalEnergy
