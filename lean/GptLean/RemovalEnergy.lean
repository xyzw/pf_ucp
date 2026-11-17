import GptLean.RemovalConstruction
import GptLean.RemovalVacuum
import GptLean.Repair.LocalCost

/-!
Energy realization for the removal construction. The first result evaluates
the full countable channel from the actual covariant product derivatives and
the scalar action on the remaining form components. The later construction
derives the integrable and summable operator majorant from conditional source
energies and field moments. No finite-energy output is an input.
-/

namespace GptLean.RemovalEnergy

open MeasureTheory Filter RemovalState RemovalConstruction
open GptLean.Repair
open scoped ENNReal

variable {X V H F : Type*} [MeasurableSpace X] {ν : Measure X}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The radiation and Coulomb square-root components are unchanged by the
channel after summation. Their fibre space can be a Hilbert direct sum. -/
theorem preserved_form_hasSum (basis : HilbertBasis ℕ ℂ V)
    {z : X → V} {r : X → F}
    (hz : AEStronglyMeasurable z ν) (hr : AEStronglyMeasurable r ν)
    (hunit : ∀ᵐ x ∂ν, ‖z x‖ = 1)
    (hi : Integrable (fun x => ‖r x‖ ^ 2) ν) :
    HasSum (fun j => ∫ x, ‖coordinate basis (z x) j • r x‖ ^ 2 ∂ν)
      (∫ x, ‖r x‖ ^ 2 ∂ν) := by
  apply hasSum_integral_nonnegative
    (f := fun j x => ‖coordinate basis (z x) j • r x‖ ^ 2)
    (g := fun x => ‖r x‖ ^ 2)
    (fun j => ((coordinate_aestronglyMeasurable basis hz j).smul hr).norm.pow 2)
    (fun _ => Eventually.of_forall (fun _ => sq_nonneg _)) _ hi
  filter_upwards [hunit] with x hx
  change HasSum (fun j => ‖coordinate basis (z x) j • r x‖ ^ 2) (‖r x‖ ^ 2)
  simpa only [hx, one_pow, one_mul] using
    coordinate_smul_norm_sq_hasSum basis (z x) (r x)

/-- Exact rank-one form evaluation turns the pointwise channel calculation
into an unbounded operator energy sum. Finiteness is proved before converting
the series to a real value. -/
theorem channel_form_sum {J K T : Type*} [Fintype J]
    [NormedAddCommGroup K] [NormedAddCommGroup T]
    [NormedSpace ℝ T] [CompleteSpace T]
    (R : Gaussian.RankOneData K T) {Tr : PositiveTraceData T} (E : PositiveForm Tr)
    (basis : HilbertBasis ℕ ℂ V) (v : ℕ → K)
    {z : X → V} {dz : J → X → V} {u : J → X → H}
    {ψ : X → H} {s : J → X → ℝ} {r : X → F}
    (hz : AEStronglyMeasurable z ν)
    (hdz : ∀ j, AEStronglyMeasurable (dz j) ν)
    (hu : ∀ j, AEStronglyMeasurable (u j) ν)
    (hψ : AEStronglyMeasurable ψ ν) (hr : AEStronglyMeasurable r ν)
    (hunit : ∀ᵐ x ∂ν, ‖z x‖ = 1)
    (hconn : ∀ j, ∀ᵐ x ∂ν, inner ℂ (z x) (dz j x) = Complex.I * s j x)
    (hkin : Integrable (fun x => localChannelKinetic basis (z x)
      (fun j => dz j x) (fun j => u j x) (ψ x)) ν)
    (hrest : Integrable (fun x => ‖r x‖ ^ 2) ν)
    (hform : ∀ a, E.expectation (R.rankOne (v a)) =
      ENNReal.ofReal ((∫ x, 1 / 2 * ∑ j,
        ‖channelDerivative basis z (dz j) (u j) ψ a x‖ ^ 2 ∂ν) +
        (∫ x, ‖coordinate basis (z x) a • r x‖ ^ 2 ∂ν))) :
    (∑' a, E.expectation (R.rankOne (v a))) =
      ENNReal.ofReal ((∫ x, localChannelKinetic basis (z x)
        (fun j => dz j x) (fun j => u j x) (ψ x) ∂ν) +
        (∫ x, ‖r x‖ ^ 2 ∂ν)) := by
  have hk := integrated_localChannelKinetic basis hz hdz hu hψ hunit hconn hkin
  have hr' := preserved_form_hasSum basis hz hr hunit hrest
  simp_rw [hform]
  rw [← ENNReal.ofReal_tsum_of_nonneg _ (hk.add hr').summable, (hk.add hr').tsum_eq]
  intro a
  exact add_nonneg (integral_nonneg (fun _ => mul_nonneg (by norm_num)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))))
    (integral_nonneg (fun _ => sq_nonneg _))

section Moments

variable {Q K T : Type*} [MeasurableSpace Q] {μ : Measure Q}
  [IsProbabilityMeasure μ] [NormedAddCommGroup K]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : Gaussian.RankOneData K T} {Tr : PositiveTraceData T} {E : PositiveForm Tr}

/-- Conditional source data after electronic localization and WIS slicing.
The energy series is an exact rank-one form calculation, obtained from
`channel_form_sum`. The only inequality on the channel is its pointwise
metric estimate, represented here by the proved kinetic majorant.

This record is an intermediate analytic interface. Its field-moment and
source identities must be supplied by the spatial and physical realization.
-/
structure MomentData (R : Gaussian.RankOneData K T) (Tr : PositiveTraceData T)
    (E : PositiveForm Tr) (μ : Measure Q) (C CZ e k L a b : ℝ) where
  vector : ℕ → ℕ → Q → K
  measurable : ∀ i j, AEStronglyMeasurable (vector i j) μ
  mass : ℕ → Q → ℝ
  mass_nonneg : ∀ i q, 0 ≤ mass i q
  mass_sum : ∀ i, ∀ᵐ q ∂μ, HasSum (fun j => ‖vector i j q‖ ^ 2) (mass i q)
  mass_integrable : ∀ i, Integrable (mass i) μ
  normalized : HasSum (fun i => ∫ q, mass i q ∂μ) 1
  source : ℕ → Q → ℝ
  source_nonneg : ∀ i, ∀ᵐ q ∂μ, 0 ≤ source i q
  source_integrable : ∀ i, Integrable (source i) μ
  input : ℕ → ℝ
  soft : ℕ → ℝ
  soft_nonneg : ∀ i, 0 ≤ soft i
  input_summable : Summable input
  soft_summable : Summable soft
  source_energy : ∀ i, (∫ q, source i q ∂μ) = input i - soft i
  fieldSize : ℕ → Q → ℝ
  field_nonneg : ∀ i q, 0 ≤ fieldSize i q
  field_measurable : ∀ i, AEStronglyMeasurable (fieldSize i) μ
  second_integrable : ∀ i, Integrable (fun q => mass i q * fieldSize i q ^ 2) μ
  second_bound : ∀ i, (∫ q, mass i q * fieldSize i q ^ 2 ∂μ) ≤
    CZ * k ^ 2 * (a ^ 2 * soft i + b ^ 2 * (∫ q, mass i q ∂μ))
  formEnergy : ℕ → Q → ℝ
  form_nonneg : ∀ i, ∀ᵐ q ∂μ, 0 ≤ formEnergy i q
  form_series : ∀ i, ∀ᵐ q ∂μ,
    (∑' j, E.expectation (R.rankOne (vector i j q))) = ENNReal.ofReal (formEnergy i q)
  kinetic_bound : ∀ i, ∀ᵐ q ∂μ, formEnergy i q ≤
    localKineticMajorant (source i) (mass i) (fieldSize i) C e L q
  positive_compatible : R.positive ⊆ Tr.positive
  trace_compatible : R.trace = Tr.trace

namespace MomentData

variable {C CZ e k L a b : ℝ} (D : MomentData R Tr E μ C CZ e k L a b)

noncomputable def clusterMass (i : ℕ) : ℝ := ∫ q, D.mass i q ∂μ

noncomputable def coefficient (i : ℕ) : ℝ :=
  a ^ 2 * D.soft i + b ^ 2 * D.clusterMass i

omit [IsProbabilityMeasure μ] [CompleteSpace T] in
theorem clusterMass_nonneg (i : ℕ) : 0 ≤ D.clusterMass i :=
  integral_nonneg (D.mass_nonneg i)

omit [IsProbabilityMeasure μ] [CompleteSpace T] in
theorem coefficient_nonneg (i : ℕ) : 0 ≤ D.coefficient i :=
  add_nonneg (mul_nonneg (sq_nonneg _) (D.soft_nonneg i))
    (mul_nonneg (sq_nonneg _) (D.clusterMass_nonneg i))

noncomputable def cap (i : ℕ) : Q → ℝ :=
  localKineticMajorant (D.source i) (D.mass i) (D.fieldSize i) C e L

omit [IsProbabilityMeasure μ] [CompleteSpace T] in
theorem cap_nonneg (hC : 0 ≤ C) (he : 0 ≤ e) (i : ℕ) :
    ∀ᵐ q ∂μ, 0 ≤ D.cap i q := by
  filter_upwards [D.source_nonneg i] with q hq
  exact localKineticMajorant_nonneg hq (D.mass_nonneg i q) (D.field_nonneg i q) hC he

omit [IsProbabilityMeasure μ] [CompleteSpace T] in
theorem cap_integral (hC : 0 ≤ C) (hCZ : 0 ≤ CZ) (he : 0 ≤ e) (hk : 0 ≤ k)
    (i : ℕ) : Integrable (D.cap i) μ ∧
    (∫ q, D.cap i q ∂μ) ≤ D.input i - D.soft i +
      (C * max CZ (Real.sqrt CZ) * e ^ 2 * k ^ 2 * L ^ 2) * D.coefficient i +
      (C * max CZ (Real.sqrt CZ) * e * k) *
        Real.sqrt (D.clusterMass i * D.coefficient i) := by
  obtain ⟨hi, hb⟩ := localKineticMajorant_integrable_and_le
    hC hCZ he hk (D.coefficient_nonneg i) (D.mass_nonneg i) (D.field_nonneg i)
    (D.mass_integrable i).aestronglyMeasurable (D.field_measurable i)
    (D.source_integrable i) (D.mass_integrable i)
    (D.second_integrable i) (D.second_bound i)
  exact ⟨hi, by simpa only [D.source_energy, clusterMass, coefficient, cap] using hb⟩

omit [IsProbabilityMeasure μ] [CompleteSpace T] in
/-- Summability of the cap is derived from the source ensemble and the
weighted first/second moment estimates, before constructing the operator. -/
theorem cap_summable (hC : 0 ≤ C) (hCZ : 0 ≤ CZ) (he : 0 ≤ e) (hk : 0 ≤ k) :
    Summable (fun i => ∫ q, D.cap i q ∂μ) := by
  have hcoeff : Summable D.coefficient :=
    (D.soft_summable.mul_left (a ^ 2)).add (D.normalized.summable.mul_left (b ^ 2))
  have hroot := (RemovalAssembly.summable_sqrt_mul D.clusterMass_nonneg
    D.coefficient_nonneg D.normalized.summable hcoeff).1
  exact Summable.of_nonneg_of_le
    (fun i => integral_nonneg_of_ae (D.cap_nonneg hC he i))
    (fun i => (D.cap_integral hC hCZ he hk i).2)
    (((D.input_summable.sub D.soft_summable).add
      (hcoeff.mul_left (C * max CZ (Real.sqrt CZ) * e ^ 2 * k ^ 2 * L ^ 2))).add
      (hroot.mul_left (C * max CZ (Real.sqrt CZ) * e * k)))

/-- The finite-energy vector ensemble is constructed from the source data.
Its cap integrability, cap summability and total energy inequality are no
longer independent premises. -/
noncomputable def vectorData (hC : 0 ≤ C) (hCZ : 0 ≤ CZ) (he : 0 ≤ e) (hk : 0 ≤ k) :
    VectorData R Tr E μ where
  vector := D.vector
  measurable := D.measurable
  mass := D.mass
  mass_sum := D.mass_sum
  mass_integrable := D.mass_integrable
  normalized := D.normalized
  positive_compatible := D.positive_compatible
  trace_compatible := D.trace_compatible
  energyCap := D.cap
  cap_integrable i := (D.cap_integral hC hCZ he hk i).1
  cap_nonneg := D.cap_nonneg hC he
  cap_summable := D.cap_summable hC hCZ he hk
  vector_energy_le i := by
    filter_upwards [D.form_series i, D.kinetic_bound i] with q hq hbound
    rw [hq]
    exact ENNReal.ofReal_le_ofReal hbound

omit [IsProbabilityMeasure μ] [CompleteSpace T] in
/-- A single constant absorbs the repair, field-moment and vacuum constants.
It is chosen independently of the input state and of the cluster scale. -/
theorem cap_integral_add_vacuum {Cv Ctotal : ℝ}
    (hC : 0 ≤ C) (hCZ : 0 ≤ CZ) (he : 0 ≤ e) (hk : 0 ≤ k)
    (hrepair : C * max CZ (Real.sqrt CZ) ≤ Ctotal) (hvacuum : Cv ≤ Ctotal)
    (i : ℕ) :
    (∫ q, D.cap i q + (Cv * e ^ 2 * b ^ 2) * D.mass i q ∂μ) ≤
      D.input i - D.soft i +
        (Ctotal * e ^ 2 * k ^ 2 * L ^ 2) * D.coefficient i +
        (Ctotal * e * k) * Real.sqrt (D.clusterMass i * D.coefficient i) +
        (Ctotal * e ^ 2 * b ^ 2) * D.clusterMass i := by
  rw [integral_add (D.cap_integral hC hCZ he hk i).1
    ((D.mass_integrable i).const_mul _), integral_const_mul]
  have hp := D.clusterMass_nonneg i
  have hB := D.coefficient_nonneg i
  calc
    _ ≤ (D.input i - D.soft i +
        (C * max CZ (Real.sqrt CZ) * e ^ 2 * k ^ 2 * L ^ 2) * D.coefficient i +
        (C * max CZ (Real.sqrt CZ) * e * k) *
          Real.sqrt (D.clusterMass i * D.coefficient i)) +
        (Cv * e ^ 2 * b ^ 2) * D.clusterMass i :=
      add_le_add (D.cap_integral hC hCZ he hk i).2 le_rfl
    _ ≤ _ := by gcongr

end MomentData
end Moments
end GptLean.RemovalEnergy
