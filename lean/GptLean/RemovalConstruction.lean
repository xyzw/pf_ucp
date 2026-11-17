import GptLean.Repair.TraceChannel
import GptLean.ObservableAssembly
import GptLean.SoftRemoval

/-!
Construction of a normalized finite-energy removal output from the actual
countable family of repaired vectors. The two vector indices (source and
Kraus) can be flattened by `Repair.flattenVectors`. Measurability, positive
trace-class convergence and the full unbounded energy decomposition are
conclusions, not properties of an assumed output state.

The local vector form bounds and standard trace/rank-one identifications
are explicit. The physical application must still provide its electronic
localization, conditional vectors and tested form identities.
-/

namespace GptLean.RemovalConstruction

open MeasureTheory Filter RemovalState
open scoped ENNReal

variable {Q K T : Type*} [MeasurableSpace Q] {μ : Measure Q}
  [IsProbabilityMeasure μ] [NormedAddCommGroup K]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : Gaussian.RankOneData K T} {Tr : PositiveTraceData T}
  {E : PositiveForm Tr}

/-- Inputs are vectors and their scalar mass/form estimates. No output
operator or output state occurs among the fields. -/
structure VectorData (R : Gaussian.RankOneData K T)
    (Tr : PositiveTraceData T) (E : PositiveForm Tr) (μ : Measure Q) where
  vector : ℕ → ℕ → Q → K
  measurable : ∀ a k, AEStronglyMeasurable (vector a k) μ
  mass : ℕ → Q → ℝ
  mass_sum : ∀ a, ∀ᵐ q ∂μ, HasSum (fun k => ‖vector a k q‖ ^ 2) (mass a q)
  mass_integrable : ∀ a, Integrable (mass a) μ
  normalized : HasSum (fun a => ∫ q, mass a q ∂μ) 1
  positive_compatible : R.positive ⊆ Tr.positive
  trace_compatible : R.trace = Tr.trace
  energyCap : ℕ → Q → ℝ
  cap_integrable : ∀ a, Integrable (energyCap a) μ
  cap_nonneg : ∀ a, ∀ᵐ q ∂μ, 0 ≤ energyCap a q
  cap_summable : Summable (fun a => ∫ q, energyCap a q ∂μ)
  vector_energy_le : ∀ a, ∀ᵐ q ∂μ,
    (∑' k, E.expectation (R.rankOne (vector a k q))) ≤ ENNReal.ofReal (energyCap a q)

namespace VectorData

variable (D : VectorData R Tr E μ)

noncomputable def conditional (a : ℕ) (q : Q) : T :=
  Repair.rankOneSeries R (fun k => D.vector a k q)

noncomputable def output : T := aggregate D.conditional μ

noncomputable def clusterMass (a : ℕ) : ℝ := ∫ q, D.mass a q ∂μ

theorem cluster_mass_nonneg (a : ℕ) : 0 ≤ D.clusterMass a := by
  apply integral_nonneg_of_ae
  filter_upwards [D.mass_sum a] with q hq
  rw [← hq.tsum_eq]
  exact tsum_nonneg (fun k => sq_nonneg _)

theorem conditional_integrable (a : ℕ) : Integrable (D.conditional a) μ :=
  Repair.rankOneSeries_integrable R (D.measurable a) (D.mass_sum a) (D.mass_integrable a)

theorem conditional_positive (a : ℕ) : ∀ᵐ q ∂μ, D.conditional a q ∈ Tr.positive := by
  filter_upwards [D.mass_sum a] with q hq
  exact D.positive_compatible (Repair.rankOneSeries_positive R hq)

theorem conditional_trace (a : ℕ) : ∀ᵐ q ∂μ, Tr.trace (D.conditional a q) = D.mass a q := by
  filter_upwards [D.mass_sum a] with q hq
  rw [← D.trace_compatible]
  exact Repair.rankOneSeries_trace R hq

theorem conditional_norm_integral (a : ℕ) :
    (∫ q, ‖D.conditional a q‖ ∂μ) = ∫ q, D.mass a q ∂μ := by
  apply integral_congr_ae
  filter_upwards [D.conditional_positive a, D.conditional_trace a] with q hp ht
  exact (Tr.norm_eq_trace hp).trans ht

theorem conditional_norm_summable : Summable (fun a => ∫ q, ‖D.conditional a q‖ ∂μ) := by
  simpa only [D.conditional_norm_integral] using D.normalized.summable

theorem output_hasSum : HasSum (fun a => ∫ q, D.conditional a q ∂μ) D.output :=
  PositiveForm.aggregate_hasSum_of_norm D.conditional_norm_summable

theorem output_normalized : D.output ∈ Tr.positive ∧ Tr.trace D.output = 1 := by
  apply Tr.normalized_aggregate D.conditional_integrable
    (fun a => (D.conditional_integrable a).1) D.conditional_positive D.conditional_positive
    (fun _ => Eventually.of_forall (fun _ => rfl))
  convert D.normalized using 1
  funext a
  exact integral_congr_ae (D.conditional_trace a)

/-- The conditional energy is derived for the defined operator series. -/
theorem conditional_energy (a : ℕ) : ∀ᵐ q ∂μ,
    E.expectation (D.conditional a q) =
      ∑' k, E.expectation (R.rankOne (D.vector a k q)) := by
  filter_upwards [D.mass_sum a] with q hq
  exact Repair.rankOneSeries_expectation R E D.positive_compatible hq

theorem conditional_energy_le (a : ℕ) : ∀ᵐ q ∂μ,
    E.expectation (D.conditional a q) ≤ ENNReal.ofReal (D.energyCap a q) := by
  filter_upwards [D.conditional_energy a, D.vector_energy_le a] with q he hb
  rwa [he]

theorem conditional_energy_finite (a : ℕ) : ∀ᵐ q ∂μ,
    E.expectation (D.conditional a q) < ⊤ :=
  (D.conditional_energy_le a).mono (fun _ hq => hq.trans_lt ENNReal.ofReal_lt_top)

/-- The unbounded energy identity holds before any finiteness conversion. -/
theorem output_energy : E.expectation D.output =
    ∑' a, ∫⁻ q, ∑' k, E.expectation (R.rankOne (D.vector a k q)) ∂μ := by
  rw [output, E.expectation_aggregate D.conditional_integrable
    D.conditional_positive D.conditional_norm_summable]
  exact tsum_congr (fun a => lintegral_congr_ae (D.conditional_energy a))

theorem output_energy_le : E.expectation D.output ≤
    ENNReal.ofReal (∑' a, ∫ q, D.energyCap a q ∂μ) :=
  E.expectation_aggregate_le D.conditional_integrable D.conditional_positive
    D.conditional_norm_summable D.cap_integrable D.cap_nonneg D.cap_summable
    D.conditional_energy_le

theorem output_energy_finite : E.expectation D.output < ⊤ :=
  D.output_energy_le.trans_lt ENNReal.ofReal_lt_top

/-- The state is now constructed, including its finite form energy. -/
noncomputable def state : E.State :=
  ⟨D.output, D.output_normalized.1, D.output_normalized.2, D.output_energy_finite⟩

noncomputable def clusterEnergy (a : ℕ) : ℝ :=
  (∫⁻ q, E.expectation (D.conditional a q) ∂μ).toReal

theorem cluster_energy_le (a : ℕ) : D.clusterEnergy a ≤ ∫ q, D.energyCap a q ∂μ := by
  have he : (∫⁻ q, E.expectation (D.conditional a q) ∂μ) ≤
      ENNReal.ofReal (∫ q, D.energyCap a q ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal (D.cap_integrable a) (D.cap_nonneg a)]
    exact lintegral_mono_ae (D.conditional_energy_le a)
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top he).trans_eq
    (ENNReal.toReal_ofReal (integral_nonneg_of_ae (D.cap_nonneg a)))

theorem cluster_energy_total : (E.expectation D.output).toReal = ∑' a, D.clusterEnergy a := by
  have he := E.expectation_aggregate D.conditional_integrable D.conditional_positive
    D.conditional_norm_summable
  have hf : ∀ a, (∫⁻ q, E.expectation (D.conditional a q) ∂μ) ≠ ⊤ := by
    intro a
    exact ne_top_of_le_ne_top D.output_energy_finite.ne
      (by rw [output, he]; exact ENNReal.le_tsum a)
  rw [output, he, ENNReal.tsum_toReal_eq hf]
  rfl

/-- The bounded spectral approximants suffice to pass every tested current
through both the conditional integral and the localization sum. -/
theorem current_assembly (J : FormObservable E) {bound : ℕ → Q → ℝ}
    (hb : ∀ a, Integrable (bound a) μ)
    (hs : Summable (fun a => ∫ q, bound a q ∂μ))
    (hbound : ∀ n a, ∀ᵐ q ∂μ,
      ‖J.approximation n (D.conditional a q)‖ ≤ bound a q) :
    J.value D.output = ∑' a, ∫ q, J.value (D.conditional a q) ∂μ :=
  (J.value_aggregate D.conditional_integrable D.conditional_positive
    D.conditional_energy_finite D.conditional_norm_summable
    D.output_normalized.1 D.output_energy_finite hb hs hbound).2.2

/-- A standard current form bound supplies the required integrable majorant
from the vector mass and energy estimates. Conditional current domination
does not have to be asserted separately. -/
theorem current_assembly_of_form_bound (J : FormObservable E) {C : ℝ}
    (hC : 0 ≤ C)
    (hform : ∀ n x, x ∈ Tr.positive → E.expectation x < ⊤ →
      ‖J.approximation n x‖ ≤ C * (Tr.trace x + (E.expectation x).toReal)) :
    J.value D.output = ∑' a, ∫ q, J.value (D.conditional a q) ∂μ := by
  apply D.current_assembly J (bound := fun a q => C * (D.mass a q + D.energyCap a q))
  · intro a
    exact ((D.mass_integrable a).add (D.cap_integrable a)).const_mul C
  · simpa only [integral_const_mul, integral_add (D.mass_integrable _) (D.cap_integrable _)]
      using (D.normalized.summable.add D.cap_summable).mul_left C
  · intro n a
    filter_upwards [D.conditional_positive a, D.conditional_energy_finite a,
      D.conditional_trace a, D.conditional_energy_le a, D.cap_nonneg a]
      with q hp hf ht he hc
    have hb : (E.expectation (D.conditional a q)).toReal ≤ D.energyCap a q := by
      exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top he).trans_eq (ENNReal.toReal_ofReal hc)
    exact (hform n _ hp hf).trans
      (mul_le_mul_of_nonneg_left (by rw [ht]; exact add_le_add le_rfl hb) hC)

/-- Conditional tested identities and the source series imply exact
recovery of every test on the constructed output. -/
theorem tested_constraint_eq {Test : Type*} (J : Test → FormObservable E)
    (target : Test → ℝ) (source : Test → ℕ → Q → ℝ)
    (C : Test → ℝ) (hC : ∀ t, 0 ≤ C t)
    (hform : ∀ t n x, x ∈ Tr.positive → E.expectation x < ⊤ →
      ‖(J t).approximation n x‖ ≤ C t * (Tr.trace x + (E.expectation x).toReal))
    (hlocal : ∀ t a, ∀ᵐ q ∂μ, (J t).value (D.conditional a q) = source t a q)
    (hsource : ∀ t, HasSum (fun a => ∫ q, source t a q ∂μ) (target t)) :
    (fun t => (J t).value D.output) = target := by
  funext t
  rw [D.current_assembly_of_form_bound (J t) (hC t) (hform t)]
  exact (tsum_congr (fun a => integral_congr_ae (hlocal t a))).trans (hsource t).tsum_eq

/-- Every bounded observable, including a partial trace, is evaluated on
the actual output by the convergent integral series. -/
theorem bounded_assembly {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (B : T →L[ℝ] F) :
    B D.output = ∑' a, ∫ q, B (D.conditional a q) ∂μ := by
  have h := (B.hasSum D.output_hasSum).tsum_eq.symm
  simpa only [← B.integral_comp_comm (D.conditional_integrable _)] using h

/-- The model uses the energy of the constructed finite-energy operator. -/
noncomputable def model {P : Type*} (constraint : T → P) : DFT.StateModel E.State P where
  energy s := (E.expectation s.val).toReal
  density s := constraint s.val

/-- Instantiate the earlier removal interface with the constructed state.
Only local vector costs, IMS and tested constraint identities remain here.
No output-energy decomposition or finite-energy state is supplied. -/
noncomputable def localizedOutput {P F : Type*} (constraint : T → P)
    (m : E.State) (marginal : E.State → F) (target : F)
    {input soft : ℕ → ℝ} {Esoft C e k L a b : ℝ}
    (hpair : constraint D.output = constraint m.val)
    (hmarg : marginal D.state = target)
    (hsoft : ∀ i, 0 ≤ soft i)
    (hi : Summable input) (hs : Summable soft) (hst : ∑' i, soft i = Esoft)
    (hims : ∑' i, input i ≤ (E.expectation m.val).toReal + C * (L ^ 2)⁻¹)
    (hcost : ∀ i, (∫ q, D.energyCap i q ∂μ) ≤ input i - soft i +
      (C * e ^ 2 * k ^ 2 * L ^ 2) * (a ^ 2 * soft i + b ^ 2 * D.clusterMass i) +
      (C * e * k) * Real.sqrt (D.clusterMass i * (a ^ 2 * soft i + b ^ 2 * D.clusterMass i)) +
      (C * e ^ 2 * b ^ 2) * D.clusterMass i) :
    SoftRemoval.LocalizedOutput (model constraint) m marginal target Esoft C e k L a b where
  state := D.state
  pair_eq := hpair
  marginal_eq := hmarg
  inputEnergy := input
  outputEnergy := D.clusterEnergy
  softEnergy := soft
  mass := D.clusterMass
  mass_nonneg := D.cluster_mass_nonneg
  soft_nonneg := hsoft
  output_nonneg := fun _ => ENNReal.toReal_nonneg
  input_summable := hi
  soft_summable := hs
  mass_summable := D.normalized.summable
  mass_total := D.normalized.tsum_eq
  soft_total := hst
  output_total := D.cluster_energy_total
  ims := hims
  local_cost := fun i => (D.cluster_energy_le i).trans (hcost i)

end VectorData
end GptLean.RemovalConstruction
