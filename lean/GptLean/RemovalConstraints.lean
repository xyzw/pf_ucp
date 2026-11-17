import GptLean.RemovalVacuum
import GptLean.Repair.ParameterSections

/-!
Constraints of the same trace-class removal output.

The identities here start at rank-one vectors. Bounded density tests and
hard marginals pass through the convergent trace series. Current tests pass
through the same series by spectral approximation and the positive energy
bound. In particular no constraint identity for a conditional or final
output operator is an input.
-/

namespace GptLean.RemovalConstraints

open MeasureTheory Filter RemovalState RemovalConstruction
open scoped ENNReal Topology

section Density

variable {X V H T : Type*} [MeasurableSpace X] {ν : Measure X}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]

/-- Signed bounded multiplication tests are preserved by the actual
coordinate multipliers. This includes every density test. -/
theorem integrated_channel_density (b : HilbertBasis ℕ ℂ V)
    {z : X → V} {ψ : X → H} {w : X → ℝ} {C : ℝ}
    (hz : AEStronglyMeasurable z ν) (hψ : AEStronglyMeasurable ψ ν)
    (hw : AEStronglyMeasurable w ν) (_hC : 0 ≤ C)
    (hbound : ∀ᵐ x ∂ν, ‖w x‖ ≤ C)
    (hunit : ∀ᵐ x ∂ν, ‖z x‖ = 1)
    (hmass : Integrable (fun x => ‖ψ x‖ ^ 2) ν) :
    HasSum (fun k => ∫ x, w x * ‖Repair.channelValue b z ψ k x‖ ^ 2 ∂ν)
      (∫ x, w x * ‖ψ x‖ ^ 2 ∂ν) := by
  have hs : ∀ᵐ x ∂ν, HasSum
      (fun k => ‖Repair.channelValue b z ψ k x‖ ^ 2) (‖ψ x‖ ^ 2) := by
    filter_upwards [hunit] with x hx
    simpa only [Repair.channelValue, hx, one_pow, one_mul] using
      Repair.coordinate_smul_norm_sq_hasSum b (z x) (ψ x)
  apply hasSum_integral_of_dominated_convergence
    (fun k x => C * ‖Repair.channelValue b z ψ k x‖ ^ 2)
    (fun k => hw.mul ((Repair.channelValue_measurable b hz hψ k).norm.pow 2))
  · intro k
    filter_upwards [hbound] with x hx
    change ‖w x * ‖Repair.channelValue b z ψ k x‖ ^ 2‖ ≤
      C * ‖Repair.channelValue b z ψ k x‖ ^ 2
    rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_right hx (sq_nonneg _)
  · exact hs.mono (fun x hx => (hx.mul_left C).summable)
  · apply (hmass.const_mul C).congr
    filter_upwards [hs] with x hx
    exact (hx.mul_left C).tsum_eq.symm
  · exact hs.mono (fun x hx => hx.mul_left (w x))

/-- Rank-one multiplication calculus turns the vector density identity
into an identity for the constructed trace-class channel. -/
theorem traceChannel_density (R : Gaussian.RankOneData (Lp H 2 ν) T)
    (b : HilbertBasis ℕ ℂ V) (B : T →L[ℝ] ℝ)
    {z : X → V} {ψ : X → H} {w : X → ℝ} {C : ℝ}
    (hB : ∀ f : Lp H 2 ν, B (R.rankOne f) = ∫ x, w x * ‖f x‖ ^ 2 ∂ν)
    (hz : AEStronglyMeasurable z ν) (hψ : AEStronglyMeasurable ψ ν)
    (hw : AEStronglyMeasurable w ν) (hC : 0 ≤ C)
    (hbound : ∀ᵐ x ∂ν, ‖w x‖ ≤ C)
    (hunit : ∀ᵐ x ∂ν, ‖z x‖ = 1)
    (hmass : Integrable (fun x => ‖ψ x‖ ^ 2) ν) :
    B (Repair.traceChannel R b hz hψ hunit hmass) = ∫ x, w x * ‖ψ x‖ ^ 2 ∂ν := by
  apply Repair.rankOneSeries_observable R B
    (Repair.channelVector_mass b hz hψ hunit hmass)
  have he (k : ℕ) : B (R.rankOne (Repair.channelVector b hz hψ hunit hmass k)) =
      ∫ x, w x * ‖Repair.channelValue b z ψ k x‖ ^ 2 ∂ν := by
    rw [hB]
    apply integral_congr_ae
    filter_upwards [(Repair.channelValue_memLp b hz hψ hunit hmass k).coeFn_toLp]
      with x hx
    change w x * ‖(Repair.channelValue_memLp b hz hψ hunit hmass k).toLp _ x‖ ^ 2 = _
    rw [hx]
  simpa only [he] using integrated_channel_density b hz hψ hw hC hbound hunit hmass

/-- Countably many source vectors use exactly the same density test.
Both vector indices are summed in trace norm. -/
theorem mixedTraceChannel_density (R : Gaussian.RankOneData (Lp H 2 ν) T)
    (b : HilbertBasis ℕ ℂ V) (B : T →L[ℝ] ℝ)
    {z : X → V} {ψ : ℕ → X → H} {w : X → ℝ} {C mass : ℝ}
    (hB : ∀ f : Lp H 2 ν, B (R.rankOne f) = ∫ x, w x * ‖f x‖ ^ 2 ∂ν)
    (hz : AEStronglyMeasurable z ν) (hψ : ∀ n, AEStronglyMeasurable (ψ n) ν)
    (hw : AEStronglyMeasurable w ν) (hC : 0 ≤ C)
    (hbound : ∀ᵐ x ∂ν, ‖w x‖ ≤ C)
    (hunit : ∀ᵐ x ∂ν, ‖z x‖ = 1)
    (hint : ∀ n, Integrable (fun x => ‖ψ n x‖ ^ 2) ν)
    (hmass : HasSum (fun n => ∫ x, ‖ψ n x‖ ^ 2 ∂ν) mass) :
    B (Repair.mixedTraceChannel R b hz hψ hunit hint) =
      ∑' n, ∫ x, w x * ‖ψ n x‖ ^ 2 ∂ν := by
  have hs : Summable (fun n => Repair.traceChannel R b hz (hψ n) hunit (hint n)) :=
    hmass.summable.of_norm_bounded
      (fun n => Repair.traceChannel_norm_le R b hz (hψ n) hunit (hint n))
  rw [Repair.mixedTraceChannel_eq_tsum R b hz hψ hunit hint hmass, B.map_tsum hs]
  exact tsum_congr
    (fun n => traceChannel_density R b B hB hz (hψ n) hw hC hbound hunit (hint n))

end Density

section Current

variable {K T : Type*} [NormedAddCommGroup K]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : Gaussian.RankOneData K T} {Tr : PositiveTraceData T} {E : PositiveForm Tr}

/-- The full positive energy form may contain potential and photon terms.
Only its finite sum and a standard current form bound are needed to pass
rank-one current limits to the trace-class series. -/
theorem rankOneSeries_current (J : FormObservable E)
    (hpositive : R.positive ⊆ Tr.positive) (htrace : R.trace = Tr.trace)
    {v : ℕ → K} {j : ℕ → ℝ} {mass C : ℝ}
    (hmass : HasSum (fun k => ‖v k‖ ^ 2) mass)
    (henergy : (∑' k, E.expectation (R.rankOne (v k))) < ⊤)
    (_hC : 0 ≤ C)
    (hform : ∀ n x, x ∈ Tr.positive → E.expectation x < ⊤ →
      ‖J.approximation n x‖ ≤ C * (Tr.trace x + (E.expectation x).toReal))
    (hcurrent : ∀ k, Tendsto (fun n => J.approximation n (R.rankOne (v k)))
      atTop (𝓝 (j k))) :
    J.value (Repair.rankOneSeries R v) = ∑' k, j k := by
  have hk (k : ℕ) : E.expectation (R.rankOne (v k)) < ⊤ :=
    (ENNReal.le_tsum k).trans_lt henergy
  have hb : Summable (fun k => C * (‖v k‖ ^ 2 +
      (E.expectation (R.rankOne (v k))).toReal)) :=
    (hmass.summable.add (ENNReal.summable_toReal henergy.ne)).mul_left C
  have hbound (n k : ℕ) : ‖J.approximation n (R.rankOne (v k))‖ ≤
      C * (‖v k‖ ^ 2 + (E.expectation (R.rankOne (v k))).toReal) := by
    have h := hform n _ (hpositive (R.rankOne_positive _)) (hk k)
    rwa [← htrace, R.trace_rankOne] at h
  have hl := tendsto_tsum_of_dominated_convergence hb hcurrent
    (Eventually.of_forall hbound)
  have hs := (Repair.rankOneSeries_hasSum R hmass).summable
  have hf : E.expectation (Repair.rankOneSeries R v) < ⊤ := by
    rwa [Repair.rankOneSeries_expectation R E hpositive hmass]
  apply tendsto_nhds_unique
    (J.converges _ (hpositive (Repair.rankOneSeries_positive R hmass)) hf)
  simpa only [Repair.rankOneSeries, (J.approximation _).map_tsum hs] using hl

end Current

section CommonOutput

variable {Q K T : Type*} [MeasurableSpace Q] {μ : Measure Q}
  [IsProbabilityMeasure μ] [NormedAddCommGroup K]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : Gaussian.RankOneData K T} {Tr : PositiveTraceData T} {E : PositiveForm Tr}

/-- A bounded constraint of the assembled state follows from rank-one
values and the localized source series. The target can be a trace-class
hard marginal rather than a scalar. -/
theorem bounded_constraint_eq {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F]
    (D : VectorData R Tr E μ) (B : T →L[ℝ] F)
    (source : ℕ → Q → F) (target : F)
    (hlocal : ∀ a, ∀ᵐ q ∂μ,
      HasSum (fun k => B (R.rankOne (D.vector a k q))) (source a q))
    (hsource : HasSum (fun a => ∫ q, source a q ∂μ) target) :
    B D.output = target := by
  rw [D.bounded_assembly B]
  have he (a : ℕ) : (fun q => B (D.conditional a q)) =ᵐ[μ] source a := by
    filter_upwards [D.mass_sum a, hlocal a] with q hm hl
    exact Repair.rankOneSeries_observable R B hm hl
  exact (tsum_congr (fun a => integral_congr_ae (he a))).trans hsource.tsum_eq

/-- Density uses bounded multiplication tests while current uses its
unbounded form trace. Both constraints are obtained for the operator
constructed from precisely the same vectors. -/
theorem current_constraint_eq {Test : Type*}
    (D : VectorData R Tr E μ) (J : Test → FormObservable E)
    (value : Test → ℕ → ℕ → Q → ℝ)
    (source : Test → ℕ → Q → ℝ) (target : Test → ℝ)
    (C : Test → ℝ) (hC : ∀ t, 0 ≤ C t)
    (hform : ∀ t n x, x ∈ Tr.positive → E.expectation x < ⊤ →
      ‖(J t).approximation n x‖ ≤ C t * (Tr.trace x + (E.expectation x).toReal))
    (hrank : ∀ t a, ∀ᵐ q ∂μ, ∀ k,
      Tendsto (fun n => (J t).approximation n (R.rankOne (D.vector a k q)))
        atTop (𝓝 (value t a k q)))
    (hlocal : ∀ t a, ∀ᵐ q ∂μ,
      HasSum (fun k => value t a k q) (source t a q))
    (hsource : ∀ t, HasSum (fun a => ∫ q, source t a q ∂μ) (target t)) :
    (fun t => (J t).value D.output) = target := by
  apply D.tested_constraint_eq J target source C hC hform _ hsource
  intro t a
  filter_upwards [D.mass_sum a, D.vector_energy_le a, hrank t a, hlocal t a]
    with q hm he hr hl
  exact (rankOneSeries_current (J t) D.positive_compatible D.trace_compatible hm
    (he.trans_lt ENNReal.ofReal_lt_top) (hC t) (hform t) hr).trans hl.tsum_eq

/-- One constructed normalized finite-energy state has all three exact
constraints. The hypotheses mention rank-one tests and source sums only. -/
theorem same_state_constraints {DensityTest CurrentTest F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (D : VectorData R Tr E μ)
    (density : DensityTest → T →L[ℝ] ℝ) (current : CurrentTest → FormObservable E)
    (marginal : T →L[ℝ] F)
    (densitySource : DensityTest → ℕ → Q → ℝ)
    (currentVector : CurrentTest → ℕ → ℕ → Q → ℝ)
    (currentSource : CurrentTest → ℕ → Q → ℝ) (marginalSource : ℕ → Q → F)
    (ρ : DensityTest → ℝ) (j : CurrentTest → ℝ) (θ : F)
    (hdlocal : ∀ t a, ∀ᵐ q ∂μ,
      HasSum (fun k => density t (R.rankOne (D.vector a k q))) (densitySource t a q))
    (hdsource : ∀ t, HasSum (fun a => ∫ q, densitySource t a q ∂μ) (ρ t))
    (C : CurrentTest → ℝ) (hC : ∀ t, 0 ≤ C t)
    (hform : ∀ t n x, x ∈ Tr.positive → E.expectation x < ⊤ →
      ‖(current t).approximation n x‖ ≤
        C t * (Tr.trace x + (E.expectation x).toReal))
    (hjrank : ∀ t a, ∀ᵐ q ∂μ, ∀ k,
      Tendsto (fun n => (current t).approximation n (R.rankOne (D.vector a k q)))
        atTop (𝓝 (currentVector t a k q)))
    (hjlocal : ∀ t a, ∀ᵐ q ∂μ,
      HasSum (fun k => currentVector t a k q) (currentSource t a q))
    (hjsource : ∀ t, HasSum (fun a => ∫ q, currentSource t a q ∂μ) (j t))
    (hmlocal : ∀ a, ∀ᵐ q ∂μ,
      HasSum (fun k => marginal (R.rankOne (D.vector a k q))) (marginalSource a q))
    (hmsource : HasSum (fun a => ∫ q, marginalSource a q ∂μ) θ) :
    (fun t => density t D.state.val) = ρ ∧
    (fun t => (current t).value D.state.val) = j ∧ marginal D.state.val = θ := by
  refine ⟨?_, ?_, bounded_constraint_eq D marginal marginalSource θ hmlocal hmsource⟩
  · funext t
    exact bounded_constraint_eq D (density t) (densitySource t) (ρ t) (hdlocal t) (hdsource t)
  · exact current_constraint_eq D current currentVector currentSource j C hC hform
      hjrank hjlocal hjsource

/-- The pair is evaluated on the trace-class operator of the state. -/
def testedPair {DensityTest CurrentTest : Type*}
    (density : DensityTest → T →L[ℝ] ℝ) (current : CurrentTest → FormObservable E)
    (x : T) : (DensityTest → ℝ) × (CurrentTest → ℝ) :=
  (fun t => density t x, fun t => (current t).value x)

/-- Local input data for exact constraints. None of the fields refers to
the value of a constraint on the final or conditional output operator. -/
structure ConstraintData {DensityTest CurrentTest F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D : VectorData R Tr E μ)
    (density : DensityTest → T →L[ℝ] ℝ) (current : CurrentTest → FormObservable E)
    (marginal : T →L[ℝ] F)
    (ρ : DensityTest → ℝ) (j : CurrentTest → ℝ) (θ : F) where
  densitySource : DensityTest → ℕ → Q → ℝ
  currentVector : CurrentTest → ℕ → ℕ → Q → ℝ
  currentSource : CurrentTest → ℕ → Q → ℝ
  marginalSource : ℕ → Q → F
  density_local : ∀ t a, ∀ᵐ q ∂μ,
    HasSum (fun k => density t (R.rankOne (D.vector a k q))) (densitySource t a q)
  density_source : ∀ t, HasSum (fun a => ∫ q, densitySource t a q ∂μ) (ρ t)
  currentConstant : CurrentTest → ℝ
  currentConstant_nonneg : ∀ t, 0 ≤ currentConstant t
  current_bound : ∀ t n x, x ∈ Tr.positive → E.expectation x < ⊤ →
    ‖(current t).approximation n x‖ ≤
      currentConstant t * (Tr.trace x + (E.expectation x).toReal)
  current_rankOne : ∀ t a, ∀ᵐ q ∂μ, ∀ k,
    Tendsto (fun n => (current t).approximation n (R.rankOne (D.vector a k q)))
      atTop (𝓝 (currentVector t a k q))
  current_local : ∀ t a, ∀ᵐ q ∂μ,
    HasSum (fun k => currentVector t a k q) (currentSource t a q)
  current_source : ∀ t, HasSum (fun a => ∫ q, currentSource t a q ∂μ) (j t)
  marginal_local : ∀ a, ∀ᵐ q ∂μ,
    HasSum (fun k => marginal (R.rankOne (D.vector a k q))) (marginalSource a q)
  marginal_source : HasSum (fun a => ∫ q, marginalSource a q ∂μ) θ

namespace ConstraintData

variable {DensityTest CurrentTest F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {D : VectorData R Tr E μ}
  {density : DensityTest → T →L[ℝ] ℝ} {current : CurrentTest → FormObservable E}
  {marginal : T →L[ℝ] F} {ρ : DensityTest → ℝ} {j : CurrentTest → ℝ} {θ : F}

theorem constraints (A : ConstraintData D density current marginal ρ j θ) :
    testedPair density current D.state.val = (ρ, j) ∧ marginal D.state.val = θ := by
  obtain ⟨hd, hj, hm⟩ := same_state_constraints D density current marginal
    A.densitySource A.currentVector A.currentSource A.marginalSource ρ j θ
    A.density_local A.density_source A.currentConstant A.currentConstant_nonneg
    A.current_bound A.current_rankOne A.current_local A.current_source
    A.marginal_local A.marginal_source
  exact ⟨Prod.ext hd hj, hm⟩

/-- The removal interface now receives the constructed state with proved
density, current and marginal constraints. Only the energy estimates of
the localized source remain external to this constraint assembly. -/
noncomputable def localizedOutput (m : E.State)
    (A : ConstraintData D density current marginal
      (fun t => density t m.val) (fun t => (current t).value m.val) θ)
    {input soft : ℕ → ℝ} {Esoft C e k L a b : ℝ}
    (hsoft : ∀ i, 0 ≤ soft i)
    (hi : Summable input) (hs : Summable soft) (hst : ∑' i, soft i = Esoft)
    (hims : ∑' i, input i ≤ (E.expectation m.val).toReal + C * (L ^ 2)⁻¹)
    (hcost : ∀ i, (∫ q, D.energyCap i q ∂μ) ≤ input i - soft i +
      (C * e ^ 2 * k ^ 2 * L ^ 2) * (a ^ 2 * soft i + b ^ 2 * D.clusterMass i) +
      (C * e * k) * Real.sqrt (D.clusterMass i * (a ^ 2 * soft i + b ^ 2 * D.clusterMass i)) +
      (C * e ^ 2 * b ^ 2) * D.clusterMass i) :
    SoftRemoval.LocalizedOutput (VectorData.model (testedPair density current)) m
      (fun s => marginal s.val) θ Esoft C e k L a b :=
  D.localizedOutput (testedPair density current) m (fun s => marginal s.val) θ
    A.constraints.1 A.constraints.2 hsoft hi hs hst hims hcost

end ConstraintData

end CommonOutput

section MixedSource

variable {X Q V H T : Type*} [MeasurableSpace X] [MeasurableSpace Q]
  {ν : Measure X} {μ : Measure Q} [IsProbabilityMeasure μ]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : Gaussian.RankOneData (Lp H 2 ν) T}
  {Tr : PositiveTraceData T} {E : PositiveForm Tr}

/-- The countable source vectors and repair multipliers realizing a
`VectorData` family. Only representatives, their mass and the defining
vector equality occur here. No observable or output constraint is stored. -/
structure MixedChannelRealization (D : VectorData R Tr E μ)
    (b : HilbertBasis ℕ ℂ V) where
  z : ℕ → Q → X → V
  source : ℕ → ℕ → Q → X → H
  multiplier_measurable : ∀ a q, AEStronglyMeasurable (z a q) ν
  source_measurable : ∀ a n q, AEStronglyMeasurable (source a n q) ν
  unit : ∀ a q, ∀ᵐ x ∂ν, ‖z a q x‖ = 1
  source_integrable : ∀ a n q, Integrable (fun x => ‖source a n q x‖ ^ 2) ν
  source_mass : ∀ a, ∀ᵐ q ∂μ,
    HasSum (fun n => ∫ x, ‖source a n q x‖ ^ 2 ∂ν) (D.mass a q)
  vector_eq : ∀ a, ∀ᵐ q ∂μ, ∀ k, D.vector a k q =
    Repair.flattenVectors (fun n => Repair.channelVector b (multiplier_measurable a q)
      (source_measurable a n q) (unit a q) (source_integrable a n q)) k

namespace MixedChannelRealization

variable {D : VectorData R Tr E μ} {b : HilbertBasis ℕ ℂ V}
  (A : MixedChannelRealization D b)

/-- The operator identity is deduced from the actual vector realization. -/
theorem conditional_eq (a : ℕ) : ∀ᵐ q ∂μ, D.conditional a q =
    Repair.mixedTraceChannel R b (A.multiplier_measurable a q)
      (fun n => A.source_measurable a n q) (A.unit a q)
      (fun n => A.source_integrable a n q) := by
  filter_upwards [A.vector_eq a] with q hq
  unfold VectorData.conditional Repair.mixedTraceChannel Repair.rankOneSeries
  exact tsum_congr (fun k => congrArg R.rankOne (hq k))

/-- Every bounded density test is recovered from the original countable
source decomposition. Parseval and the rank-one trace formula discharge
the entire conditional-output identity. -/
theorem density_eq (B : T →L[ℝ] ℝ) {w : X → ℝ} {C target : ℝ}
    (hB : ∀ f : Lp H 2 ν, B (R.rankOne f) = ∫ x, w x * ‖f x‖ ^ 2 ∂ν)
    (hw : AEStronglyMeasurable w ν) (hC : 0 ≤ C)
    (hbound : ∀ᵐ x ∂ν, ‖w x‖ ≤ C)
    (hsource : HasSum
      (fun a => ∫ q, ∑' n, ∫ x, w x * ‖A.source a n q x‖ ^ 2 ∂ν ∂μ) target) :
    B D.output = target := by
  rw [D.bounded_assembly B]
  have he (a : ℕ) : (fun q => B (D.conditional a q)) =ᵐ[μ]
      (fun q => ∑' n, ∫ x, w x * ‖A.source a n q x‖ ^ 2 ∂ν) := by
    filter_upwards [A.conditional_eq a, A.source_mass a] with q hq hm
    rw [hq]
    exact mixedTraceChannel_density R b B hB (A.multiplier_measurable a q)
      (fun n => A.source_measurable a n q) hw hC hbound (A.unit a q)
      (fun n => A.source_integrable a n q) hm
  exact (tsum_congr (fun a => integral_congr_ae (he a))).trans hsource.tsum_eq

/-- Bounded hard-photon tests are recovered using the same countable
vectors, Kraus index and conditional integral as the density theorem. -/
theorem hard_test_eq (W : H →L[ℂ] H) (B : T →L[ℝ] ℂ) {target : ℂ}
    (hB : ∀ f : Lp H 2 ν,
      B (R.rankOne f) = ∫ x, inner ℂ (f x) (W (f x)) ∂ν)
    (hsource : HasSum
      (fun a => ∫ q, ∑' n, ∫ x,
        inner ℂ (A.source a n q x) (W (A.source a n q x)) ∂ν ∂μ) target) :
    B D.output = target := by
  rw [D.bounded_assembly B]
  have he (a : ℕ) : (fun q => B (D.conditional a q)) =ᵐ[μ]
      (fun q => ∑' n, ∫ x,
        inner ℂ (A.source a n q x) (W (A.source a n q x)) ∂ν) := by
    filter_upwards [A.conditional_eq a, A.source_mass a] with q hq hm
    rw [hq]
    exact Repair.mixedTraceChannel_preserves R b W B hB (A.multiplier_measurable a q)
      (fun n => A.source_measurable a n q) (A.unit a q)
      (fun n => A.source_integrable a n q) hm
  exact (tsum_congr (fun a => integral_congr_ae (he a))).trans hsource.tsum_eq

/-- Separating bounded hard-photon observables identify the actual
trace-class marginal. A marginal identity for the output is a conclusion. -/
theorem hard_marginal_eq {F Test : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (M : T →L[ℝ] F) (tests : Test → F →L[ℝ] ℂ) (W : Test → H →L[ℂ] H)
    (separate : ∀ x y : F, (∀ t, tests t x = tests t y) → x = y) (target : F)
    (hrank : ∀ t (f : Lp H 2 ν), tests t (M (R.rankOne f)) =
      ∫ x, inner ℂ (f x) (W t (f x)) ∂ν)
    (hsource : ∀ t, HasSum
      (fun a => ∫ q, ∑' n, ∫ x,
        inner ℂ (A.source a n q x) (W t (A.source a n q x)) ∂ν ∂μ)
      (tests t target)) :
    M D.output = target := by
  apply separate
  intro t
  exact A.hard_test_eq (W t) ((tests t).comp M) (hrank t) (hsource t)

end MixedChannelRealization
end MixedSource

section SingleSource

variable {X Q V H T : Type*} [MeasurableSpace X] [MeasurableSpace Q]
  {ν : Measure X} {μ : Measure Q} [IsProbabilityMeasure μ]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : Gaussian.RankOneData (Lp H 2 ν) T}
  {Tr : PositiveTraceData T} {E : PositiveForm Tr}

/-- Each localization index may already contain the source spectral index.
Representatives are identified almost everywhere, which accommodates the
zero convention of the measurable L²-section construction. -/
structure ChannelRealization (D : VectorData R Tr E μ)
    (b : HilbertBasis ℕ ℂ V) where
  z : ℕ → Q → X → V
  source : ℕ → Q → X → H
  multiplier_measurable : ∀ a q, AEStronglyMeasurable (z a q) ν
  source_measurable : ∀ a q, AEStronglyMeasurable (source a q) ν
  unit : ∀ a, ∀ᵐ q ∂μ, ∀ᵐ x ∂ν, ‖z a q x‖ = 1
  source_integrable : ∀ a, ∀ᵐ q ∂μ, Integrable (fun x => ‖source a q x‖ ^ 2) ν
  vector_rep : ∀ a, ∀ᵐ q ∂μ, ∀ k,
    (fun x => D.vector a k q x) =ᵐ[ν] Repair.channelValue b (z a q) (source a q) k

namespace ChannelRealization

variable {D : VectorData R Tr E μ} {b : HilbertBasis ℕ ℂ V}
  (A : ChannelRealization D b)

/-- Signed density-test series are proved directly from the L²
representatives of this exact vector family. -/
theorem density_local (B : T →L[ℝ] ℝ) {w : X → ℝ} {C : ℝ}
    (hB : ∀ f : Lp H 2 ν, B (R.rankOne f) = ∫ x, w x * ‖f x‖ ^ 2 ∂ν)
    (hw : AEStronglyMeasurable w ν) (hC : 0 ≤ C)
    (hbound : ∀ᵐ x ∂ν, ‖w x‖ ≤ C) (a : ℕ) :
    ∀ᵐ q ∂μ, HasSum (fun k => B (R.rankOne (D.vector a k q)))
      (∫ x, w x * ‖A.source a q x‖ ^ 2 ∂ν) := by
  filter_upwards [A.unit a, A.source_integrable a, A.vector_rep a] with q hu hi hv
  have he (k : ℕ) : B (R.rankOne (D.vector a k q)) =
      ∫ x, w x * ‖Repair.channelValue b (A.z a q) (A.source a q) k x‖ ^ 2 ∂ν := by
    rw [hB]
    exact integral_congr_ae ((hv k).mono (fun x hx =>
      congrArg (fun v : H => w x * ‖v‖ ^ 2) hx))
  simpa only [he] using integrated_channel_density b (A.multiplier_measurable a q)
    (A.source_measurable a q) hw hC hbound hu hi

theorem density_eq (B : T →L[ℝ] ℝ) {w : X → ℝ} {C target : ℝ}
    (hB : ∀ f : Lp H 2 ν, B (R.rankOne f) = ∫ x, w x * ‖f x‖ ^ 2 ∂ν)
    (hw : AEStronglyMeasurable w ν) (hC : 0 ≤ C)
    (hbound : ∀ᵐ x ∂ν, ‖w x‖ ≤ C)
    (hsource : HasSum
      (fun a => ∫ q, ∫ x, w x * ‖A.source a q x‖ ^ 2 ∂ν ∂μ) target) :
    B D.output = target :=
  bounded_constraint_eq D B _ target (A.density_local B hB hw hC hbound) hsource

/-- Every bounded hard-fibre test uses the very same representative
equality as the density series. -/
theorem hard_local (W : H →L[ℂ] H) (B : T →L[ℝ] ℂ)
    (hB : ∀ f : Lp H 2 ν,
      B (R.rankOne f) = ∫ x, inner ℂ (f x) (W (f x)) ∂ν) (a : ℕ) :
    ∀ᵐ q ∂μ, HasSum (fun k => B (R.rankOne (D.vector a k q)))
      (∫ x, inner ℂ (A.source a q x) (W (A.source a q x)) ∂ν) := by
  filter_upwards [A.unit a, A.source_integrable a, A.vector_rep a] with q hu hi hv
  have he (k : ℕ) : B (R.rankOne (D.vector a k q)) =
      ∫ x, inner ℂ (Repair.channelValue b (A.z a q) (A.source a q) k x)
        (W (Repair.channelValue b (A.z a q) (A.source a q) k x)) ∂ν := by
    rw [hB]
    exact integral_congr_ae ((hv k).mono (fun _ hx =>
      congrArg (fun v : H => inner ℂ v (W v)) hx))
  simpa only [he] using Repair.integrated_channel_bounded_observable b W
    (A.multiplier_measurable a q) (A.source_measurable a q) hu hi

theorem hard_marginal_eq {F Test : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (M : T →L[ℝ] F) (tests : Test → F →L[ℝ] ℂ) (W : Test → H →L[ℂ] H)
    (separate : ∀ x y : F, (∀ t, tests t x = tests t y) → x = y) (target : F)
    (hrank : ∀ t (f : Lp H 2 ν), tests t (M (R.rankOne f)) =
      ∫ x, inner ℂ (f x) (W t (f x)) ∂ν)
    (hsource : ∀ t, HasSum
      (fun a => ∫ q, ∫ x,
        inner ℂ (A.source a q x) (W t (A.source a q x)) ∂ν ∂μ)
      (tests t target)) :
    M D.output = target := by
  apply separate
  intro t
  exact bounded_constraint_eq D ((tests t).comp M) _ _
    (A.hard_local (W t) ((tests t).comp M) (hrank t)) (hsource t)

/-- The original conditional source as an actual L² vector. -/
noncomputable def sourceVector (a : ℕ) (q : Q) : Lp H 2 ν :=
  Repair.toL2Section (μ := ν) (A.source a) q

/-- The vector-valued marginal series follows from countably many
separating hard-photon tests. Its target is the marginal of the original
source rank-one vector, not a supplied conditional-output identity. -/
theorem marginal_local {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (M : T →L[ℝ] F) (tests : ℕ → F →L[ℝ] ℂ) (W : ℕ → H →L[ℂ] H)
    (separate : ∀ x y : F, (∀ t, tests t x = tests t y) → x = y)
    (hrank : ∀ t (f : Lp H 2 ν), tests t (M (R.rankOne f)) =
      ∫ x, inner ℂ (f x) (W t (f x)) ∂ν) (a : ℕ) :
    ∀ᵐ q ∂μ, HasSum (fun k => M (R.rankOne (D.vector a k q)))
      (M (R.rankOne (A.sourceVector a q))) := by
  filter_upwards [D.mass_sum a, A.source_integrable a,
    ae_all_iff.mpr (fun t => A.hard_local (W t) ((tests t).comp M) (hrank t) a)]
    with q hm hi ht
  have hsource : MemLp (A.source a q) 2 ν :=
    (memLp_two_iff_integrable_sq_norm (A.source_measurable a q)).mpr hi
  have hrep : (A.sourceVector a q : X → H) =ᵐ[ν] A.source a q := by
    rw [sourceVector, Repair.toL2Section_eq hsource]
    exact hsource.coeFn_toLp
  have hsum := M.hasSum (Repair.rankOneSeries_hasSum R hm)
  have heq : M (D.conditional a q) = M (R.rankOne (A.sourceVector a q)) := by
    apply separate
    intro t
    have hs := ((tests t).hasSum hsum).unique (ht t)
    refine hs.trans ?_
    rw [hrank]
    exact integral_congr_ae (hrep.symm.mono (fun _ hx =>
      congrArg (fun v : H => inner ℂ v (W t v)) hx))
  rw [← heq]
  exact hsum

/-- The vector current integral used by a physical rank-one form trace. -/
noncomputable def currentVector (dz : ℕ → Q → X → V) (u : ℕ → Q → X → H)
    (a k : ℕ) (q : Q) : ℝ :=
  (∫ x, inner ℂ (Repair.channelValue b (A.z a q) (A.source a q) k x)
    (Repair.channelDerivative b (A.z a q) (dz a q) (u a q) (A.source a q) k x) ∂ν).re

/-- The source expression has the exact repair-current shift. The phase
and residual-field calculation identifies this with the original current. -/
noncomputable def currentSource (u : ℕ → Q → X → H) (s : ℕ → Q → X → ℝ)
    (a : ℕ) (q : Q) : ℝ :=
  (∫ x, inner ℂ (A.source a q x) (u a q x) +
    (s a q x : ℂ) * ‖A.source a q x‖ ^ 2 ∂ν).re

/-- The current uses the identical shifted source derivative that enters
the source kinetic energy, before the conditional parameter is integrated. -/
theorem currentSource_eq_shifted (u : ℕ → Q → X → H) (s : ℕ → Q → X → ℝ)
    (a : ℕ) (q : Q) :
    A.currentSource u s a q =
      (∫ x, inner ℂ (A.source a q x)
        (u a q x + (s a q x : ℂ) • A.source a q x) ∂ν).re := by
  unfold currentSource
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  simp only [inner_add_right, inner_smul_right, inner_self_eq_norm_sq_to_K]
  rfl

/-- The current series is derived from the connection and the actual
product derivative. No conditional current identity is assumed. -/
theorem current_local {dz : ℕ → Q → X → V} {u : ℕ → Q → X → H}
    {s : ℕ → Q → X → ℝ}
    (hdz : ∀ a, ∀ᵐ q ∂μ, AEStronglyMeasurable (dz a q) ν)
    (hu : ∀ a, ∀ᵐ q ∂μ, AEStronglyMeasurable (u a q) ν)
    (hconn : ∀ a, ∀ᵐ q ∂μ, ∀ᵐ x ∂ν,
      inner ℂ (A.z a q x) (dz a q x) = Complex.I * s a q x)
    (hkinetic : ∀ a, ∀ᵐ q ∂μ, Integrable (fun x => ‖u a q x‖ ^ 2 +
      2 * s a q x * (inner ℂ (u a q x) (A.source a q x)).re +
        ‖dz a q x‖ ^ 2 * ‖A.source a q x‖ ^ 2) ν) (a : ℕ) :
    ∀ᵐ q ∂μ, HasSum (fun k => A.currentVector dz u a k q) (A.currentSource u s a q) := by
  filter_upwards [A.unit a, A.source_integrable a, hdz a, hu a, hconn a, hkinetic a]
    with q hn hm hd huq hc hk
  exact Complex.hasSum_re (Repair.integrated_channel_current b
    (A.multiplier_measurable a q) hd huq (A.source_measurable a q) hn hc hm hk).2.1

/-- The unbounded current of the actual assembled output is identified
using only local physical rank-one calculus and the original source sum. -/
theorem current_eq {Test : Type*} (J : Test → FormObservable E)
    (dz : Test → ℕ → Q → X → V) (u : Test → ℕ → Q → X → H)
    (s : Test → ℕ → Q → X → ℝ)
    (hdz : ∀ t a, ∀ᵐ q ∂μ, AEStronglyMeasurable (dz t a q) ν)
    (hu : ∀ t a, ∀ᵐ q ∂μ, AEStronglyMeasurable (u t a q) ν)
    (hconn : ∀ t a, ∀ᵐ q ∂μ, ∀ᵐ x ∂ν,
      inner ℂ (A.z a q x) (dz t a q x) = Complex.I * s t a q x)
    (hkinetic : ∀ t a, ∀ᵐ q ∂μ, Integrable (fun x => ‖u t a q x‖ ^ 2 +
      2 * s t a q x * (inner ℂ (u t a q x) (A.source a q x)).re +
        ‖dz t a q x‖ ^ 2 * ‖A.source a q x‖ ^ 2) ν)
    (C : Test → ℝ) (hC : ∀ t, 0 ≤ C t)
    (hform : ∀ t n x, x ∈ Tr.positive → E.expectation x < ⊤ →
      ‖(J t).approximation n x‖ ≤ C t * (Tr.trace x + (E.expectation x).toReal))
    (hrank : ∀ t a, ∀ᵐ q ∂μ, ∀ k,
      Tendsto (fun n => (J t).approximation n (R.rankOne (D.vector a k q)))
        atTop (𝓝 (A.currentVector (dz t) (u t) a k q)))
    (target : Test → ℝ)
    (hsource : ∀ t, HasSum (fun a => ∫ q, A.currentSource (u t) (s t) a q ∂μ) (target t)) :
    (fun t => (J t).value D.output) = target :=
  current_constraint_eq D J (fun t => A.currentVector (dz t) (u t))
    (fun t => A.currentSource (u t) (s t)) target C hC hform hrank
    (fun t => A.current_local (hdz t) (hu t) (hconn t) (hkinetic t)) hsource

/-- Construct every constraint hypothesis from actual channel
representatives, standard rank-one trace calculus and the original source
decomposition. The Parseval and current identities are proved internally. -/
noncomputable def constraintData {DensityTest CurrentTest F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (density : DensityTest → T →L[ℝ] ℝ) (current : CurrentTest → FormObservable E)
    (marginal : T →L[ℝ] F)
    (weight : DensityTest → X → ℝ) (weightBound : DensityTest → ℝ)
    (weight_measurable : ∀ t, AEStronglyMeasurable (weight t) ν)
    (weightBound_nonneg : ∀ t, 0 ≤ weightBound t)
    (weight_bounded : ∀ t, ∀ᵐ x ∂ν, ‖weight t x‖ ≤ weightBound t)
    (density_rankOne : ∀ t (f : Lp H 2 ν), density t (R.rankOne f) =
      ∫ x, weight t x * ‖f x‖ ^ 2 ∂ν)
    (dz : CurrentTest → ℕ → Q → X → V) (u : CurrentTest → ℕ → Q → X → H)
    (s : CurrentTest → ℕ → Q → X → ℝ)
    (dz_measurable : ∀ t a, ∀ᵐ q ∂μ, AEStronglyMeasurable (dz t a q) ν)
    (u_measurable : ∀ t a, ∀ᵐ q ∂μ, AEStronglyMeasurable (u t a q) ν)
    (connection : ∀ t a, ∀ᵐ q ∂μ, ∀ᵐ x ∂ν,
      inner ℂ (A.z a q x) (dz t a q x) = Complex.I * s t a q x)
    (kinetic_integrable : ∀ t a, ∀ᵐ q ∂μ, Integrable (fun x => ‖u t a q x‖ ^ 2 +
      2 * s t a q x * (inner ℂ (u t a q x) (A.source a q x)).re +
        ‖dz t a q x‖ ^ 2 * ‖A.source a q x‖ ^ 2) ν)
    (currentBound : CurrentTest → ℝ) (currentBound_nonneg : ∀ t, 0 ≤ currentBound t)
    (current_bound : ∀ t n x, x ∈ Tr.positive → E.expectation x < ⊤ →
      ‖(current t).approximation n x‖ ≤
        currentBound t * (Tr.trace x + (E.expectation x).toReal))
    (current_rankOne : ∀ t a, ∀ᵐ q ∂μ, ∀ k,
      Tendsto (fun n => (current t).approximation n (R.rankOne (D.vector a k q)))
        atTop (𝓝 (A.currentVector (dz t) (u t) a k q)))
    (tests : ℕ → F →L[ℝ] ℂ) (W : ℕ → H →L[ℂ] H)
    (separate : ∀ x y : F, (∀ t, tests t x = tests t y) → x = y)
    (marginal_rankOne : ∀ t (f : Lp H 2 ν), tests t (marginal (R.rankOne f)) =
      ∫ x, inner ℂ (f x) (W t (f x)) ∂ν)
    (ρ : DensityTest → ℝ) (j : CurrentTest → ℝ) (θ : F)
    (density_source : ∀ t, HasSum
      (fun a => ∫ q, ∫ x, weight t x * ‖A.source a q x‖ ^ 2 ∂ν ∂μ) (ρ t))
    (current_source : ∀ t, HasSum
      (fun a => ∫ q, A.currentSource (u t) (s t) a q ∂μ) (j t))
    (marginal_source : HasSum
      (fun a => ∫ q, marginal (R.rankOne (A.sourceVector a q)) ∂μ) θ) :
    ConstraintData D density current marginal ρ j θ where
  densitySource t a q := ∫ x, weight t x * ‖A.source a q x‖ ^ 2 ∂ν
  currentVector t := A.currentVector (dz t) (u t)
  currentSource t := A.currentSource (u t) (s t)
  marginalSource a q := marginal (R.rankOne (A.sourceVector a q))
  density_local t := A.density_local (density t) (density_rankOne t)
    (weight_measurable t) (weightBound_nonneg t) (weight_bounded t)
  density_source := density_source
  currentConstant := currentBound
  currentConstant_nonneg := currentBound_nonneg
  current_bound := current_bound
  current_rankOne := current_rankOne
  current_local t := A.current_local (dz_measurable t) (u_measurable t)
    (connection t) (kinetic_integrable t)
  current_source := current_source
  marginal_local := A.marginal_local marginal tests W separate marginal_rankOne
  marginal_source := marginal_source

end ChannelRealization
end SingleSource

section VacuumTransport

variable {Q K H T U F DensityTest CurrentTest : Type*}
  [MeasurableSpace Q] {μ : Measure Q} [IsProbabilityMeasure μ]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {R : Gaussian.RankOneData K T} {S : Gaussian.RankOneData H U}
  {Tr : PositiveTraceData T} {Tr' : PositiveTraceData U}
  {E : PositiveForm Tr} {E' : PositiveForm Tr'}
  {D : VectorData R Tr E μ}
  {density : DensityTest → T →L[ℝ] ℝ} {current : CurrentTest → FormObservable E}
  {marginal : T →L[ℝ] F} {ρ : DensityTest → ℝ} {j : CurrentTest → ℝ} {θ : F}

/-- Vacuum preparation transports the local constraint data. Only
rank-one density, current and partial-trace identities enter. In
particular the unbounded currents need not have identical spectral
approximants on the hard and full Hilbert spaces. -/
noncomputable def ConstraintData.prepare
    (A : ConstraintData D density current marginal ρ j θ)
    (embedding : K →ₗᵢ[ℂ] H)
    (hpositive : S.positive ⊆ Tr'.positive) (htrace : S.trace = Tr'.trace)
    {c : ℝ} (hc : 0 ≤ c)
    (henergy : ∀ v, E.expectation (R.rankOne v) < ⊤ →
      E'.expectation (S.rankOne (embedding v)) ≤
        E.expectation (R.rankOne v) + ENNReal.ofReal (c * ‖v‖ ^ 2))
    (density' : DensityTest → U →L[ℝ] ℝ) (current' : CurrentTest → FormObservable E')
    (marginal' : U →L[ℝ] F)
    (hdensity : ∀ t v, density' t (S.rankOne (embedding v)) = density t (R.rankOne v))
    (hcurrent : ∀ t v, E.expectation (R.rankOne v) < ⊤ →
      (current' t).value (S.rankOne (embedding v)) = (current t).value (R.rankOne v))
    (hmarginal : ∀ v, marginal' (S.rankOne (embedding v)) = marginal (R.rankOne v))
    (C' : CurrentTest → ℝ) (hC' : ∀ t, 0 ≤ C' t)
    (hform' : ∀ t n x, x ∈ Tr'.positive → E'.expectation x < ⊤ →
      ‖(current' t).approximation n x‖ ≤ C' t * (Tr'.trace x + (E'.expectation x).toReal)) :
    ConstraintData (RemovalVacuum.prepareVectorData D embedding hpositive htrace hc henergy)
      density' current' marginal' ρ j θ where
  densitySource := A.densitySource
  currentVector := A.currentVector
  currentSource := A.currentSource
  marginalSource := A.marginalSource
  density_local t a := by
    filter_upwards [A.density_local t a] with q hq
    change HasSum (fun k => density' t (S.rankOne (embedding (D.vector a k q)))) _
    simpa only [hdensity] using hq
  density_source := A.density_source
  currentConstant := C'
  currentConstant_nonneg := hC'
  current_bound := hform'
  current_rankOne t a := by
    filter_upwards [D.vector_energy_le a, A.current_rankOne t a] with q he hj
    intro k
    have hf : E.expectation (R.rankOne (D.vector a k q)) < ⊤ :=
      (ENNReal.le_tsum k).trans_lt (he.trans_lt ENNReal.ofReal_lt_top)
    have hf' : E'.expectation (S.rankOne (embedding (D.vector a k q))) < ⊤ :=
      (henergy _ hf).trans_lt (ENNReal.add_lt_top.mpr ⟨hf, ENNReal.ofReal_lt_top⟩)
    have hv : (current t).value (R.rankOne (D.vector a k q)) = A.currentVector t a k q :=
      tendsto_nhds_unique ((current t).converges _
        (D.positive_compatible (R.rankOne_positive _)) hf) (hj k)
    have hl := (current' t).converges _ (hpositive (S.rankOne_positive _)) hf'
    rw [hcurrent t _ hf, hv] at hl
    exact hl
  current_local := A.current_local
  current_source := A.current_source
  marginal_local a := by
    filter_upwards [A.marginal_local a] with q hq
    change HasSum (fun k => marginal' (S.rankOne (embedding (D.vector a k q)))) _
    simpa only [hmarginal] using hq
  marginal_source := A.marginal_source

end VacuumTransport
end GptLean.RemovalConstraints
