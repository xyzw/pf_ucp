import GptLean.Repair.IntegratedChannel
import GptLean.Gaussian.Disintegration
import GptLean.PositiveForm
import GptLean.ObservableAssembly
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Data.Nat.Pairing

/-!
The repair channel as a convergent series of positive rank-one operators.
The vectors are the actual Hilbert-basis coordinate multipliers, embedded
in `Lp H 2 μ`. The channel is not an input to any of the results below.

`Gaussian.RankOneData` records standard rank-one trace calculus. For a
parameter-dependent family, strong measurability of its L2 sections is the
only additional input. Countable trace-class convergence, measurability,
positivity and trace preservation are proved here.
-/

namespace GptLean.Repair

open MeasureTheory Filter
open scoped ENNReal Topology

variable {X V H T : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]

/-- The norm of an actual L2 representative is its squared-density integral. -/
theorem toL2_norm_sq {f : X → H} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have hi := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (hf.toLp f)
  rw [L2.inner_def] at hi
  have he : (fun x => inner ℂ (hf.toLp f x) (hf.toLp f x)) =ᵐ[μ]
      (fun x => ((‖f x‖ ^ 2 : ℝ) : ℂ)) := by
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx]
    simp [inner_self_eq_norm_sq_to_K]
  rw [integral_congr_ae he, integral_complex_ofReal] at hi
  simpa only [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow,
    Complex.ofReal_re] using congrArg Complex.re hi.symm

/-- Every coordinate multiplier defines an actual square-integrable vector. -/
theorem channelValue_memLp (b : HilbertBasis ℕ ℂ V)
    {z : X → V} {ψ : X → H}
    (hz : AEStronglyMeasurable z μ) (hψ : AEStronglyMeasurable ψ μ)
    (hunit : ∀ᵐ x ∂μ, ‖z x‖ = 1)
    (hint : Integrable (fun x => ‖ψ x‖ ^ 2) μ) (a : ℕ) :
    MemLp (channelValue b z ψ a) 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm (channelValue_measurable b hz hψ a)).mpr
  apply hint.mono' ((channelValue_measurable b hz hψ a).norm.pow 2)
  filter_upwards [hunit] with x hx
  change ‖‖channelValue b z ψ a x‖ ^ 2‖ ≤ ‖ψ x‖ ^ 2
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hc := coordinate_norm_le b (z x) a
  rw [hx] at hc
  dsimp [channelValue]
  rw [norm_smul, mul_pow]
  have hc2 : ‖coordinate b (z x) a‖ ^ 2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) hc 2
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hc2 (sq_nonneg ‖ψ x‖)

/-- The vector used in the rank-one Kraus series, without a choice of representatives. -/
noncomputable def channelVector (b : HilbertBasis ℕ ℂ V)
    {z : X → V} {ψ : X → H}
    (hz : AEStronglyMeasurable z μ) (hψ : AEStronglyMeasurable ψ μ)
    (hunit : ∀ᵐ x ∂μ, ‖z x‖ = 1)
    (hint : Integrable (fun x => ‖ψ x‖ ^ 2) μ) (a : ℕ) : Lp H 2 μ :=
  (channelValue_memLp b hz hψ hunit hint a).toLp (channelValue b z ψ a)

theorem channelVector_norm_sq (b : HilbertBasis ℕ ℂ V)
    {z : X → V} {ψ : X → H}
    (hz : AEStronglyMeasurable z μ) (hψ : AEStronglyMeasurable ψ μ)
    (hunit : ∀ᵐ x ∂μ, ‖z x‖ = 1)
    (hint : Integrable (fun x => ‖ψ x‖ ^ 2) μ) (a : ℕ) :
    ‖channelVector b hz hψ hunit hint a‖ ^ 2 =
      ∫ x, ‖channelValue b z ψ a x‖ ^ 2 ∂μ :=
  toL2_norm_sq (channelValue_memLp b hz hψ hunit hint a)

/-- Parseval proves the total mass of the constructed L2 vectors. -/
theorem channelVector_mass (b : HilbertBasis ℕ ℂ V)
    {z : X → V} {ψ : X → H}
    (hz : AEStronglyMeasurable z μ) (hψ : AEStronglyMeasurable ψ μ)
    (hunit : ∀ᵐ x ∂μ, ‖z x‖ = 1)
    (hint : Integrable (fun x => ‖ψ x‖ ^ 2) μ) :
    HasSum (fun a => ‖channelVector b hz hψ hunit hint a‖ ^ 2)
      (∫ x, ‖ψ x‖ ^ 2 ∂μ) := by
  simpa only [channelVector_norm_sq] using integrated_channel_mass b hz hψ hunit hint

/-- The L2 inner product agrees with the integral of representatives. -/
theorem toL2_inner {f g : X → H} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℂ (hf.toLp f) (hg.toLp g) = ∫ x, inner ℂ (f x) (g x) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy]

/-- The derived channel derivative belongs to L2 whenever the exact kinetic
density is integrable. -/
theorem channelDerivative_memLp (b : HilbertBasis ℕ ℂ V)
    {z dz : X → V} {u ψ : X → H} {s : X → ℝ}
    (hz : AEStronglyMeasurable z μ) (hdz : AEStronglyMeasurable dz μ)
    (hu : AEStronglyMeasurable u μ) (hψ : AEStronglyMeasurable ψ μ)
    (hunit : ∀ᵐ x ∂μ, ‖z x‖ = 1)
    (hconn : ∀ᵐ x ∂μ, inner ℂ (z x) (dz x) = Complex.I * s x)
    (hint : Integrable (fun x => ‖u x‖ ^ 2 +
      2 * s x * (inner ℂ (u x) (ψ x)).re + ‖dz x‖ ^ 2 * ‖ψ x‖ ^ 2) μ) (a : ℕ) :
    MemLp (channelDerivative b z dz u ψ a) 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm
    (channelDerivative_measurable b hz hdz hu hψ a)).mpr
  apply integrable_term_of_nonnegative_hasSum
    (fun a => (channelDerivative_measurable b hz hdz hu hψ a).norm.pow 2)
    (fun a => Eventually.of_forall (fun x => sq_nonneg _)) _ hint a
  filter_upwards [hunit, hconn] with x hx hc
  exact coordinate_channel_energy b hx hc (u x) (ψ x)

/-- The L2 derivative vector used in the quadratic form evaluation. -/
noncomputable def channelDerivativeVector (b : HilbertBasis ℕ ℂ V)
    {z dz : X → V} {u ψ : X → H} {s : X → ℝ}
    (hz : AEStronglyMeasurable z μ) (hdz : AEStronglyMeasurable dz μ)
    (hu : AEStronglyMeasurable u μ) (hψ : AEStronglyMeasurable ψ μ)
    (hunit : ∀ᵐ x ∂μ, ‖z x‖ = 1)
    (hconn : ∀ᵐ x ∂μ, inner ℂ (z x) (dz x) = Complex.I * s x)
    (hint : Integrable (fun x => ‖u x‖ ^ 2 +
      2 * s x * (inner ℂ (u x) (ψ x)).re + ‖dz x‖ ^ 2 * ‖ψ x‖ ^ 2) μ) (a : ℕ) :
    Lp H 2 μ :=
  (channelDerivative_memLp b hz hdz hu hψ hunit hconn hint a).toLp
    (channelDerivative b z dz u ψ a)

/-- The exact energy series is an identity of actual Hilbert-space vectors. -/
theorem channelDerivativeVector_energy (b : HilbertBasis ℕ ℂ V)
    {z dz : X → V} {u ψ : X → H} {s : X → ℝ}
    (hz : AEStronglyMeasurable z μ) (hdz : AEStronglyMeasurable dz μ)
    (hu : AEStronglyMeasurable u μ) (hψ : AEStronglyMeasurable ψ μ)
    (hunit : ∀ᵐ x ∂μ, ‖z x‖ = 1)
    (hconn : ∀ᵐ x ∂μ, inner ℂ (z x) (dz x) = Complex.I * s x)
    (hint : Integrable (fun x => ‖u x‖ ^ 2 +
      2 * s x * (inner ℂ (u x) (ψ x)).re + ‖dz x‖ ^ 2 * ‖ψ x‖ ^ 2) μ) :
    HasSum (fun a => ‖channelDerivativeVector b hz hdz hu hψ hunit hconn hint a‖ ^ 2)
      (∫ x, ‖u x‖ ^ 2 + 2 * s x * (inner ℂ (u x) (ψ x)).re +
        ‖dz x‖ ^ 2 * ‖ψ x‖ ^ 2 ∂μ) := by
  simpa only [channelDerivativeVector, toL2_norm_sq] using
    integrated_channel_energy b hz hdz hu hψ hunit hconn hint

/-- The current series is an identity of the constructed L2 values and
derivatives, including absolute integrability of its representatives. -/
theorem channelVector_current (b : HilbertBasis ℕ ℂ V)
    {z dz : X → V} {u ψ : X → H} {s : X → ℝ}
    (hz : AEStronglyMeasurable z μ) (hdz : AEStronglyMeasurable dz μ)
    (hu : AEStronglyMeasurable u μ) (hψ : AEStronglyMeasurable ψ μ)
    (hunit : ∀ᵐ x ∂μ, ‖z x‖ = 1)
    (hconn : ∀ᵐ x ∂μ, inner ℂ (z x) (dz x) = Complex.I * s x)
    (hmass : Integrable (fun x => ‖ψ x‖ ^ 2) μ)
    (hint : Integrable (fun x => ‖u x‖ ^ 2 +
      2 * s x * (inner ℂ (u x) (ψ x)).re + ‖dz x‖ ^ 2 * ‖ψ x‖ ^ 2) μ) :
    HasSum (fun a => inner ℂ (channelVector b hz hψ hunit hmass a)
      (channelDerivativeVector b hz hdz hu hψ hunit hconn hint a))
      (∫ x, inner ℂ (ψ x) (u x) + (s x : ℂ) * ‖ψ x‖ ^ 2 ∂μ) := by
  simpa only [channelVector, channelDerivativeVector, toL2_inner] using
    (integrated_channel_current b hz hdz hu hψ hunit hconn hmass hint).2.1

section RankOneSeries

variable {K Q F : Type*} [NormedAddCommGroup K]
  [MeasurableSpace Q] {ν : Measure Q}
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The trace-class output is defined by its rank-one components. -/
noncomputable def rankOneSeries (R : Gaussian.RankOneData K T) (v : ℕ → K) : T :=
  ∑' a, R.rankOne (v a)

/-- Square-summability of vectors proves convergence in trace norm. -/
theorem rankOneSeries_hasSum (R : Gaussian.RankOneData K T) {v : ℕ → K}
    {mass : ℝ} (hmass : HasSum (fun a => ‖v a‖ ^ 2) mass) :
    HasSum (fun a => R.rankOne (v a)) (rankOneSeries R v) := by
  have hs : Summable (fun a => ‖R.rankOne (v a)‖) := by
    simpa only [R.norm_rankOne] using hmass.summable
  exact hs.of_norm.hasSum

theorem rankOneSeries_positive (R : Gaussian.RankOneData K T) {v : ℕ → K}
    {mass : ℝ} (hmass : HasSum (fun a => ‖v a‖ ^ 2) mass) :
    rankOneSeries R v ∈ R.positive := by
  apply R.closed_positive.mem_of_tendsto (rankOneSeries_hasSum R hmass)
  apply Eventually.of_forall
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using R.zero_positive
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using R.add_positive (R.rankOne_positive (v a)) ih

theorem rankOneSeries_trace (R : Gaussian.RankOneData K T) {v : ℕ → K}
    {mass : ℝ} (hmass : HasSum (fun a => ‖v a‖ ^ 2) mass) :
    R.trace (rankOneSeries R v) = mass := by
  have ht := R.trace.hasSum (rankOneSeries_hasSum R hmass)
  simp only [R.trace_rankOne] at ht
  exact ht.unique hmass

omit [CompleteSpace T] in
theorem rankOneSeries_norm_le (R : Gaussian.RankOneData K T) {v : ℕ → K}
    {mass : ℝ} (hmass : HasSum (fun a => ‖v a‖ ^ 2) mass) :
    ‖rankOneSeries R v‖ ≤ mass := by
  have hs : Summable (fun a => ‖R.rankOne (v a)‖) := by
    simpa only [R.norm_rankOne] using hmass.summable
  simpa only [rankOneSeries, R.norm_rankOne, hmass.tsum_eq] using norm_tsum_le_tsum_norm hs

/-- Measurability of the vectors passes to the convergent operator series.
No measurable trace-class channel is assumed. -/
theorem rankOneSeries_aestronglyMeasurable (R : Gaussian.RankOneData K T)
    {v : ℕ → Q → K} {mass : Q → ℝ}
    (hv : ∀ a, AEStronglyMeasurable (v a) ν)
    (hmass : ∀ᵐ u ∂ν, HasSum (fun a => ‖v a u‖ ^ 2) (mass u)) :
    AEStronglyMeasurable (fun u => rankOneSeries R (fun a => v a u)) ν := by
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun s : Finset ℕ => fun u => ∑ a ∈ s, R.rankOne (v a u))
  · intro s
    exact s.aestronglyMeasurable_fun_sum
      (fun a _ => R.continuous_rankOne.comp_aestronglyMeasurable (hv a))
  · filter_upwards [hmass] with u hu
    exact rankOneSeries_hasSum R hu

/-- Integrability follows from the input mass before taking any integral. -/
theorem rankOneSeries_integrable (R : Gaussian.RankOneData K T)
    {v : ℕ → Q → K} {mass : Q → ℝ}
    (hv : ∀ a, AEStronglyMeasurable (v a) ν)
    (hmass : ∀ᵐ u ∂ν, HasSum (fun a => ‖v a u‖ ^ 2) (mass u))
    (hmassint : Integrable mass ν) :
    Integrable (fun u => rankOneSeries R (fun a => v a u)) ν := by
  apply hmassint.mono' (rankOneSeries_aestronglyMeasurable R hv hmass)
  filter_upwards [hmass] with u hu
  exact rankOneSeries_norm_le R hu

/-- Rank-one evaluation and a proved scalar series determine every bounded
observable of the constructed channel. -/
theorem rankOneSeries_observable (R : Gaussian.RankOneData K T) (B : T →L[ℝ] F)
    {v : ℕ → K} {mass : ℝ} {value : F}
    (hmass : HasSum (fun a => ‖v a‖ ^ 2) mass)
    (hvalue : HasSum (fun a => B (R.rankOne (v a))) value) :
    B (rankOneSeries R v) = value :=
  (B.hasSum (rankOneSeries_hasSum R hmass)).unique hvalue

/-- Unbounded positive expectations commute with this actual trace-class
series by monotone spectral truncation. -/
theorem rankOneSeries_expectation (R : Gaussian.RankOneData K T)
    {Tr : RemovalState.PositiveTraceData T} (E : RemovalState.PositiveForm Tr)
    (hpositive : R.positive ⊆ Tr.positive) {v : ℕ → K} {mass : ℝ}
    (hmass : HasSum (fun a => ‖v a‖ ^ 2) mass) :
    E.expectation (rankOneSeries R v) = ∑' a, E.expectation (R.rankOne (v a)) :=
  E.expectation_tsum (rankOneSeries_hasSum R hmass).summable
    (fun a => hpositive (R.rankOne_positive (v a)))

/-- A fixed enumeration of source-vector and Kraus-vector pairs. -/
noncomputable def flattenVectors (v : ℕ → ℕ → K) (a : ℕ) : K :=
  v (Nat.unpair a).1 (Nat.unpair a).2

set_option maxHeartbeats 800000 in
/-- Nonnegative mass sums justify flattening both countable indices. -/
theorem flattenVectors_mass {v : ℕ → ℕ → K} {mass : ℕ → ℝ} {total : ℝ}
    (hlocal : ∀ n, HasSum (fun a => ‖v n a‖ ^ 2) (mass n))
    (hmass : HasSum mass total) :
    HasSum (fun a => ‖flattenVectors v a‖ ^ 2) total := by
  have hf : (fun n => ∑' a, ‖v n a‖ ^ 2) = mass :=
    funext (fun n => (hlocal n).tsum_eq)
  have hp : Summable (fun p : ℕ × ℕ => ‖v p.1 p.2‖ ^ 2) := by
    apply (summable_prod_of_nonneg (fun p => sq_nonneg ‖v p.1 p.2‖)).mpr
    refine ⟨fun n => (hlocal n).summable, ?_⟩
    rw [hf]
    exact hmass.summable
  have hprod : HasSum (fun p : ℕ × ℕ => ‖v p.1 p.2‖ ^ 2) total := by
    convert hp.hasSum using 1
    rw [hp.tsum_prod' (fun n => (hlocal n).summable), hf, hmass.tsum_eq]
  change HasSum ((fun p : ℕ × ℕ => ‖v p.1 p.2‖ ^ 2) ∘ Nat.pairEquiv.symm) total
  exact (Nat.pairEquiv.symm.hasSum_iff
    (f := fun p : ℕ × ℕ => ‖v p.1 p.2‖ ^ 2) (a := total)).mpr hprod

/-- Rank-one form evaluation gives the energy of the constructed series.
Output form-domain membership is a consequence of the finite scalar sum. -/
theorem rankOneSeries_energy (R : Gaussian.RankOneData K T)
    {Tr : RemovalState.PositiveTraceData T} (E : RemovalState.PositiveForm Tr)
    (hpositive : R.positive ⊆ Tr.positive) {v d : ℕ → K} {mass energy : ℝ}
    (hmass : HasSum (fun a => ‖v a‖ ^ 2) mass)
    (henergy : HasSum (fun a => ‖d a‖ ^ 2) energy)
    (hform : ∀ a, E.expectation (R.rankOne (v a)) = ENNReal.ofReal (‖d a‖ ^ 2)) :
    E.expectation (rankOneSeries R v) = ENNReal.ofReal energy := by
  rw [rankOneSeries_expectation R E hpositive hmass]
  simp_rw [hform]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun a => sq_nonneg _) henergy.summable,
    henergy.tsum_eq]

/-- Rank-one spectral current calculus passes to the actual repaired
operator by a proved dominated limit. No current identity for the output
operator is assumed. The uniform bound is the usual quadratic Young bound. -/
theorem rankOneSeries_current [InnerProductSpace ℂ K]
    (R : Gaussian.RankOneData K T)
    {Tr : RemovalState.PositiveTraceData T} {E : RemovalState.PositiveForm Tr}
    (J : RemovalState.FormObservable E) (hpositive : R.positive ⊆ Tr.positive)
    {v d : ℕ → K} {mass energy : ℝ}
    (hmass : HasSum (fun a => ‖v a‖ ^ 2) mass)
    (henergy : HasSum (fun a => ‖d a‖ ^ 2) energy)
    (hform : ∀ a, E.expectation (R.rankOne (v a)) = ENNReal.ofReal (‖d a‖ ^ 2))
    (hcurrent : ∀ a, Tendsto (fun n => J.approximation n (R.rankOne (v a)))
      atTop (𝓝 ((inner ℂ (v a) (d a)).re)))
    (hbound : ∀ n a, ‖J.approximation n (R.rankOne (v a))‖ ≤
      (‖v a‖ ^ 2 + ‖d a‖ ^ 2) / 2) :
    J.value (rankOneSeries R v) = ∑' a, (inner ℂ (v a) (d a)).re := by
  have hs := (rankOneSeries_hasSum R hmass).summable
  have hb : Summable (fun a => (‖v a‖ ^ 2 + ‖d a‖ ^ 2) / 2) :=
    (hmass.summable.add henergy.summable).div_const 2
  have hl := tendsto_tsum_of_dominated_convergence hb hcurrent
    (Eventually.of_forall hbound)
  have hpos := hpositive (rankOneSeries_positive R hmass)
  have hfinite : E.expectation (rankOneSeries R v) < ⊤ := by
    rw [rankOneSeries_energy R E hpositive hmass henergy hform]
    exact ENNReal.ofReal_lt_top
  apply tendsto_nhds_unique (J.converges _ hpos hfinite)
  simpa only [rankOneSeries, (J.approximation _).map_tsum hs] using hl

end RankOneSeries

/-- The concrete output on a rank-one input. -/
noncomputable def traceChannel (R : Gaussian.RankOneData (Lp H 2 μ) T)
    (b : HilbertBasis ℕ ℂ V) {z : X → V} {ψ : X → H}
    (hz : AEStronglyMeasurable z μ) (hψ : AEStronglyMeasurable ψ μ)
    (hunit : ∀ᵐ x ∂μ, ‖z x‖ = 1)
    (hint : Integrable (fun x => ‖ψ x‖ ^ 2) μ) : T :=
  rankOneSeries R (channelVector b hz hψ hunit hint)

theorem traceChannel_positive (R : Gaussian.RankOneData (Lp H 2 μ) T)
    (b : HilbertBasis ℕ ℂ V) {z : X → V} {ψ : X → H}
    (hz : AEStronglyMeasurable z μ) (hψ : AEStronglyMeasurable ψ μ)
    (hunit : ∀ᵐ x ∂μ, ‖z x‖ = 1)
    (hint : Integrable (fun x => ‖ψ x‖ ^ 2) μ) :
    traceChannel R b hz hψ hunit hint ∈ R.positive :=
  rankOneSeries_positive R (channelVector_mass b hz hψ hunit hint)

theorem traceChannel_trace (R : Gaussian.RankOneData (Lp H 2 μ) T)
    (b : HilbertBasis ℕ ℂ V) {z : X → V} {ψ : X → H}
    (hz : AEStronglyMeasurable z μ) (hψ : AEStronglyMeasurable ψ μ)
    (hunit : ∀ᵐ x ∂μ, ‖z x‖ = 1)
    (hint : Integrable (fun x => ‖ψ x‖ ^ 2) μ) :
    R.trace (traceChannel R b hz hψ hunit hint) = ∫ x, ‖ψ x‖ ^ 2 ∂μ :=
  rankOneSeries_trace R (channelVector_mass b hz hψ hunit hint)

omit [CompleteSpace T] in
theorem traceChannel_norm_le (R : Gaussian.RankOneData (Lp H 2 μ) T)
    (b : HilbertBasis ℕ ℂ V) {z : X → V} {ψ : X → H}
    (hz : AEStronglyMeasurable z μ) (hψ : AEStronglyMeasurable ψ μ)
    (hunit : ∀ᵐ x ∂μ, ‖z x‖ = 1)
    (hint : Integrable (fun x => ‖ψ x‖ ^ 2) μ) :
    ‖traceChannel R b hz hψ hunit hint‖ ≤ ∫ x, ‖ψ x‖ ^ 2 ∂μ :=
  rankOneSeries_norm_le R (channelVector_mass b hz hψ hunit hint)

/-- The parameter-dependent trace-class channel is measurable as a conclusion
of measurability of the concrete L2 multiplier sections. -/
theorem traceChannel_aestronglyMeasurable {Q : Type*} [MeasurableSpace Q]
    {ν : Measure Q} (R : Gaussian.RankOneData (Lp H 2 μ) T)
    (b : HilbertBasis ℕ ℂ V) {z : Q → X → V} {ψ : Q → X → H}
    (hz : ∀ q, AEStronglyMeasurable (z q) μ)
    (hψ : ∀ q, AEStronglyMeasurable (ψ q) μ)
    (hunit : ∀ q, ∀ᵐ x ∂μ, ‖z q x‖ = 1)
    (hint : ∀ q, Integrable (fun x => ‖ψ q x‖ ^ 2) μ)
    (hsections : ∀ a, AEStronglyMeasurable
      (fun q => channelVector b (hz q) (hψ q) (hunit q) (hint q) a) ν) :
    AEStronglyMeasurable
      (fun q => traceChannel R b (hz q) (hψ q) (hunit q) (hint q)) ν := by
  apply rankOneSeries_aestronglyMeasurable R hsections
  exact Eventually.of_forall (fun q => channelVector_mass b (hz q) (hψ q) (hunit q) (hint q))

/-- The conditional output is integrable in trace norm from the source mass. -/
theorem traceChannel_integrable {Q : Type*} [MeasurableSpace Q]
    {ν : Measure Q} (R : Gaussian.RankOneData (Lp H 2 μ) T)
    (b : HilbertBasis ℕ ℂ V) {z : Q → X → V} {ψ : Q → X → H}
    (hz : ∀ q, AEStronglyMeasurable (z q) μ)
    (hψ : ∀ q, AEStronglyMeasurable (ψ q) μ)
    (hunit : ∀ q, ∀ᵐ x ∂μ, ‖z q x‖ = 1)
    (hint : ∀ q, Integrable (fun x => ‖ψ q x‖ ^ 2) μ)
    (hsections : ∀ a, AEStronglyMeasurable
      (fun q => channelVector b (hz q) (hψ q) (hunit q) (hint q) a) ν)
    (hmass : Integrable (fun q => ∫ x, ‖ψ q x‖ ^ 2 ∂μ) ν) :
    Integrable (fun q => traceChannel R b (hz q) (hψ q) (hunit q) (hint q)) ν := by
  apply rankOneSeries_integrable R hsections _ hmass
  exact Eventually.of_forall (fun q => channelVector_mass b (hz q) (hψ q) (hunit q) (hint q))

section MixedChannel

variable (R : Gaussian.RankOneData (Lp H 2 μ) T) (b : HilbertBasis ℕ ℂ V)
  {z : X → V} {ψ : ℕ → X → H}
  (hz : AEStronglyMeasurable z μ) (hψ : ∀ n, AEStronglyMeasurable (ψ n) μ)
  (hunit : ∀ᵐ x ∂μ, ‖z x‖ = 1)
  (hint : ∀ n, Integrable (fun x => ‖ψ n x‖ ^ 2) μ)

/-- The mixed conditional state is the rank-one series over both the input
spectral vectors and the actual coordinate multipliers. -/
noncomputable def mixedTraceChannel : T :=
  rankOneSeries R (flattenVectors (fun n => channelVector b hz (hψ n) hunit (hint n)))

theorem mixedChannelVector_mass {mass : ℝ}
    (hmass : HasSum (fun n => ∫ x, ‖ψ n x‖ ^ 2 ∂μ) mass) :
    HasSum (fun a => ‖flattenVectors
      (fun n => channelVector b hz (hψ n) hunit (hint n)) a‖ ^ 2) mass :=
  flattenVectors_mass (fun n => channelVector_mass b hz (hψ n) hunit (hint n)) hmass

theorem mixedTraceChannel_positive {mass : ℝ}
    (hmass : HasSum (fun n => ∫ x, ‖ψ n x‖ ^ 2 ∂μ) mass) :
    mixedTraceChannel R b hz hψ hunit hint ∈ R.positive :=
  rankOneSeries_positive R (mixedChannelVector_mass b hz hψ hunit hint hmass)

theorem mixedTraceChannel_trace {mass : ℝ}
    (hmass : HasSum (fun n => ∫ x, ‖ψ n x‖ ^ 2 ∂μ) mass) :
    R.trace (mixedTraceChannel R b hz hψ hunit hint) = mass :=
  rankOneSeries_trace R (mixedChannelVector_mass b hz hψ hunit hint hmass)

omit [CompleteSpace T] in
theorem mixedTraceChannel_norm_le {mass : ℝ}
    (hmass : HasSum (fun n => ∫ x, ‖ψ n x‖ ^ 2 ∂μ) mass) :
    ‖mixedTraceChannel R b hz hψ hunit hint‖ ≤ mass :=
  rankOneSeries_norm_le R (mixedChannelVector_mass b hz hψ hunit hint hmass)

/-- The flattened definition agrees with the nested physical channel sum. -/
theorem mixedTraceChannel_eq_tsum {mass : ℝ}
    (hmass : HasSum (fun n => ∫ x, ‖ψ n x‖ ^ 2 ∂μ) mass) :
    mixedTraceChannel R b hz hψ hunit hint =
      ∑' n, traceChannel R b hz (hψ n) hunit (hint n) := by
  let v := fun n => channelVector b hz (hψ n) hunit (hint n)
  have hs := (rankOneSeries_hasSum R
    (mixedChannelVector_mass b hz hψ hunit hint hmass)).summable
  have hp : Summable (fun p : ℕ × ℕ => R.rankOne (v p.1 p.2)) :=
    Nat.pairEquiv.symm.summable_iff.mp hs
  change (∑' a, R.rankOne (flattenVectors v a)) = ∑' n, ∑' a, R.rankOne (v n a)
  rw [show (∑' a, R.rankOne (flattenVectors v a)) =
      ∑' p : ℕ × ℕ, R.rankOne (v p.1 p.2) from
    Nat.pairEquiv.symm.tsum_eq (fun p => R.rankOne (v p.1 p.2))]
  exact hp.tsum_prod' (fun n =>
    (rankOneSeries_hasSum R (channelVector_mass b hz (hψ n) hunit (hint n))).summable)

/-- Positive unbounded forms are evaluated by the same double rank-one
series, with possibly infinite expectations retained. -/
theorem mixedTraceChannel_expectation {Tr : RemovalState.PositiveTraceData T}
    (E : RemovalState.PositiveForm Tr) (hpositive : R.positive ⊆ Tr.positive)
    {mass : ℝ} (hmass : HasSum (fun n => ∫ x, ‖ψ n x‖ ^ 2 ∂μ) mass) :
    E.expectation (mixedTraceChannel R b hz hψ hunit hint) =
      ∑' n, ∑' a, E.expectation (R.rankOne (channelVector b hz (hψ n) hunit (hint n) a)) := by
  rw [mixedTraceChannel, rankOneSeries_expectation R E hpositive
    (mixedChannelVector_mass b hz hψ hunit hint hmass)]
  exact (Nat.pairEquiv.symm.tsum_eq (fun p : ℕ × ℕ => E.expectation
    (R.rankOne (channelVector b hz (hψ p.1) hunit (hint p.1) p.2)))).trans
      ENNReal.tsum_prod'

end MixedChannel

/-- Parameter measurability of the mixed conditional output is proved from
the individual concrete L2 multiplier sections. -/
theorem mixedTraceChannel_aestronglyMeasurable {Q : Type*} [MeasurableSpace Q]
    {ν : Measure Q} (R : Gaussian.RankOneData (Lp H 2 μ) T)
    (b : HilbertBasis ℕ ℂ V) {z : Q → X → V} {ψ : ℕ → Q → X → H}
    (hz : ∀ q, AEStronglyMeasurable (z q) μ)
    (hψ : ∀ n q, AEStronglyMeasurable (ψ n q) μ)
    (hunit : ∀ q, ∀ᵐ x ∂μ, ‖z q x‖ = 1)
    (hint : ∀ n q, Integrable (fun x => ‖ψ n q x‖ ^ 2) μ)
    (hsections : ∀ n a, AEStronglyMeasurable
      (fun q => channelVector b (hz q) (hψ n q) (hunit q) (hint n q) a) ν)
    {mass : Q → ℝ}
    (hmass : ∀ᵐ q ∂ν, HasSum (fun n => ∫ x, ‖ψ n q x‖ ^ 2 ∂μ) (mass q)) :
    AEStronglyMeasurable (fun q => mixedTraceChannel R b (hz q)
      (fun n => hψ n q) (hunit q) (fun n => hint n q)) ν := by
  apply rankOneSeries_aestronglyMeasurable R
    (fun a => hsections (Nat.unpair a).1 (Nat.unpair a).2)
  filter_upwards [hmass] with q hq
  exact mixedChannelVector_mass b (hz q) (fun n => hψ n q) (hunit q)
    (fun n => hint n q) hq

/-- Trace-norm integrability of a mixed conditional output follows from its
source mass, before integrating the output. -/
theorem mixedTraceChannel_integrable {Q : Type*} [MeasurableSpace Q]
    {ν : Measure Q} (R : Gaussian.RankOneData (Lp H 2 μ) T)
    (b : HilbertBasis ℕ ℂ V) {z : Q → X → V} {ψ : ℕ → Q → X → H}
    (hz : ∀ q, AEStronglyMeasurable (z q) μ)
    (hψ : ∀ n q, AEStronglyMeasurable (ψ n q) μ)
    (hunit : ∀ q, ∀ᵐ x ∂μ, ‖z q x‖ = 1)
    (hint : ∀ n q, Integrable (fun x => ‖ψ n q x‖ ^ 2) μ)
    (hsections : ∀ n a, AEStronglyMeasurable
      (fun q => channelVector b (hz q) (hψ n q) (hunit q) (hint n q) a) ν)
    {mass : Q → ℝ}
    (hmass : ∀ᵐ q ∂ν, HasSum (fun n => ∫ x, ‖ψ n q x‖ ^ 2 ∂μ) (mass q))
    (hmassint : Integrable mass ν) :
    Integrable (fun q => mixedTraceChannel R b (hz q)
      (fun n => hψ n q) (hunit q) (fun n => hint n q)) ν := by
  apply rankOneSeries_integrable R
    (fun a => hsections (Nat.unpair a).1 (Nat.unpair a).2) _ hmassint
  filter_upwards [hmass] with q hq
  exact mixedChannelVector_mass b (hz q) (fun n => hψ n q) (hunit q)
    (fun n => hint n q) hq

/-- Bounded fibre observables include every bounded hard-photon observable.
Their expectation is preserved before forming the trace-class series. -/
theorem integrated_channel_bounded_observable (b : HilbertBasis ℕ ℂ V)
    (W : H →L[ℂ] H) {z : X → V} {ψ : X → H}
    (hz : AEStronglyMeasurable z μ) (hψ : AEStronglyMeasurable ψ μ)
    (hunit : ∀ᵐ x ∂μ, ‖z x‖ = 1)
    (hint : Integrable (fun x => ‖ψ x‖ ^ 2) μ) :
    HasSum (fun a => ∫ x, inner ℂ (channelValue b z ψ a x)
      (W (channelValue b z ψ a x)) ∂μ)
      (∫ x, inner ℂ (ψ x) (W (ψ x)) ∂μ) := by
  have hWψ : AEStronglyMeasurable (fun x => W (ψ x)) μ :=
    W.continuous.comp_aestronglyMeasurable hψ
  have hWint : Integrable (fun x => ‖W (ψ x)‖ ^ 2) μ := by
    apply (hint.const_mul (‖W‖ ^ 2)).mono' (hWψ.norm.pow 2)
    filter_upwards with x
    change ‖‖W (ψ x)‖ ^ 2‖ ≤ ‖W‖ ^ 2 * ‖ψ x‖ ^ 2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h := W.le_opNorm (ψ x)
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg (W (ψ x))) h 2
  have hm : ∀ᵐ x ∂μ, HasSum (fun a => ‖channelValue b z ψ a x‖ ^ 2) (‖ψ x‖ ^ 2) := by
    filter_upwards [hunit] with x hx
    simpa only [channelValue, hx, one_pow, one_mul] using
      coordinate_smul_norm_sq_hasSum b (z x) (ψ x)
  have hk : ∀ᵐ x ∂μ, HasSum
      (fun a => ‖channelValue b z (fun y => W (ψ y)) a x‖ ^ 2) (‖W (ψ x)‖ ^ 2) := by
    filter_upwards [hunit] with x hx
    simpa only [channelValue, hx, one_pow, one_mul] using
      coordinate_smul_norm_sq_hasSum b (z x) (W (ψ x))
  have hc : ∀ᵐ x ∂μ, HasSum
      (fun a => inner ℂ (channelValue b z ψ a x)
        (channelValue b z (fun y => W (ψ y)) a x))
      (inner ℂ (ψ x) (W (ψ x))) := by
    filter_upwards [hunit] with x hx
    simpa [channelValue, inner_self_eq_norm_sq_to_K, hx] using
      coordinate_smul_inner_hasSum b (z x) (z x) (ψ x) (W (ψ x))
  have h := (integrated_inner_series
    (fun a => channelValue_measurable b hz hψ a)
    (fun a => channelValue_measurable b hz hWψ a) hm hk hc hint hWint).1
  simpa only [channelValue, map_smul] using h

/-- The actual trace-class channel preserves each bounded fibre observable.
The sole operator input is the usual rank-one expectation formula. -/
theorem traceChannel_preserves (R : Gaussian.RankOneData (Lp H 2 μ) T)
    (b : HilbertBasis ℕ ℂ V) (W : H →L[ℂ] H) (B : T →L[ℝ] ℂ)
    (hB : ∀ f : Lp H 2 μ, B (R.rankOne f) = ∫ x, inner ℂ (f x) (W (f x)) ∂μ)
    {z : X → V} {ψ : X → H}
    (hz : AEStronglyMeasurable z μ) (hψ : AEStronglyMeasurable ψ μ)
    (hunit : ∀ᵐ x ∂μ, ‖z x‖ = 1)
    (hint : Integrable (fun x => ‖ψ x‖ ^ 2) μ) :
    B (traceChannel R b hz hψ hunit hint) = ∫ x, inner ℂ (ψ x) (W (ψ x)) ∂μ := by
  apply rankOneSeries_observable R B (channelVector_mass b hz hψ hunit hint)
  have he : ∀ a, B (R.rankOne (channelVector b hz hψ hunit hint a)) =
      ∫ x, inner ℂ (channelValue b z ψ a x) (W (channelValue b z ψ a x)) ∂μ := by
    intro a
    rw [hB]
    apply integral_congr_ae
    filter_upwards [(channelValue_memLp b hz hψ hunit hint a).coeFn_toLp] with x hx
    change inner ℂ ((channelValue_memLp b hz hψ hunit hint a).toLp _ x)
      (W ((channelValue_memLp b hz hψ hunit hint a).toLp _ x)) = _
    rw [hx]
  simpa only [he] using integrated_channel_bounded_observable b W hz hψ hunit hint

/-- The mixed channel preserves every bounded hard-fibre observable, with
both the spectral and Kraus sums justified in trace norm. -/
theorem mixedTraceChannel_preserves (R : Gaussian.RankOneData (Lp H 2 μ) T)
    (b : HilbertBasis ℕ ℂ V) (W : H →L[ℂ] H) (B : T →L[ℝ] ℂ)
    (hB : ∀ f : Lp H 2 μ, B (R.rankOne f) = ∫ x, inner ℂ (f x) (W (f x)) ∂μ)
    {z : X → V} {ψ : ℕ → X → H}
    (hz : AEStronglyMeasurable z μ) (hψ : ∀ n, AEStronglyMeasurable (ψ n) μ)
    (hunit : ∀ᵐ x ∂μ, ‖z x‖ = 1)
    (hint : ∀ n, Integrable (fun x => ‖ψ n x‖ ^ 2) μ)
    {mass : ℝ} (hmass : HasSum (fun n => ∫ x, ‖ψ n x‖ ^ 2 ∂μ) mass) :
    B (mixedTraceChannel R b hz hψ hunit hint) =
      ∑' n, ∫ x, inner ℂ (ψ n x) (W (ψ n x)) ∂μ := by
  have hs : Summable (fun n => traceChannel R b hz (hψ n) hunit (hint n)) :=
    hmass.summable.of_norm_bounded (fun n => traceChannel_norm_le R b hz (hψ n) hunit (hint n))
  rw [mixedTraceChannel_eq_tsum R b hz hψ hunit hint hmass, B.map_tsum hs]
  exact tsum_congr (fun n => traceChannel_preserves R b W B hB hz (hψ n) hunit (hint n))

/-- Every nonnegative multiplication form, including an unbounded Coulomb
term, is preserved by the actual trace-class channel. Infinity is allowed. -/
theorem traceChannel_potential (R : Gaussian.RankOneData (Lp H 2 μ) T)
    {Tr : RemovalState.PositiveTraceData T} (E : RemovalState.PositiveForm Tr)
    (hpositive : R.positive ⊆ Tr.positive) (b : HilbertBasis ℕ ℂ V)
    (W : X → ℝ≥0∞) (hW : AEMeasurable W μ)
    (hform : ∀ f : Lp H 2 μ, E.expectation (R.rankOne f) =
      ∫⁻ x, W x * ENNReal.ofReal (‖f x‖ ^ 2) ∂μ)
    {z : X → V} {ψ : X → H}
    (hz : AEStronglyMeasurable z μ) (hψ : AEStronglyMeasurable ψ μ)
    (hunit : ∀ᵐ x ∂μ, ‖z x‖ = 1)
    (hint : Integrable (fun x => ‖ψ x‖ ^ 2) μ) :
    E.expectation (traceChannel R b hz hψ hunit hint) =
      ∫⁻ x, W x * ENNReal.ofReal (‖ψ x‖ ^ 2) ∂μ := by
  rw [traceChannel, rankOneSeries_expectation R E hpositive
    (channelVector_mass b hz hψ hunit hint)]
  have he (a : ℕ) : E.expectation (R.rankOne (channelVector b hz hψ hunit hint a)) =
      ∫⁻ x, W x * ENNReal.ofReal (‖channelValue b z ψ a x‖ ^ 2) ∂μ := by
    rw [hform]
    apply lintegral_congr_ae
    filter_upwards [(channelValue_memLp b hz hψ hunit hint a).coeFn_toLp] with x hx
    change W x * ENNReal.ofReal
      (‖(channelValue_memLp b hz hψ hunit hint a).toLp _ x‖ ^ 2) = _
    rw [hx]
  simpa only [he] using integrated_channel_potential b W hz hψ hW hunit

section ChannelForms

variable (R : Gaussian.RankOneData (Lp H 2 μ) T)
  {Tr : RemovalState.PositiveTraceData T} (E : RemovalState.PositiveForm Tr)
  (hpositive : R.positive ⊆ Tr.positive)
  (b : HilbertBasis ℕ ℂ V) {z dz : X → V} {u ψ : X → H} {s : X → ℝ}
  (hz : AEStronglyMeasurable z μ) (hdz : AEStronglyMeasurable dz μ)
  (hu : AEStronglyMeasurable u μ) (hψ : AEStronglyMeasurable ψ μ)
  (hunit : ∀ᵐ x ∂μ, ‖z x‖ = 1)
  (hconn : ∀ᵐ x ∂μ, inner ℂ (z x) (dz x) = Complex.I * s x)
  (hmass : Integrable (fun x => ‖ψ x‖ ^ 2) μ)
  (hkinetic : Integrable (fun x => ‖u x‖ ^ 2 +
    2 * s x * (inner ℂ (u x) (ψ x)).re + ‖dz x‖ ^ 2 * ‖ψ x‖ ^ 2) μ)

include hpositive in
/-- The full channel's kinetic energy follows from the weak product rule
and rank-one form evaluation, through the actual L2 derivative vectors. -/
theorem traceChannel_energy
    (hform : ∀ a, E.expectation (R.rankOne (channelVector b hz hψ hunit hmass a)) =
      ENNReal.ofReal (‖channelDerivativeVector b hz hdz hu hψ hunit hconn hkinetic a‖ ^ 2)) :
    E.expectation (traceChannel R b hz hψ hunit hmass) =
      ENNReal.ofReal (∫ x, ‖u x‖ ^ 2 + 2 * s x * (inner ℂ (u x) (ψ x)).re +
        ‖dz x‖ ^ 2 * ‖ψ x‖ ^ 2 ∂μ) :=
  rankOneSeries_energy R E hpositive (channelVector_mass b hz hψ hunit hmass)
    (channelDerivativeVector_energy b hz hdz hu hψ hunit hconn hkinetic) hform

include hpositive in
/-- The current trace of the constructed channel has the required shift.
Only rank-one spectral limits and their standard uniform form bound enter
from operator theory. The output current identity is proved. -/
theorem traceChannel_current (J : RemovalState.FormObservable E)
    (hform : ∀ a, E.expectation (R.rankOne (channelVector b hz hψ hunit hmass a)) =
      ENNReal.ofReal (‖channelDerivativeVector b hz hdz hu hψ hunit hconn hkinetic a‖ ^ 2))
    (hcurrent : ∀ a, Tendsto
      (fun n => J.approximation n (R.rankOne (channelVector b hz hψ hunit hmass a)))
      atTop (𝓝 ((inner ℂ (channelVector b hz hψ hunit hmass a)
        (channelDerivativeVector b hz hdz hu hψ hunit hconn hkinetic a)).re)))
    (hbound : ∀ n a,
      ‖J.approximation n (R.rankOne (channelVector b hz hψ hunit hmass a))‖ ≤
        (‖channelVector b hz hψ hunit hmass a‖ ^ 2 +
          ‖channelDerivativeVector b hz hdz hu hψ hunit hconn hkinetic a‖ ^ 2) / 2) :
    J.value (traceChannel R b hz hψ hunit hmass) =
      (∫ x, inner ℂ (ψ x) (u x) + (s x : ℂ) * ‖ψ x‖ ^ 2 ∂μ).re := by
  have he := rankOneSeries_current R J hpositive
    (channelVector_mass b hz hψ hunit hmass)
    (channelDerivativeVector_energy b hz hdz hu hψ hunit hconn hkinetic)
    hform hcurrent hbound
  exact he.trans (Complex.hasSum_re
    (channelVector_current b hz hdz hu hψ hunit hconn hmass hkinetic)).tsum_eq

end ChannelForms

end GptLean.Repair
