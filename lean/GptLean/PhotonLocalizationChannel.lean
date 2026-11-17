import GptLean.Repair.TraceChannel
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
Normal channels from a countable Hilbert-space dilation.

The output of a pure state is the trace-norm convergent sum of its actual
Kraus vectors. Parseval proves convergence, positivity, and preservation
of trace. The only trace-class background is the universal bounded linear
extension of this formula and the spectral decomposition of a positive
trace-class operator. Neither background field mentions photon cutoffs.
-/

namespace GptLean.PhotonLocalizationChannel

open Filter Topology
open scoped InnerProductSpace

variable {H T : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]

/-- Coordinates of a dilation in an orthonormal basis of its environment. -/
abbrev KrausIsometry (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  H →ₗᵢ[ℂ] lp (fun _ : ℕ => H) 2

/-- The vector mass of an arbitrary isometric dilation is Parseval's identity. -/
theorem kraus_mass (U : KrausIsometry H) (v : H) :
    HasSum (fun a => ‖U v a‖ ^ 2) (‖v‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, U.norm_map] using
    lp.hasSum_norm (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) (U v)

/-- The actual partial trace of a dilated pure state. -/
noncomputable def pure (R : Gaussian.RankOneData H T) (U : KrausIsometry H) (v : H) : T :=
  Repair.rankOneSeries R (fun a => U v a)

theorem pure_hasSum (R : Gaussian.RankOneData H T) (U : KrausIsometry H) (v : H) :
    HasSum (fun a => R.rankOne (U v a)) (pure R U v) :=
  Repair.rankOneSeries_hasSum R (kraus_mass U v)

theorem pure_positive (R : Gaussian.RankOneData H T) (U : KrausIsometry H) (v : H) :
    pure R U v ∈ R.positive :=
  Repair.rankOneSeries_positive R (kraus_mass U v)

theorem pure_trace (R : Gaussian.RankOneData H T) (U : KrausIsometry H) (v : H) :
    R.trace (pure R U v) = ‖v‖ ^ 2 :=
  Repair.rankOneSeries_trace R (kraus_mass U v)

theorem pure_norm_le (R : Gaussian.RankOneData H T) (U : KrausIsometry H) (v : H) :
    ‖pure R U v‖ ≤ ‖v‖ ^ 2 :=
  Repair.rankOneSeries_norm_le R (kraus_mass U v)

/-- Universal normal trace calculus. `extend` is the standard linear
extension of the explicit partial-trace series for every dilation. The
positive spectral theorem supplies a sequence of square-root eigenvectors.
Positivity and preservation of trace of the extension are proved below. -/
structure NormalTraceData (R : Gaussian.RankOneData H T) where
  extend : KrausIsometry H → T →L[ℝ] T
  extend_rankOne : ∀ U v, extend U (R.rankOne v) = pure R U v
  positive_decomposition : ∀ x ∈ R.positive,
    ∃ v : ℕ → H, HasSum (fun n => R.rankOne (v n)) x

namespace NormalTraceData

variable {R : Gaussian.RankOneData H T} (N : NormalTraceData R)

/-- Normality identifies the output on every positive spectral series. -/
theorem extend_hasSum (U : KrausIsometry H) {v : ℕ → H} {x : T}
    (hv : HasSum (fun n => R.rankOne (v n)) x) :
    HasSum (fun n => pure R U (v n)) (N.extend U x) := by
  simpa only [N.extend_rankOne] using (N.extend U).hasSum hv

/-- The full channel is positive by closedness of the trace-class cone. -/
theorem positive (U : KrausIsometry H) {x : T} (hx : x ∈ R.positive) :
    N.extend U x ∈ R.positive := by
  obtain ⟨v, hv⟩ := N.positive_decomposition x hx
  apply R.closed_positive.mem_of_tendsto (N.extend_hasSum U hv)
  apply Eventually.of_forall
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using R.zero_positive
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using R.add_positive (pure_positive R U (v a)) ih

/-- Conservation of trace is derived on all positive normal operators. -/
theorem trace (U : KrausIsometry H) {x : T} (hx : x ∈ R.positive) :
    R.trace (N.extend U x) = R.trace x := by
  obtain ⟨v, hv⟩ := N.positive_decomposition x hx
  have h₁ := R.trace.hasSum (N.extend_hasSum U hv)
  have h₂ := R.trace.hasSum hv
  simp only [pure_trace] at h₁
  simp only [R.trace_rankOne] at h₂
  exact h₁.unique h₂

/-- Positive normal states form a closed subset of trace class. -/
def states (_N : NormalTraceData R) : Set T := {x | x ∈ R.positive ∧ R.trace x = 1}

theorem states_closed : IsClosed (N.states) :=
  R.closed_positive.inter (isClosed_eq R.trace.continuous continuous_const)

theorem preserves_states (U : KrausIsometry H) {x : T} (hx : x ∈ N.states) :
    N.extend U x ∈ N.states :=
  ⟨N.positive U hx.1, (N.trace U hx.1).trans hx.2⟩

/-- Equality of bounded observables on the actual pure outputs determines
the observable on every positive trace-class input. -/
theorem observable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (U : KrausIsometry H) (B C : T →L[ℝ] F)
    (hpure : ∀ v, B (pure R U v) = C (R.rankOne v))
    {x : T} (hx : x ∈ R.positive) : B (N.extend U x) = C x := by
  obtain ⟨v, hv⟩ := N.positive_decomposition x hx
  have h₁ := B.hasSum (N.extend_hasSum U hv)
  simp only [hpure] at h₁
  exact h₁.unique (C.hasSum hv)

/-- Environment-coordinate Parseval proves electronic observable
preservation from the vector intertwining with the electronic operator. -/
theorem electronic (U : KrausIsometry H) (W : H →L[ℂ] H)
    (B : T →L[ℝ] ℂ)
    (hB : ∀ v, B (R.rankOne v) = inner ℂ v (W v))
    (hW : ∀ v a, U (W v) a = W (U v a))
    {x : T} (hx : x ∈ R.positive) : B (N.extend U x) = B x := by
  apply N.observable U B B _ hx
  intro v
  rw [hB]
  apply Repair.rankOneSeries_observable R B (kraus_mass U v)
  have h := lp.hasSum_inner (𝕜 := ℂ) (U v) (U (W v))
  simpa only [hB, hW, U.inner_map_map] using h

/-- The squared-coordinate construction also transports any positive
unbounded form through monotone spectral truncations. -/
theorem pure_expectation {Tr : RemovalState.PositiveTraceData T}
    (E : RemovalState.PositiveForm Tr) (hpositive : R.positive ⊆ Tr.positive)
    (U : KrausIsometry H) (v : H) :
    E.expectation (pure R U v) = ∑' a, E.expectation (R.rankOne (U v a)) :=
  Repair.rankOneSeries_expectation R E hpositive (kraus_mass U v)

/-- A fixed source spectral decomposition gives the actual Kraus vectors
of the mixed output. The double series is absolutely convergent in trace
norm, so no fresh spectral decomposition of the output is chosen. -/
theorem mixed_hasSum (U : KrausIsometry H) {v : ℕ → H} {x : T}
    (hv : HasSum (fun n => R.rankOne (v n)) x) :
    HasSum (fun n => R.rankOne
      (Repair.flattenVectors (fun i a => U (v i) a) n)) (N.extend U x) := by
  have hm : HasSum (fun n => ‖v n‖ ^ 2) (R.trace x) := by
    simpa only [R.trace_rankOne] using R.trace.hasSum hv
  have hmass : Summable (fun p : ℕ × ℕ => ‖U (v p.1) p.2‖ ^ 2) := by
    apply (summable_prod_of_nonneg (fun p => sq_nonneg ‖U (v p.1) p.2‖)).mpr
    refine ⟨fun n => (kraus_mass U (v n)).summable, ?_⟩
    simpa only [(kraus_mass U _).tsum_eq] using hm.summable
  have hs : Summable (fun p : ℕ × ℕ => R.rankOne (U (v p.1) p.2)) := by
    apply Summable.of_norm
    simpa only [R.norm_rankOne] using hmass
  have hp : HasSum (fun p : ℕ × ℕ => R.rankOne (U (v p.1) p.2)) (N.extend U x) := by
    convert hs.hasSum using 1
    rw [hs.tsum_prod' (fun n => (pure_hasSum R U (v n)).summable)]
    exact (N.extend_hasSum U hv).tsum_eq.symm
  exact (Nat.pairEquiv.symm.hasSum_iff
    (f := fun p : ℕ × ℕ => R.rankOne (U (v p.1) p.2))
    (a := N.extend U x)).mpr hp

end NormalTraceData

end GptLean.PhotonLocalizationChannel
