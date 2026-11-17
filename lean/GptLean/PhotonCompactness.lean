import GptLean.PhotonNumber
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
The retained-state construction in Step 2 of `thm-continuum-compactness`.

Adapted from the topological and retained-state parts of
`claude_lean/QEDFT/PhotonLoss/Compactness.lean` and `Assembly.lean`.
Unlike that assembly, the weight monotonicity and discarded-photon estimate
are derived here from a normalized joint number law using `PhotonNumber`.

The construction needs local total boundedness and asymptotic sector tails,
with the manuscript's order of quantifiers. It imposes no mean-number bound.
The optional final theorem passes an existing number bound through both
limits by lower semicontinuity.

The closed set `states` stands for normal positive trace-one operators in
the complete trace-norm space. Its concrete identification, the Fock
localization maps and their joint laws, the gentle estimate, and the local
Rellich approximation remain inputs. Sharp energy comparison and current
passage are not asserted here. In particular this file does not instantiate
`Attainment.PhotonLossInput` or `Closure.BoundedConstraintClosure`.
-/

namespace GptLean.PhotonLoss

open Filter Topology
open scoped ENNReal

/-- Uniform approximation by totally bounded sets gives total boundedness. -/
theorem totallyBounded_range_of_approx {X ι : Type*} [PseudoMetricSpace X]
    (x : ι → X)
    (h : ∀ ε > 0, ∃ K : Set X, TotallyBounded K ∧
      ∀ n, ∃ y ∈ K, dist (x n) y ≤ ε) :
    TotallyBounded (Set.range x) := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨K, hK, hxK⟩ := h (ε / 2) (half_pos hε)
  obtain ⟨t, ht, hKt⟩ := Metric.totallyBounded_iff.1 hK (ε / 2) (half_pos hε)
  refine ⟨t, ht, ?_⟩
  rintro _ ⟨n, rfl⟩
  obtain ⟨y, hyK, hy⟩ := hxK n
  obtain ⟨c, hct, hyc⟩ := Set.mem_iUnion₂.1 (hKt hyK)
  refine Set.mem_iUnion₂.2 ⟨c, hct, ?_⟩
  rw [Metric.mem_ball] at hyc ⊢
  calc dist (x n) c ≤ dist (x n) y + dist y c := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt hy hyc
    _ = ε := add_halves ε

/-- Countably many locally precompact sequences admit a common subsequence. -/
theorem exists_diagonal_subseq {X : Type*} [MetricSpace X] [CompleteSpace X]
    (x : ℕ → ℕ → X) (h : ∀ m, TotallyBounded (Set.range (x m))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ G : ℕ → X, ∀ m, Tendsto (fun n => x m (φ n)) atTop (𝓝 (G m)) := by
  have hc : IsCompact (Set.pi Set.univ fun m => closure (Set.range (x m))) :=
    isCompact_univ_pi fun m => (h m).closure.isCompact_of_isClosed isClosed_closure
  have hmem : ∀ n, (fun m => x m n) ∈ Set.pi Set.univ fun m => closure (Set.range (x m)) :=
    fun n m _ => subset_closure (Set.mem_range_self n)
  obtain ⟨G, -, φ, hφ, hG⟩ := hc.tendsto_subseq hmem
  exact ⟨φ, hφ, G, fun m => (tendsto_pi_nhds.1 hG) m⟩

/-- Joint retained/discarded number statistics of a localization dilation.
The identities identify the two marginal observables. The gentle estimate
is a separate operator input rather than a consequence of number statistics. -/
structure LocalizationNumberLaw {X : Type*} [NormedAddCommGroup X]
    (tail : ℕ → X → ℝ) (weight : X → ℝ) (original retained : X) where
  p : ℕ × ℕ → ℝ
  nonneg : ∀ x, 0 ≤ p x
  summable : Summable p
  normalized : ∑' x, p x = 1
  tail_eq : ∀ M, tail M retained = tailIn p M
  weight_in : weight retained = bIn p
  weight_total : weight original = bTot p
  gentle : ‖original - retained‖ ≤ lossModulus (discardProb p)

/-- Model inputs for construction of the retained normal limit. The index
`m` represents radius `3^(m+1)` so all radii of the manuscript are included. -/
structure LocalizationData (X : Type*) [NormedAddCommGroup X] where
  states : Set X
  states_closed : IsClosed states
  localize : ℕ → X → X
  localize_cont : ∀ m, Continuous (localize m)
  localize_state : ∀ m, ∀ τ ∈ states, localize m τ ∈ states
  localize_comp : ∀ m l, m < l → ∀ τ ∈ states,
    localize m (localize l τ) = localize m τ
  tail : ℕ → X → ℝ
  tail_cont : ∀ M, Continuous (tail M)
  weight : X → ℝ
  number_law : ∀ m, ∀ τ ∈ states,
    Nonempty (LocalizationNumberLaw tail weight τ (localize m τ))

namespace LocalizationData

variable {X : Type*} [NormedAddCommGroup X] (D : LocalizationData X)
  {ω G : ℕ → X} {Γ : X}

/-- The bounded decreasing number weight is nonnegative on every state. -/
theorem weight_nonneg {τ : X} (hτ : τ ∈ D.states) : 0 ≤ D.weight τ := by
  obtain ⟨law⟩ := D.number_law 0 τ hτ
  rw [law.weight_total]
  exact bTot_nonneg law.nonneg

/-- Localization increases the expectation of `2^(-number)`. -/
theorem weight_mono (m : ℕ) {τ : X} (hτ : τ ∈ D.states) :
    D.weight τ ≤ D.weight (D.localize m τ) := by
  obtain ⟨law⟩ := D.number_law m τ hτ
  rw [law.weight_total, law.weight_in]
  exact sub_nonneg.mp (bIn_sub_bTot_nonneg law.nonneg law.summable)

/-- The discarded-photon estimate is derived from the joint law. -/
theorem loss (m : ℕ) {τ : X} (hτ : τ ∈ D.states) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ ‖τ - D.localize m τ‖ ≤ lossModulus t ∧
      ∀ M : ℕ, t ≤ D.tail M (D.localize m τ) +
        2 ^ (M + 1) * (D.weight (D.localize m τ) - D.weight τ) := by
  obtain ⟨law⟩ := D.number_law m τ hτ
  refine ⟨discardProb law.p, discardProb_nonneg law.nonneg,
    discardProb_le_one law.nonneg law.summable law.normalized, law.gentle, ?_⟩
  intro M
  rw [law.tail_eq, law.weight_in, law.weight_total]
  exact discardProb_le law.nonneg law.summable M

section Retained

variable (hω : ∀ n, ω n ∈ D.states)
  (hG : ∀ m, Tendsto (fun n => D.localize m (ω n)) atTop (𝓝 (G m)))
include hω hG

theorem retained_mem (m : ℕ) : G m ∈ D.states :=
  D.states_closed.mem_of_tendsto (hG m)
    (Eventually.of_forall fun n => D.localize_state m _ (hω n))

/-- Localization consistency survives the first trace-norm limit. -/
theorem retained_consistent {m l : ℕ} (hml : m < l) : D.localize m (G l) = G m := by
  have h1 : Tendsto (fun n => D.localize m (D.localize l (ω n))) atTop
      (𝓝 (D.localize m (G l))) := ((D.localize_cont m).tendsto _).comp (hG l)
  have h2 : (fun n => D.localize m (D.localize l (ω n))) =
      fun n => D.localize m (ω n) :=
    funext fun n => D.localize_comp m l hml _ (hω n)
  rw [h2] at h1
  exact tendsto_nhds_unique h1 (hG m)

theorem retained_weight_antitone : Antitone fun m => D.weight (G m) := by
  refine antitone_nat_of_succ_le fun m => ?_
  have h := D.weight_mono m (D.retained_mem hω hG (m + 1))
  rwa [D.retained_consistent hω hG (Nat.lt_succ_self m)] at h

omit hω in
/-- Asymptotic sector tightness passes to all retained limits. The eventual
index may depend on `m`. No uniform bound in the original sequence is used. -/
theorem retained_tail_le
    (htight : ∀ ε > 0, ∃ M, ∀ m, ∀ᶠ n in atTop,
      D.tail M (D.localize m (ω n)) ≤ ε) :
    ∀ ε > 0, ∃ M, ∀ m, D.tail M (G m) ≤ ε := fun ε hε => by
  obtain ⟨M, hM⟩ := htight ε hε
  exact ⟨M, fun m => le_of_tendsto (((D.tail_cont M).tendsto _).comp (hG m)) (hM m)⟩

/-- First choose the sector cutoff, then the localization radius. -/
theorem retained_norm_sub_le_eps
    (htail : ∀ ε > 0, ∃ M, ∀ m, D.tail M (G m) ≤ ε) {ε : ℝ}
    (hε : 0 < ε) : ∃ m₀, ∀ m ≥ m₀, ∀ l, m < l → ‖G l - G m‖ ≤ ε := by
  set δ : ℝ := min (ε ^ 2 / 32) (ε / 4)
  have hδpos : 0 < δ := lt_min (by positivity) (by positivity)
  obtain ⟨M, hM⟩ := htail δ hδpos
  have hpow : (0 : ℝ) < 2 ^ (M + 1) := by positivity
  have hb : CauchySeq fun m => D.weight (G m) :=
    (tendsto_atTop_ciInf (D.retained_weight_antitone hω hG)
      ⟨0, by rintro _ ⟨m, rfl⟩
             exact D.weight_nonneg (D.retained_mem hω hG m)⟩).cauchySeq
  obtain ⟨m₀, hm₀⟩ := Metric.cauchySeq_iff.1 hb (δ / 2 ^ (M + 1)) (by positivity)
  refine ⟨m₀, fun m hm l hml => ?_⟩
  obtain ⟨t, -, -, hnorm, ht⟩ := D.loss m (D.retained_mem hω hG l)
  rw [D.retained_consistent hω hG hml] at hnorm ht
  have hbl : D.weight (G m) - D.weight (G l) ≤ δ / 2 ^ (M + 1) :=
    (le_abs_self _).trans (by simpa [Real.dist_eq] using
      (hm₀ m hm l (hm.trans hml.le)).le)
  have hmul : 2 ^ (M + 1) * (D.weight (G m) - D.weight (G l)) ≤ δ := by
    have h := mul_le_mul_of_nonneg_left hbl hpow.le
    have e : (2 : ℝ) ^ (M + 1) * (δ / 2 ^ (M + 1)) = δ := by field_simp
    rwa [e] at h
  apply hnorm.trans
  exact lossModulus_le hε (by linarith [ht M, hM m])

theorem retained_cauchySeq
    (htail : ∀ ε > 0, ∃ M, ∀ m, D.tail M (G m) ≤ ε) : CauchySeq G := by
  rw [Metric.cauchySeq_iff']
  intro ε hε
  obtain ⟨m₀, hm₀⟩ := D.retained_norm_sub_le_eps hω hG htail (half_pos hε)
  refine ⟨m₀, fun l hl => ?_⟩
  rcases (show m₀ ≤ l from hl).lt_or_eq with h | h
  · rw [dist_eq_norm]
    exact (hm₀ m₀ le_rfl l h).trans_lt (half_lt_self hε)
  · rw [← h, dist_self]
    exact hε

end Retained

/-- Construction of a normal retained limit. The original states need not
have a convergent subsequence and need not have bounded mean photon number. -/
theorem exists_retained_limit [CompleteSpace X] (ω : ℕ → X)
    (hω : ∀ n, ω n ∈ D.states)
    (hloc : ∀ m, TotallyBounded (Set.range fun n => D.localize m (ω n)))
    (htight : ∀ ε > 0, ∃ M, ∀ m, ∀ᶠ n in atTop,
      D.tail M (D.localize m (ω n)) ≤ ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : ℕ → X,
      (∀ m, Tendsto (fun n => D.localize m (ω (φ n))) atTop (𝓝 (G m))) ∧
      (∀ m, G m ∈ D.states) ∧
      (∀ m l, m < l → D.localize m (G l) = G m) ∧
      ∃ Γ ∈ D.states, Tendsto G atTop (𝓝 Γ) := by
  obtain ⟨φ, hφ, G, hG⟩ := exists_diagonal_subseq (fun m n => D.localize m (ω n)) hloc
  have hω' : ∀ n, ω (φ n) ∈ D.states := fun n => hω (φ n)
  have htail := D.retained_tail_le hG fun ε hε =>
    (htight ε hε).imp fun M hM m => hφ.tendsto_atTop.eventually (hM m)
  obtain ⟨Γ, hΓ⟩ := cauchySeq_tendsto_of_complete (D.retained_cauchySeq hω' hG htail)
  exact ⟨φ, hφ, G, hG, D.retained_mem hω' hG,
    fun m l hml => D.retained_consistent hω' hG hml, Γ,
    D.states_closed.mem_of_tendsto hΓ (Eventually.of_forall (D.retained_mem hω' hG)), hΓ⟩

/-- Local compact approximation is sufficient for the construction. In the
manuscript it comes from electronic/photon cutoffs and finite-rank compression. -/
theorem exists_retained_limit_of_approx [CompleteSpace X] (ω : ℕ → X)
    (hω : ∀ n, ω n ∈ D.states)
    (happrox : ∀ m ε, 0 < ε → ∃ K : Set X, TotallyBounded K ∧
      ∀ n, ∃ y ∈ K, dist (D.localize m (ω n)) y ≤ ε)
    (htight : ∀ ε > 0, ∃ M, ∀ m, ∀ᶠ n in atTop,
      D.tail M (D.localize m (ω n)) ≤ ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : ℕ → X,
      (∀ m, Tendsto (fun n => D.localize m (ω (φ n))) atTop (𝓝 (G m))) ∧
      (∀ m, G m ∈ D.states) ∧
      (∀ m l, m < l → D.localize m (G l) = G m) ∧
      ∃ Γ ∈ D.states, Tendsto G atTop (𝓝 Γ) :=
  D.exists_retained_limit ω hω
    (fun m => totallyBounded_range_of_approx _ (happrox m)) htight

/-- A lower semicontinuous nonnegative observable preserves a constant bound. -/
theorem observable_le_of_tendsto {f : X → ℝ≥0∞} (hf : LowerSemicontinuous f)
    {u : ℕ → X} {x : X} (hu : Tendsto u atTop (𝓝 x)) {M : ℝ≥0∞}
    (hM : ∀ n, f (u n) ≤ M) : f x ≤ M := by
  refine le_of_forall_lt_imp_le_of_dense fun y hy => ?_
  have hev : ∀ᶠ n in atTop, y < f (u n) := hu.eventually (hf x y hy)
  exact ge_of_tendsto tendsto_const_nhds (hev.mono fun n hn => hn.le.trans (hM n))

/-- Optional number control passes through both retained-state limits.
This statement is separate from existence, which has no mean-number input. -/
theorem retained_number_le (number : X → ℝ≥0∞)
    (hnumber : LowerSemicontinuous number)
    (hdecrease : ∀ m, ∀ τ ∈ D.states, number (D.localize m τ) ≤ number τ)
    (hω : ∀ n, ω n ∈ D.states)
    (hG : ∀ m, Tendsto (fun n => D.localize m (ω n)) atTop (𝓝 (G m)))
    (hΓ : Tendsto G atTop (𝓝 Γ)) {M : ℝ≥0∞}
    (hM : ∀ n, number (ω n) ≤ M) :
    (∀ m, number (G m) ≤ M) ∧ number Γ ≤ M := by
  have hGM : ∀ m, number (G m) ≤ M := fun m =>
    observable_le_of_tendsto hnumber (hG m)
      (fun n => (hdecrease m _ (hω n)).trans (hM n))
  exact ⟨hGM, observable_le_of_tendsto hnumber hΓ hGM⟩

/-- The same construction with an optional inherited number cap. The cap
does not replace the sector-tightness input in this abstract interface. -/
theorem exists_retained_limit_with_number [CompleteSpace X] (ω : ℕ → X)
    (hω : ∀ n, ω n ∈ D.states)
    (hloc : ∀ m, TotallyBounded (Set.range fun n => D.localize m (ω n)))
    (htight : ∀ ε > 0, ∃ M, ∀ m, ∀ᶠ n in atTop,
      D.tail M (D.localize m (ω n)) ≤ ε)
    (number : X → ℝ≥0∞) (hnumber : LowerSemicontinuous number)
    (hdecrease : ∀ m, ∀ τ ∈ D.states, number (D.localize m τ) ≤ number τ)
    {M : ℝ≥0∞} (hM : ∀ n, number (ω n) ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : ℕ → X,
      (∀ m, Tendsto (fun n => D.localize m (ω (φ n))) atTop (𝓝 (G m))) ∧
      (∀ m, G m ∈ D.states ∧ number (G m) ≤ M) ∧
      ∃ Γ ∈ D.states, Tendsto G atTop (𝓝 Γ) ∧ number Γ ≤ M := by
  obtain ⟨φ, hφ, G, hG, hGmem, -, Γ, hΓmem, hΓ⟩ :=
    D.exists_retained_limit ω hω hloc htight
  obtain ⟨hGM, hΓM⟩ := D.retained_number_le number hnumber hdecrease
    (fun n => hω (φ n)) hG hΓ (fun n => hM (φ n))
  exact ⟨φ, hφ, G, hG, fun m => ⟨hGmem m, hGM m⟩, Γ, hΓmem, hΓ, hΓM⟩

end LocalizationData
end GptLean.PhotonLoss
