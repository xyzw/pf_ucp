import GptLean.PhotonLossClosure
import GptLean.PhotonLocalizationChannel

/-!
Retaining a closed physical state sector throughout photon loss.

For fermionic states the sector is the fixed set of the canonical
electronic compression. The actual normal channel commutes with that
compression whenever its Kraus vectors commute with the electronic
projection. Closure and all localization estimates then restrict to the
physical sector without changing the energy, number or tested pairings.
-/

namespace GptLean.PhotonLocalizationChannel

open Filter Topology

variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  {A : Gaussian.RankOneData H X}

/-- Canonical electronic compression commutes with the constructed
normal channel, proved on its explicit Kraus and source series. -/
theorem NormalTraceData.compression_commutes
    (normal : NormalTraceData A) (U : KrausIsometry H)
    (P : H →L[ℂ] H) (compression : X →L[ℝ] X)
    (hcompression : ∀ v, compression (A.rankOne v) = A.rankOne (P v))
    (hcommute : ∀ v k, P (U v k) = U (P v) k)
    {x : X} (hx : x ∈ A.positive) :
    compression (normal.extend U x) = normal.extend U (compression x) := by
  have hpure (v : H) : compression (pure A U v) = pure A U (P v) := by
    have hsum := compression.hasSum (pure_hasSum A U v)
    simp only [hcompression, hcommute] at hsum
    exact hsum.unique (pure_hasSum A U (P v))
  obtain ⟨v, hv⟩ := normal.positive_decomposition x hx
  have hl := compression.hasSum (normal.extend_hasSum U hv)
  have hr := (normal.extend U).hasSum (compression.hasSum hv)
  simp only [hpure] at hl
  simp only [hcompression, normal.extend_rankOne] at hr
  exact hl.unique hr

end GptLean.PhotonLocalizationChannel

namespace GptLean.PhotonLoss

open Filter Topology

variable {X Test : Type*} [NormedAddCommGroup X]

/-- Restrict the admissible normal states to a closed invariant sector.
The retained limits stay in this sector because the restricted state
space itself is closed. -/
def LocalizationData.restrict (D : LocalizationData X) (S : Set X)
    (hclosed : IsClosed S)
    (hstable : ∀ m x, x ∈ D.states → x ∈ S → D.localize m x ∈ S) :
    LocalizationData X where
  states := D.states ∩ S
  states_closed := D.states_closed.inter hclosed
  localize := D.localize
  localize_cont := D.localize_cont
  localize_state m x hx := ⟨D.localize_state m x hx.1, hstable m x hx.1 hx.2⟩
  localize_comp m l hml x hx := D.localize_comp m l hml x hx.1
  tail := D.tail
  tail_cont := D.tail_cont
  weight := D.weight
  number_law m x hx := D.number_law m x hx.1

/-- Universal trace facts descend to a smaller physical state sector. -/
def TraceData.restrict {D : LocalizationData X} (T : TraceData D Test)
    (S : Set X) (hclosed : IsClosed S)
    (hstable : ∀ m x, x ∈ D.states → x ∈ S → D.localize m x ∈ S) :
    TraceData (D.restrict S hclosed hstable) Test where
  energy := T.energy
  number := T.number
  energy_lsc := T.energy_lsc
  number_lsc := T.number_lsc
  number_decrease m x hx := T.number_decrease m x hx.1
  tail_markov M x hx hfinite := T.tail_markov M x hx.1 hfinite
  cutoff := T.cutoff
  cutoff_cont := T.cutoff_cont
  cutoff_tendsto x hx := T.cutoff_tendsto x hx.1
  truncatedEnergy := T.truncatedEnergy
  truncated_lsc := T.truncated_lsc
  energy_eq_iSup := T.energy_eq_iSup
  test := T.test
  test_passage u x E hu hE hlim := T.test_passage u x E (fun n => (hu n).1) hE hlim

/-- The proved sharp localization estimates and compactness descend
without an extra analytic hypothesis. -/
def LocalizationEstimates.restrict {D : LocalizationData X} {T : TraceData D Test}
    (J : LocalizationEstimates D T) (S : Set X) (hclosed : IsClosed S)
    (hstable : ∀ m x, x ∈ D.states → x ∈ S → D.localize m x ∈ S) :
    LocalizationEstimates (D.restrict S hclosed hstable) (T.restrict S hclosed hstable) where
  electronicTight := J.electronicTight
  precompact u E hu hE htight := J.precompact u E (fun n => (hu n).1) hE htight
  rough := J.rough
  rough_bound E m x hx hE := J.rough_bound E m x hx.1 hE
  imsError := J.imsError
  imsError_zero := J.imsError_zero
  localError := J.localError
  localError_zero := J.localError_zero
  combined_bound E e l k m x hx he hE henergy :=
    J.combined_bound E e l k m x hx.1 he hE henergy
  testError := J.testError
  testError_zero := J.testError_zero
  test_bound E t m x hx hE := J.test_bound E t m x hx.1 hE

section Fixed

variable [NormedSpace ℝ X]

/-- The fixed sector of a continuous compression is closed and invariant
under any localization commuting with the compression on states. -/
theorem LocalizationData.fixed_sector
    (D : LocalizationData X) (compression : X →L[ℝ] X)
    (hcommute : ∀ m x, x ∈ D.states →
      compression (D.localize m x) = D.localize m (compression x)) :
    IsClosed {x | compression x = x} ∧
      ∀ m x, x ∈ D.states → compression x = x →
        compression (D.localize m x) = D.localize m x := by
  refine ⟨isClosed_eq compression.continuous continuous_id, ?_⟩
  intro m x hx hfixed
  rw [hcommute m x hx, hfixed]

end Fixed

end GptLean.PhotonLoss
