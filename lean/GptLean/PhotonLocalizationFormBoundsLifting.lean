import GptLean.PhotonLocalizationChannel
import GptLean.PhotonLossClosure

/-!
Closure and second quantization preserve proved one-photon form bounds.
The estimates are lifted first through each finite particle sum, then
through the nonnegative sector sum and the source spectral decomposition.
All sums retain the value infinity, so no mean photon number is assumed.
-/

namespace GptLean.PhotonLocalizationFormBounds

open Filter Topology
open scoped ENNReal

section Core

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A lower semicontinuous form inherits a multiplier bound proved on a
form core. The approximation is in the original form, and the multiplier
only needs its already known ambient Hilbert-space continuity. -/
theorem form_bound_of_core (energy : H → ℝ≥0∞) (core : Set H)
    (hlsc : LowerSemicontinuous energy)
    (happrox : ∀ u, energy u < ⊤ → ∃ v : ℕ → H,
      (∀ n, v n ∈ core) ∧ Tendsto v atTop (𝓝 u) ∧
        Tendsto (fun n => energy (v n)) atTop (𝓝 (energy u)))
    (A : H →L[ℝ] H) {C : ℝ} (hC : 0 < C)
    (hcore : ∀ u ∈ core, energy (A u) ≤ ENNReal.ofReal C * energy u) (u : H) :
    energy (A u) ≤ ENNReal.ofReal C * energy u := by
  by_cases hfin : energy u < ⊤
  · obtain ⟨v, hv, hlim, he⟩ := happrox u hfin
    apply PhotonLoss.observable_le_of_tendsto_bounds hlsc (A.continuous.tendsto u |>.comp hlim)
      (ENNReal.Tendsto.const_mul he (Or.inr ENNReal.ofReal_ne_top))
    exact fun n => hcore (v n) (hv n)
  · have hinf : energy u = ⊤ := top_unique (not_lt.mp hfin)
    simp [hinf, (ENNReal.ofReal_pos.mpr hC).ne']

end Core

section Sectors

variable {V : Type*}

/-- Each coordinate form in a fixed particle sector is evaluated by its
one-body slice decomposition. Such decompositions allow entangled sector
vectors and are not restricted to simple tensors. -/
noncomputable def sectorForm (q : V → ℝ≥0∞) {m : ℕ} (slice : Fin m → ℕ → V) : ℝ≥0∞ :=
  ∑ i : Fin m, ∑' k, q (slice i k)

/-- Additive second quantization as the nonnegative sum of finite sector
forms. The vacuum sector contributes the empty sum. -/
noncomputable def fockForm (q : V → ℝ≥0∞)
    (slice : (m : ℕ) → Fin m → ℕ → V) : ℝ≥0∞ :=
  ∑' m, sectorForm q (slice m)

theorem sectorForm_le {q₁ q₂ : V → ℝ≥0∞} {C : ℝ≥0∞}
    (hq : ∀ u, q₁ u ≤ C * q₂ u) {m : ℕ} (slice : Fin m → ℕ → V) :
    sectorForm q₁ slice ≤ C * sectorForm q₂ slice := by
  unfold sectorForm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum fun k => hq (slice i k)

theorem fockForm_le {q₁ q₂ : V → ℝ≥0∞} {C : ℝ≥0∞}
    (hq : ∀ u, q₁ u ≤ C * q₂ u) (slice : (m : ℕ) → Fin m → ℕ → V) :
    fockForm q₁ slice ≤ C * fockForm q₂ slice := by
  unfold fockForm
  rw [← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum fun m => sectorForm_le hq (slice m)

/-- The trace-level form order follows by summing the original state's
spectral vectors, even when one of the two traces is infinite. -/
theorem spectralForm_le {q₁ q₂ : V → ℝ≥0∞} {C : ℝ≥0∞}
    (hq : ∀ u, q₁ u ≤ C * q₂ u)
    (slice : ℕ → (m : ℕ) → Fin m → ℕ → V) :
    (∑' n, fockForm q₁ (slice n)) ≤ C * ∑' n, fockForm q₂ (slice n) := by
  rw [← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum fun n => fockForm_le hq (slice n)

end Sectors

section Channel

variable {H T : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : Gaussian.RankOneData H T} (N : PhotonLocalizationChannel.NormalTraceData R)
  {Tr : RemovalState.PositiveTraceData T}

/-- A vector form estimate on the actual Kraus coordinates proves the
mixed-state estimate. Positivity, the trace-norm channel series and
monotone spectral truncation supply every exchange of infinite sums. -/
theorem channel_form_le (E F : RemovalState.PositiveForm Tr)
    (hpositive : R.positive ⊆ Tr.positive)
    (U : PhotonLocalizationChannel.KrausIsometry H) {C : ℝ≥0∞}
    (hvector : ∀ v, (∑' a, E.expectation (R.rankOne (U v a))) ≤
      C * F.expectation (R.rankOne v)) {x : T} (hx : x ∈ R.positive) :
    E.expectation (N.extend U x) ≤ C * F.expectation x := by
  obtain ⟨v, hv⟩ := N.positive_decomposition x hx
  have hout := N.extend_hasSum U hv
  rw [← hout.tsum_eq, E.expectation_tsum hout.summable
    (fun n => hpositive (PhotonLocalizationChannel.pure_positive R U (v n)))]
  rw [← hv.tsum_eq, F.expectation_tsum hv.summable
    (fun n => hpositive (R.rankOne_positive (v n))), ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro n
  rw [PhotonLocalizationChannel.NormalTraceData.pure_expectation E hpositive U (v n)]
  exact hvector (v n)

/-- Pure-state second-quantization pullbacks determine the exact mixed
trace identity. It suffices to supply the universal tensor-factorization
identity on vectors, rather than the desired physical trace formula. -/
theorem channel_form_eq (E F : RemovalState.PositiveForm Tr)
    (hpositive : R.positive ⊆ Tr.positive)
    (U : PhotonLocalizationChannel.KrausIsometry H)
    (hvector : ∀ v, (∑' a, E.expectation (R.rankOne (U v a))) =
      F.expectation (R.rankOne v)) {x : T} (hx : x ∈ R.positive) :
    E.expectation (N.extend U x) = F.expectation x := by
  obtain ⟨v, hv⟩ := N.positive_decomposition x hx
  have hout := N.extend_hasSum U hv
  rw [← hout.tsum_eq, E.expectation_tsum hout.summable
    (fun n => hpositive (PhotonLocalizationChannel.pure_positive R U (v n)))]
  rw [← hv.tsum_eq, F.expectation_tsum hv.summable
    (fun n => hpositive (R.rankOne_positive (v n)))]
  apply tsum_congr
  intro n
  rw [PhotonLocalizationChannel.NormalTraceData.pure_expectation E hpositive U (v n), hvector]

end Channel

end GptLean.PhotonLocalizationFormBounds
