import GptLean.PhysicalPhotonMarginalMoments
import GptLean.PhysicalFockNumber

/-!
The actual photon-number form agrees with the sum of its actual number
sector traces. This includes the coupled electronic model through its
constructed photon marginal. Generic nonnegative disintegration and
Markov estimates are proved for the resulting countable distribution.
-/

noncomputable section
namespace GptLean.PhysicalFock.NumberMoments

open MeasureTheory PhotonLocalizationChannel PhysicalNormalTrace RemovalState
open scoped ENNReal

variable (BT : StandardNormalTraceBackground)

theorem photon_number_sectors {x : BT.Trace PhotonFock}
    (hx : x ∈ (BT.realization PhotonFock).rank.positive) :
    (NormalPhoton.numberForm BT.normal (BT.realization PhotonFock).functional).expectation x =
      ∑' n : ℕ, ENNReal.ofReal ((n : ℝ) *
        sectorTrace (Sector photonMeasure) (BT.realization PhotonFock).functional n x) := by
  let E := NormalPhoton.numberForm BT.normal (BT.realization PhotonFock).functional
  let G := numberTraceForm (Sector photonMeasure) BT.normal
    (BT.realization PhotonFock).functional BT.traceData (fun _ hx => hx)
  have h : E.expectation x = G.expectation x := by
    obtain ⟨v, hv⟩ := BT.normal.positive_decomposition x hx
    rw [← hv.tsum_eq, E.expectation_tsum hv.summable
      (fun n => (BT.realization PhotonFock).rank.rankOne_positive (v n)),
      G.expectation_tsum hv.summable
      (fun n => (BT.realization PhotonFock).rank.rankOne_positive (v n))]
    apply tsum_congr
    intro n
    exact (NormalPhoton.numberForm_rankOne BT.normal
      (BT.realization PhotonFock).functional (v n)).trans
      (numberTraceForm_rankOne (Sector photonMeasure) BT.normal
        (BT.realization PhotonFock).functional BT.traceData (fun _ hx => hx) (v n)).symm
  exact h.trans (numberTraceForm_expectation (Sector photonMeasure) BT.normal
    (BT.realization PhotonFock).functional BT.traceData (fun _ hx => hx) hx)

variable {X : Type} [MeasurableSpace X] (μ : Measure X) [IsSeparable μ]

def sector (n : ℕ) : BT.Trace (Lp PhotonFock 2 μ) →L[ℝ] ℝ :=
  (sectorTrace (Sector photonMeasure) (BT.realization PhotonFock).functional n).comp
    (PhysicalPhotonMarginal.marginal BT μ)

theorem sector_nonneg (n : ℕ) {x : BT.Trace (Lp PhotonFock 2 μ)}
    (hx : x ∈ (BT.realization (Lp PhotonFock 2 μ)).rank.positive) : 0 ≤ sector BT μ n x :=
  sectorTrace_nonneg (Sector photonMeasure) BT.normal (BT.realization PhotonFock).functional n
    (PhysicalPhotonMarginal.marginal_positive BT μ hx)

theorem sector_hasSum {x : BT.Trace (Lp PhotonFock 2 μ)}
    (hx : x ∈ (BT.realization (Lp PhotonFock 2 μ)).rank.positive) :
    Summable (fun n => sector BT μ n x) :=
  (sectorTrace_hasSum (Sector photonMeasure) BT.normal (BT.realization PhotonFock).functional
    (PhysicalPhotonMarginal.marginal_positive BT μ hx)).summable

theorem full_number_sectors {x : BT.Trace (Lp PhotonFock 2 μ)}
    (hx : x ∈ (BT.realization (Lp PhotonFock 2 μ)).rank.positive) :
    (PhysicalPhotonMarginal.fullForm BT μ
      (NormalPhoton.numberForm BT.normal (BT.realization PhotonFock).functional)).expectation x =
      ∑' n : ℕ, ENNReal.ofReal ((n : ℝ) * sector BT μ n x) :=
  photon_number_sectors BT (PhysicalPhotonMarginal.marginal_positive BT μ hx)

/-- Nonnegative number moments disintegrate without a finite-moment premise. -/
theorem moment_disintegration {α : Type*} (p : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (q : ℕ → ℝ) (f : α → ℕ)
    (h : ∀ n, HasSum (fun a => if f a = n then p a else 0) (q n)) :
    (∑' n : ℕ, ENNReal.ofReal ((n : ℝ) * q n)) =
      ∑' a, ENNReal.ofReal ((f a : ℝ) * p a) := by
  classical
  have hq (n : ℕ) : ENNReal.ofReal (q n) =
      ∑' a, if f a = n then ENNReal.ofReal (p a) else 0 := by
    rw [← (h n).tsum_eq, ENNReal.ofReal_tsum_of_nonneg
      (fun a => by split_ifs <;> simp [hp a]) (h n).summable]
    apply tsum_congr
    intro a
    split_ifs <;> simp
  simp_rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), hq, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro a
  simp only [mul_ite, mul_zero]
  rw [tsum_eq_single (f a)]
  · simp
  · intro n hn
    simp [Ne.symm hn]

/-- Scalar sector Markov inequality, retaining an infinite mean until the final premise. -/
theorem tail_markov_of_series (q : ℕ → ℝ) (hq : ∀ n, 0 ≤ q n) (hs : Summable q)
    (M : ℕ) (E : ℝ≥0∞) (hE : E = ∑' n : ℕ, ENNReal.ofReal ((n : ℝ) * q n))
    (hfinite : E < ⊤) :
    (∑' n, if M < n then q n else 0) ≤ E.toReal / ((M : ℝ) + 1) := by
  have ht : Summable (fun n => if M < n then q n else 0) :=
    Summable.of_nonneg_of_le (fun n => by split_ifs <;> simp [hq n])
      (fun n => by split_ifs <;> simp [hq n]) hs
  have hn : 0 ≤ ∑' n, if M < n then q n else 0 :=
    tsum_nonneg (fun n => by split_ifs <;> simp [hq n])
  have hc : 0 < (M : ℝ) + 1 := by positivity
  have hb : ENNReal.ofReal (((M : ℝ) + 1) * (∑' n, if M < n then q n else 0)) ≤ E := by
    rw [hE, ENNReal.ofReal_mul hc.le, ENNReal.ofReal_tsum_of_nonneg
      (fun n => by split_ifs <;> simp [hq n]) ht, ← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro n
    rw [← ENNReal.ofReal_mul hc.le]
    apply ENNReal.ofReal_le_ofReal
    by_cases hmn : M < n
    · rw [ite_eq_left hmn]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hmn) (hq n)
    · rw [ite_eq_right hmn, mul_zero]
      exact mul_nonneg (Nat.cast_nonneg n) (hq n)
  have hr := ENNReal.toReal_mono hfinite.ne hb
  rw [ENNReal.toReal_ofReal (mul_nonneg hc.le hn)] at hr
  exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hr)

end GptLean.PhysicalFock.NumberMoments

namespace GptLean.PhysicalFock

open MeasureTheory PhysicalNormalTrace PhysicalNormalTrace.StandardNormalTraceBackground

def fullNumberForm (BT : StandardNormalTraceBackground) (N : ℕ) :
    RemovalState.PositiveForm (BT.traceData (H := FullHilbert N)) :=
  PhysicalPhotonMarginal.fullForm BT (volume : Measure (SymmetricLift.Configuration N))
    (NormalPhoton.numberForm BT.normal (BT.realization PhotonFock).functional)

end GptLean.PhysicalFock
