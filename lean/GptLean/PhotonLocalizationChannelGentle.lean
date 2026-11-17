import GptLean.PhotonLocalizationChannel
import GptLean.PhotonNumber
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
The gentle estimate for a normal channel with a positive vacuum Kraus
operator. The proof uses the explicit rank-one series, a universal
rank-one trace-norm inequality, and finite-sum Cauchy–Schwarz. It does not
assume a gentle estimate for a photon-localized state.
-/

namespace GptLean.PhotonLocalizationChannel

open Filter Topology Finset

variable {H T : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]

/-- The trace norm of a difference of positive rank-one operators is
bounded by the sum of the vector norms times their distance. This is
universal rank-one trace calculus, independent of the channel. -/
structure RankOneMetric (R : Gaussian.RankOneData H T) : Prop where
  norm_sub_le : ∀ u v,
    ‖R.rankOne u - R.rankOne v‖ ≤ (‖u‖ + ‖v‖) * ‖u - v‖

/-- The nonvacuum part of the actual Kraus series has trace norm at most
its mass. No finite Kraus truncation is assumed. -/
theorem pure_sub_vacuum_norm_le (R : Gaussian.RankOneData H T)
    (U : KrausIsometry H) (v : H) :
    ‖pure R U v - R.rankOne (U v 0)‖ ≤ ‖v‖ ^ 2 - ‖U v 0‖ ^ 2 := by
  have ht := hasSum_ite_sub_hasSum (pure_hasSum R U v) 0
  have hm := hasSum_ite_sub_hasSum (kraus_mass U v) 0
  have he : (fun a => ‖if a = 0 then (0 : T) else R.rankOne (U v a)‖) =
      (fun a => if a = 0 then (0 : ℝ) else ‖U v a‖ ^ 2) := by
    funext a
    split_ifs <;> simp [R.norm_rankOne]
  calc ‖pure R U v - R.rankOne (U v 0)‖
      = ‖∑' a, if a = 0 then (0 : T) else R.rankOne (U v a)‖ := congrArg norm ht.tsum_eq.symm
    _ ≤ ∑' a, ‖if a = 0 then (0 : T) else R.rankOne (U v a)‖ :=
      norm_tsum_le_tsum_norm (he ▸ hm.summable)
    _ = ‖v‖ ^ 2 - ‖U v 0‖ ^ 2 := by rw [he]; exact hm.tsum_eq

/-- The vacuum/nonvacuum split gives the vector-level gentle estimate. -/
theorem pure_gentle (R : Gaussian.RankOneData H T) (M : RankOneMetric R)
    (U : KrausIsometry H) (v : H) :
    ‖R.rankOne v - pure R U v‖ ≤
      2 * ‖v‖ * ‖v - U v 0‖ + (‖v‖ ^ 2 - ‖U v 0‖ ^ 2) := by
  have hk : ‖U v 0‖ ≤ ‖v‖ := by
    simpa only [U.norm_map] using lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) (U v) 0
  calc ‖R.rankOne v - pure R U v‖
      ≤ ‖R.rankOne v - R.rankOne (U v 0)‖ + ‖R.rankOne (U v 0) - pure R U v‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (‖v‖ + ‖U v 0‖) * ‖v - U v 0‖ + (‖v‖ ^ 2 - ‖U v 0‖ ^ 2) := by
      rw [norm_sub_rev (R.rankOne (U v 0))]
      exact add_le_add (M.norm_sub_le _ _) (pure_sub_vacuum_norm_le R U v)
    _ ≤ 2 * ‖v‖ * ‖v - U v 0‖ + (‖v‖ ^ 2 - ‖U v 0‖ ^ 2) := by
      nlinarith [norm_nonneg (v - U v 0)]

namespace NormalTraceData

variable {R : Gaussian.RankOneData H T} (N : NormalTraceData R)

/-- The mixed-state gentle bound follows from finite-sum Cauchy–Schwarz
and the normal spectral series. `hK` is the elementary positive-contraction
inequality for the vacuum Kraus operator, before taking traces. `loss` is
the usual bounded effect measuring a nonvacuum environment. -/
theorem gentle (M : RankOneMetric R) (U : KrausIsometry H)
    (loss : T →L[ℝ] ℝ)
    (hloss : ∀ v, loss (R.rankOne v) = ‖v‖ ^ 2 - ‖U v 0‖ ^ 2)
    (hK : ∀ v, ‖v - U v 0‖ ^ 2 ≤ ‖v‖ ^ 2 - ‖U v 0‖ ^ 2)
    {x : T} (hx : x ∈ R.positive) :
    ‖x - N.extend U x‖ ≤ 2 * √(R.trace x * loss x) + loss x := by
  obtain ⟨v, hv⟩ := N.positive_decomposition x hx
  have hm : HasSum (fun n => ‖v n‖ ^ 2) (R.trace x) := by
    simpa only [R.trace_rankOne] using R.trace.hasSum hv
  have hl : HasSum (fun n => ‖v n‖ ^ 2 - ‖U (v n) 0‖ ^ 2) (loss x) := by
    simpa only [hloss] using loss.hasSum hv
  have hl0 (n : ℕ) : 0 ≤ ‖v n‖ ^ 2 - ‖U (v n) 0‖ ^ 2 := (sq_nonneg _).trans (hK _)
  have hm0 : 0 ≤ R.trace x := tsum_nonneg (fun n => sq_nonneg _) |>.trans_eq hm.tsum_eq
  have hl0' : 0 ≤ loss x := tsum_nonneg hl0 |>.trans_eq hl.tsum_eq
  apply le_of_tendsto' (hv.sub (N.extend_hasSum U hv)).norm
  intro s
  have hms : (∑ n ∈ s, ‖v n‖ ^ 2) ≤ R.trace x := by
    rw [← hm.tsum_eq]
    exact hm.summable.sum_le_tsum s (fun _ _ => sq_nonneg _)
  have hls : (∑ n ∈ s, (‖v n‖ ^ 2 - ‖U (v n) 0‖ ^ 2)) ≤ loss x := by
    rw [← hl.tsum_eq]
    exact hl.summable.sum_le_tsum s (fun n _ => hl0 n)
  have hds : (∑ n ∈ s, ‖v n - U (v n) 0‖ ^ 2) ≤ loss x :=
    (sum_le_sum (fun n _ => hK (v n))).trans hls
  have hcs := sum_mul_sq_le_sq_mul_sq s
    (fun n => ‖v n‖) (fun n => ‖v n - U (v n) 0‖)
  have hcrosssq : (∑ n ∈ s, ‖v n‖ * ‖v n - U (v n) 0‖) ^ 2 ≤
      R.trace x * loss x := hcs.trans
    (mul_le_mul hms hds (sum_nonneg (fun _ _ => sq_nonneg _)) hm0)
  have hcross : (∑ n ∈ s, ‖v n‖ * ‖v n - U (v n) 0‖) ≤
      √(R.trace x * loss x) := by
    have hc0 : 0 ≤ ∑ n ∈ s, ‖v n‖ * ‖v n - U (v n) 0‖ :=
      sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    nlinarith [Real.sq_sqrt (mul_nonneg hm0 hl0'), Real.sqrt_nonneg (R.trace x * loss x)]
  calc ‖∑ n ∈ s, (R.rankOne (v n) - pure R U (v n))‖
      ≤ ∑ n ∈ s, ‖R.rankOne (v n) - pure R U (v n)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ s, (2 * ‖v n‖ * ‖v n - U (v n) 0‖ +
        (‖v n‖ ^ 2 - ‖U (v n) 0‖ ^ 2)) := sum_le_sum (fun n _ => pure_gentle R M U (v n))
    _ ≤ 2 * √(R.trace x * loss x) + loss x := by
      simp only [sum_add_distrib, mul_assoc, ← mul_sum]
      linarith

/-- Normalization gives precisely the modulus used by photon-loss
compactness, with discarded probability identified by its bounded effect. -/
theorem gentle_state (M : RankOneMetric R) (U : KrausIsometry H)
    (loss : T →L[ℝ] ℝ)
    (hloss : ∀ v, loss (R.rankOne v) = ‖v‖ ^ 2 - ‖U v 0‖ ^ 2)
    (hK : ∀ v, ‖v - U v 0‖ ^ 2 ≤ ‖v‖ ^ 2 - ‖U v 0‖ ^ 2)
    {x : T} (hx : x ∈ N.states) :
    ‖x - N.extend U x‖ ≤ PhotonLoss.lossModulus (loss x) := by
  simpa only [PhotonLoss.lossModulus, hx.2, one_mul] using N.gentle M U loss hloss hK hx.1

end NormalTraceData

end GptLean.PhotonLocalizationChannel
