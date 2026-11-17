import GptLean.PhysicalGraphCurrentObservable
import GptLean.PhysicalGraphCurrentPassage

/-! Adding trace mass controls every symmetric bounded map from the energy graph. -/

noncomputable section

namespace GptLean.PhysicalGraphForms.CoerciveGraph

open PhysicalNormalTrace PhysicalClosedForms RemovalState PhotonLocalizationCurrent Filter Topology
open scoped ENNReal InnerProductSpace

variable {E H K : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (G : CoerciveGraph E H K) (J : E →L[ℂ] H)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground)
  (hsym : ∀ u v, ⟪G.value u, J v⟫_ℂ = ⟪J u, G.value v⟫_ℂ)

def massCurrentObservable : FormObservable ((G.append G.value).normalForm B S) :=
  (G.append G.value).currentObservable J B S (‖J‖ * G.constant)
    (mul_nonneg (ContinuousLinearMap.opNorm_nonneg J) G.constant.coe_nonneg)
    hsym (G.operator_append_value_bound J)

def massCurrentRelativeApproximation :
    RelativeApproximation (R := (B.realization H).rank)
      ((G.append G.value).normalForm B S) (G.massCurrentObservable J B S hsym) :=
  (G.append G.value).currentRelativeApproximation J B S (‖J‖ * G.constant)
    (mul_nonneg (ContinuousLinearMap.opNorm_nonneg J) G.constant.coe_nonneg)
    hsym (G.operator_append_value_bound J)

include hsym in
theorem massCurrent_limit (u : ℕ → B.Trace H) (x : B.Trace H)
    (hlim : Tendsto u atTop (𝓝 x))
    (source : ∀ n, ∃ v : ℕ → E,
      HasSum (fun k => (B.realization H).rank.rankOne (G.value (v k))) (u n) ∧
        Summable (fun k => ‖v k‖ ^ 2))
    (limitSource : ∃ v : ℕ → E,
      HasSum (fun k => (B.realization H).rank.rankOne (G.value (v k))) x ∧
        Summable (fun k => ‖v k‖ ^ 2))
    (bound : ℝ)
    (hu : ∀ n, (((G.append G.value).normalForm B S).expectation (u n)).toReal ≤ bound)
    (hx : (((G.append G.value).normalForm B S).expectation x).toReal ≤ bound) :
    Tendsto (fun n => (G.append G.value).crossValue B S G.value J (u n)) atTop
      (𝓝 ((G.append G.value).crossValue B S G.value J x)) :=
  (G.append G.value).current_limit J B S (‖J‖ * G.constant)
    (mul_nonneg (ContinuousLinearMap.opNorm_nonneg J) G.constant.coe_nonneg)
    hsym (G.operator_append_value_bound J) u x hlim source limitSource bound hu hx

end GptLean.PhysicalGraphForms.CoerciveGraph
