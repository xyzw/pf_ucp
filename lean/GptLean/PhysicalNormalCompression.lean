import GptLean.PhysicalNormalTrace
import GptLean.PhysicalFockKrausL2
import GptLean.PhotonLocalizationLocalFormsOperators

/-!
Strongly convergent contraction multipliers converge on every positive
normal trace. The proof uses the actual spectral rank-one series. Scalar
electronic multipliers also commute with each coordinate of the photon
channel, including their adjoints.
-/

noncomputable section

namespace GptLean.PhysicalNormalCompression

open Filter Topology MeasureTheory PhysicalNormalTrace PhotonLocalization
  PhotonLocalizationChannel PhysicalFock
open scoped ENNReal InnerProductSpace

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (B : StandardNormalTraceBackground)

/-- Vector strong convergence of contractions gives trace-norm convergence
of their actual compressions on the complete positive cone. -/
theorem push_tendsto (L : ℕ → H →L[ℂ] H)
    (hcontract : ∀ m v, ‖L m v‖ ≤ ‖v‖)
    (hstrong : ∀ v, Tendsto (fun m => L m v) atTop (𝓝 v))
    {x : B.Trace H} (hx : x ∈ (B.realization H).rank.positive) :
    Tendsto (fun m => B.push (L m) x) atTop (𝓝 x) := by
  let R := (B.realization H).rank
  obtain ⟨v, hv⟩ := (B.realization H).spectral x hx
  change HasSum (fun n => R.rankOne (v n)) x at hv
  have hs : Summable (fun n => ‖v n‖ ^ 2) := by
    simpa only [R.trace_rankOne] using (R.trace.hasSum hv).summable
  have hlim := tendsto_tsum_of_dominated_convergence hs
    (fun n => (R.continuous_rankOne.tendsto (v n)).comp (hstrong (v n)))
    (Eventually.of_forall fun m n => by
      change ‖R.rankOne (L m (v n))‖ ≤ ‖v n‖ ^ 2
      rw [R.norm_rankOne]
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hcontract m (v n)))
  have heq (m : ℕ) : (∑' n, R.rankOne (L m (v n))) = B.push (L m) x := by
    have hpush : HasSum (fun n => R.rankOne (L m (v n))) (B.push (L m) x) := by
      simpa only [R, B.push_rankOne] using (B.push (L m)).hasSum hv
    exact hpush.tsum_eq
  simpa only [Function.comp_apply, heq, hv.tsum_eq] using hlim

section Scalar

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
  (a : X → ℝ) (ha : AEStronglyMeasurable a μ)
  (c : ℝ) (hc : ∀ᵐ x ∂μ, |a x| ≤ c)

omit [CompleteSpace H] in
/-- Scalar multiplication commutes with the actual lifted Kraus maps. -/
theorem multiplier_kraus (U : H →ₗᵢ[ℂ] lp (fun _ : ℕ => H) 2)
    (u : Lp H 2 μ) (n : ℕ) :
    KrausL2.lift μ U (realL2Multiplier a ha c hc u) n =
      realL2Multiplier a ha c hc (KrausL2.lift μ U u n) := by
  let P := (lp.evalCLM ℂ (fun _ : ℕ => H) 2 n).comp U.toContinuousLinearMap
  exact (congrArg (fun A : Lp H 2 μ →L[ℂ] Lp H 2 μ => A u)
    (realL2Multiplier_commute_compLpL a ha c hc P).eq).symm

/-- The adjoint commutation uses the proved self-adjointness of the real
multiplier rather than a second physical channel hypothesis. -/
theorem multiplier_adjoint_kraus (U : H →ₗᵢ[ℂ] lp (fun _ : ℕ => H) 2)
    (u : Lp H 2 μ) (n : ℕ) :
    KrausL2.lift μ U ((realL2Multiplier a ha c hc).adjoint u) n =
      (realL2Multiplier a ha c hc).adjoint (KrausL2.lift μ U u n) := by
  have hself := realL2Multiplier_selfadjoint (K := H) a ha c hc
  change KrausL2.lift μ U ((star (realL2Multiplier (K := H) a ha c hc)) u) n =
    (star (realL2Multiplier (K := H) a ha c hc)) (KrausL2.lift μ U u n)
  rw [hself.star_eq]
  exact multiplier_kraus a ha c hc U u n

end Scalar

end GptLean.PhysicalNormalCompression
