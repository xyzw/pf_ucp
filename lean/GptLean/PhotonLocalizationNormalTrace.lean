import GptLean.PhotonLocalizationChannel
import GptLean.PhotonLocalizationTrace
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
The normal trace representation used by the compactness proof.

Only the universal isometric trace pairing and its rank-one evaluation
are background. Positivity, mass and the square trace series are derived
for every positive state and for the explicit channel source vectors.
-/

namespace GptLean.PhotonLocalizationChannel

open scoped InnerProductSpace ComplexOrder

variable {H T : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]

/-- The standard isometric embedding of trace class into the dual of
bounded operators, uniform over all operators and all pure vectors. -/
structure NormalFunctionalData (R : Gaussian.RankOneData H T) where
  repr : T →L[ℝ] ((H →L[ℂ] H) →L[ℂ] ℂ)
  isometry : Isometry repr
  rankOne : ∀ v a, repr (R.rankOne v) a = ⟪v, a v⟫_ℂ

namespace NormalFunctionalData

variable {R : Gaussian.RankOneData H T} (F : NormalFunctionalData R)

omit [CompleteSpace T] in
theorem observable_hasSum {v : ℕ → H} {x : T}
    (hv : HasSum (fun k => R.rankOne (v k)) x) (a : H →L[ℂ] H) :
    HasSum (fun k => ⟪v k, a (v k)⟫_ℂ) (F.repr x a) := by
  have h := ((ContinuousLinearMap.apply ℂ ℂ a).restrictScalars ℝ).hasSum
    (F.repr.hasSum hv)
  change HasSum (fun k => F.repr (R.rankOne (v k)) a) (F.repr x a) at h
  simpa only [F.rankOne] using h

theorem square_hasSum {v : ℕ → H} {x : T}
    (hv : HasSum (fun k => R.rankOne (v k)) x) (a : H →L[ℂ] H) :
    HasSum (fun k => ‖a (v k)‖ ^ 2) (F.repr x (star a * a)).re := by
  have h := Complex.reCLM.hasSum (F.observable_hasSum hv (star a * a))
  change HasSum (fun k => (⟪v k, (star a * a) (v k)⟫_ℂ).re)
    (F.repr x (star a * a)).re at h
  convert h using 1
  ext k
  exact a.apply_norm_sq_eq_inner_adjoint_right (v k)

theorem square_trace {v : ℕ → H} {x : T}
    (hv : HasSum (fun k => R.rankOne (v k)) x) (a : H →L[ℂ] H) :
    (F.repr x (star a * a)).re = ∑' k, ‖a (v k)‖ ^ 2 :=
  (F.square_hasSum hv a).tsum_eq.symm

/-- Vector commutation with an electronic observable gives equality of
its original and localized normal trace pairings. -/
theorem electronic (N : NormalTraceData R) (U : KrausIsometry H)
    (W : H →L[ℂ] H) (hW : ∀ v a, U (W v) a = W (U v a))
    {x : T} (hx : x ∈ R.positive) :
    F.repr (N.extend U x) W = F.repr x W := by
  let B : T →L[ℝ] ℂ :=
    ((ContinuousLinearMap.apply ℂ ℂ W).restrictScalars ℝ).comp F.repr
  exact N.electronic U W B (fun v => F.rankOne v W) hW hx

theorem mass (N : NormalTraceData R) {x : T} (hx : x ∈ R.positive) :
    (F.repr x 1).re = R.trace x := by
  obtain ⟨v, hv⟩ := N.positive_decomposition x hx
  have h₁ := F.square_hasSum hv 1
  have h₂ := R.trace.hasSum hv
  simp only [star_one, one_mul, one_apply_eq_self] at h₁
  simp only [R.trace_rankOne] at h₂
  exact h₁.unique h₂

theorem positive (N : NormalTraceData R) {x : T} (hx : x ∈ R.positive) :
    PhotonTrace.IsPosFunctional (F.repr x) := by
  obtain ⟨v, hv⟩ := N.positive_decomposition x hx
  intro a
  apply Complex.nonneg_iff.mpr
  constructor
  · rw [F.square_trace hv a]
    exact tsum_nonneg fun _ => sq_nonneg _
  · have h := Complex.imCLM.hasSum (F.observable_hasSum hv (star a * a))
    change HasSum (fun k => (⟪v k, (star a * a) (v k)⟫_ℂ).im)
      (F.repr x (star a * a)).im at h
    have hz : (fun k => (⟪v k, (star a * a) (v k)⟫_ℂ).im) = 0 := by
      funext k
      change (⟪v k, a.adjoint (a (v k))⟫_ℂ).im = 0
      rw [ContinuousLinearMap.adjoint_inner_right]
      exact inner_self_im (𝕜 := ℂ) (a (v k))
    rw [hz] at h
    exact (h.unique hasSum_zero).symm

end NormalFunctionalData

end GptLean.PhotonLocalizationChannel
