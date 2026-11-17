import GptLean.PhysicalL2Countable
import GptLean.PhysicalPhotonNormalMoments

/-!
The photon marginal of the actual electronic L² state is obtained by tracing
its constructed spatial Hilbert-basis coefficients. Positivity, trace and every
bounded photon observable are transported from the same normal trace family.
No marginal compatibility or photon-moment identity is supplied as a premise.
-/

noncomputable section
namespace GptLean.PhysicalPhotonMarginal

open MeasureTheory PhotonLocalizationChannel RemovalState PhysicalNormalTrace
  PhysicalNormalTrace.StandardNormalTraceBackground PhysicalL2HilbertSum
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

section Evaluation
variable {H T : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup T] [NormedSpace ℝ T] {R : Gaussian.RankOneData H T}

def evaluation (F : NormalFunctionalData R) (A : H →L[ℂ] H) : T →L[ℝ] ℂ :=
  ((ContinuousLinearMap.apply ℂ ℂ A).restrictScalars ℝ).comp F.repr

@[simp] theorem evaluation_apply (F : NormalFunctionalData R) (A : H →L[ℂ] H) (x : T) :
    evaluation F A x = F.repr x A := rfl
end Evaluation

variable (B : StandardNormalTraceBackground)

section Universal
variable {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- An ordinary Hilbert-space observable identity determines its normal partial-trace identity. -/
theorem partialTrace_evaluation
    (U : H →ₗᵢ[ℂ] lp (fun _ : ℕ => K) 2) (A : K →L[ℂ] K) (Afull : H →L[ℂ] H)
    (hU : ∀ v, HasSum (fun n => ⟪U v n, A (U v n)⟫_ℂ) ⟪v, Afull v⟫_ℂ)
    {x : B.Trace H} (hx : x ∈ (B.realization H).rank.positive) :
    (B.realization K).functional.repr (B.partialTrace U x) A =
      (B.realization H).functional.repr x Afull := by
  have hpure (v : H) :
      (B.realization K).functional.repr (B.partialTrace U ((B.realization H).rank.rankOne v)) A =
        ⟪v, Afull v⟫_ℂ := by
    have hs := (evaluation (B.realization K).functional A).hasSum
      (Repair.rankOneSeries_hasSum (B.realization K).rank (dilation_mass U v))
    simp only [evaluation_apply, (B.realization K).functional.rankOne] at hs
    rw [B.partialTrace_rankOne]
    exact hs.unique (hU v)
  obtain ⟨v, hv⟩ := (B.realization H).spectral x hx
  have h₁ := (evaluation (B.realization K).functional A).hasSum ((B.partialTrace U).hasSum hv)
  have h₂ := (evaluation (B.realization H).functional Afull).hasSum hv
  simp only [evaluation_apply, hpure] at h₁
  simp only [evaluation_apply, (B.realization H).functional.rankOne] at h₂
  exact h₁.unique h₂
end Universal

section Spatial
variable {X H : Type} [MeasurableSpace X] (μ : Measure X) [IsSeparable μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual spatial partial trace, including its fixed basis construction. -/
def marginal : B.Trace (Lp H 2 μ) →L[ℝ] B.Trace H :=
  B.partialTrace (spatialCoefficients μ H)

theorem marginal_positive {x : B.Trace (Lp H 2 μ)}
    (hx : x ∈ (B.realization (Lp H 2 μ)).rank.positive) :
    marginal B μ x ∈ (B.realization H).rank.positive :=
  B.partialTrace_positive _ hx

theorem marginal_trace {x : B.Trace (Lp H 2 μ)}
    (hx : x ∈ (B.realization (Lp H 2 μ)).rank.positive) :
    (B.realization H).rank.trace (marginal B μ x) = (B.realization (Lp H 2 μ)).rank.trace x :=
  B.partialTrace_trace _ hx

/-- The marginal and full state give exactly the same bounded photon expectation. -/
theorem marginal_evaluation (A : H →L[ℂ] H) {x : B.Trace (Lp H 2 μ)}
    (hx : x ∈ (B.realization (Lp H 2 μ)).rank.positive) :
    (B.realization H).functional.repr (marginal B μ x) A =
      (B.realization (Lp H 2 μ)).functional.repr x (A.compLpL 2 μ) :=
  partialTrace_evaluation B (spatialCoefficients μ H) A (A.compLpL 2 μ)
    (spatialCoefficients_observable_hasSum μ H A) hx

/-- Bounded spectral caps identify all nonnegative unbounded photon forms as well. -/
theorem marginal_iSup (A : ℕ → H →L[ℂ] H) {x : B.Trace (Lp H 2 μ)}
    (hx : x ∈ (B.realization (Lp H 2 μ)).rank.positive) :
    (⨆ n, ENNReal.ofReal ((B.realization H).functional.repr (marginal B μ x) (A n)).re) =
      ⨆ n, ENNReal.ofReal ((B.realization (Lp H 2 μ)).functional.repr x ((A n).compLpL 2 μ)).re := by
  simp_rw [marginal_evaluation B μ _ hx]

/-- Pull back any positive photon form through the constructed marginal. -/
def fullForm (E : PositiveForm (B.traceData (H := H))) : PositiveForm (B.traceData (H := Lp H 2 μ)) where
  truncation n := (E.truncation n).comp (marginal B μ)
  nonneg n x hx := E.nonneg n (marginal B μ x) (marginal_positive B μ hx)
  monotone x hx := E.monotone (marginal B μ x) (marginal_positive B μ hx)

@[simp] theorem fullForm_expectation (E : PositiveForm (B.traceData (H := H))) (x : B.Trace (Lp H 2 μ)) :
    (fullForm B μ E).expectation x = E.expectation (marginal B μ x) := rfl
end Spatial

section Physical
variable (N : ℕ)

/-- The same photon marginal on the concrete full electronic/photon Hilbert space. -/
def photonMarginal : B.FullTrace N →L[ℝ] B.Trace PhysicalFock.PhotonFock :=
  marginal B (volume : Measure (SymmetricLift.Configuration N))

theorem photonMarginal_positive {x : B.FullTrace N}
    (hx : x ∈ (B.realization (FullHilbert N)).rank.positive) :
    photonMarginal B N x ∈ (B.realization PhysicalFock.PhotonFock).rank.positive :=
  marginal_positive B _ hx

theorem photonMarginal_trace {x : B.FullTrace N}
    (hx : x ∈ (B.realization (FullHilbert N)).rank.positive) :
    (B.realization PhysicalFock.PhotonFock).rank.trace (photonMarginal B N x) =
      (B.realization (FullHilbert N)).rank.trace x :=
  marginal_trace B _ hx

theorem photonMarginal_evaluation (A : PhysicalFock.PhotonFock →L[ℂ] PhysicalFock.PhotonFock)
    {x : B.FullTrace N} (hx : x ∈ (B.realization (FullHilbert N)).rank.positive) :
    (B.realization PhysicalFock.PhotonFock).functional.repr (photonMarginal B N x) A =
      (B.realization (FullHilbert N)).functional.repr x (A.compLpL 2 volume) :=
  marginal_evaluation B _ A hx
end Physical
end GptLean.PhysicalPhotonMarginal
