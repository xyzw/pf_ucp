import GptLean.PhysicalFockHardVacuumBounds

/-!
The vector hard-vacuum estimates extend to every positive normal input
under the actual trace push-forward, using its positive spectral series.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory PhotonLocalizationChannel PhysicalNormalTrace RemovalState
open Filter Topology
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

section PositiveTrace

private theorem push_rankOne_hasSum
    {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (B : StandardNormalTraceBackground) (J : H →L[ℂ] K)
    {v : ℕ → H} {x : B.Trace H}
    (hv : HasSum (fun n => (B.realization H).rank.rankOne (v n)) x) :
    HasSum (fun n => (B.realization K).rank.rankOne (J (v n))) (B.push J x) :=
  ((B.push J).hasSum hv).congr_fun fun n => (B.push_rankOne J (v n)).symm

private theorem push_form_eq_zero
    {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (B : StandardNormalTraceBackground) (J : H →L[ℂ] K)
    (E : PositiveForm (B.traceData (H := K)))
    (hE : ∀ u, E.expectation ((B.realization K).rank.rankOne (J u)) = 0)
    (x : B.Trace H) (hx : x ∈ (B.realization H).rank.positive) :
    E.expectation (B.push J x) = 0 := by
  obtain ⟨v, hv⟩ := (B.realization H).spectral x hx
  have hs := push_rankOne_hasSum B J hv
  rw [← hs.tsum_eq, E.expectation_tsum hs.summable
    (fun n => (B.realization K).rank.rankOne_positive (J (v n)))]
  exact ENNReal.tsum_eq_zero.mpr fun n => hE (v n)

private theorem push_form_le
    {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (B : StandardNormalTraceBackground) (J : H →L[ℂ] K)
    (E F : PositiveForm (B.traceData (H := K))) (c : ℝ≥0∞)
    (hEF : ∀ u, E.expectation ((B.realization K).rank.rankOne (J u)) ≤
      c * F.expectation ((B.realization K).rank.rankOne (J u)))
    (x : B.Trace H) (hx : x ∈ (B.realization H).rank.positive) :
    E.expectation (B.push J x) ≤ c * F.expectation (B.push J x) := by
  obtain ⟨v, hv⟩ := (B.realization H).spectral x hx
  have hs := push_rankOne_hasSum B J hv
  rw [← hs.tsum_eq, E.expectation_tsum hs.summable
    (fun n => (B.realization K).rank.rankOne_positive (J (v n))),
    F.expectation_tsum hs.summable
    (fun n => (B.realization K).rank.rankOne_positive (J (v n))),
    ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum fun n => hEF (v n)

private theorem submodule_push_form_eq_zero
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (B : StandardNormalTraceBackground) (S : Submodule ℂ H) [CompleteSpace S]
    (E : PositiveForm (B.traceData (H := H)))
    (hE : ∀ u ∈ S, E.expectation ((B.realization H).rank.rankOne u) = 0)
    (x : B.Trace S) (hx : x ∈ (B.realization S).rank.positive) :
    E.expectation (B.push S.subtypeL x) = 0 :=
  push_form_eq_zero B S.subtypeL E (fun u => hE u.val u.property) x hx

private theorem submodule_push_form_le
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (B : StandardNormalTraceBackground) (S : Submodule ℂ H) [CompleteSpace S]
    (E F : PositiveForm (B.traceData (H := H))) (c : ℝ≥0∞)
    (hEF : ∀ u ∈ S, E.expectation ((B.realization H).rank.rankOne u) ≤
      c * F.expectation ((B.realization H).rank.rankOne u))
    (x : B.Trace S) (hx : x ∈ (B.realization S).rank.positive) :
    E.expectation (B.push S.subtypeL x) ≤ c * F.expectation (B.push S.subtypeL x) :=
  push_form_le B S.subtypeL E F c (fun u => hEF u.val u.property) x hx

attribute [local irreducible] hardPhotonVacuumEmbedding
  StandardNormalTraceBackground.normal generatedSubspace
  NormalPhoton.softEnergyForm NormalPhoton.numberForm NormalPhoton.radiationForm

variable (B : StandardNormalTraceBackground) (BF : StandardSymmetricFockExponential)

private theorem hardPhotonVacuumEmbedding_clm (κ : ℝ) :
    (hardPhotonVacuumEmbedding BF κ).toContinuousLinearMap =
      (generatedFockSubspace (hardOnePhoton κ)).subtypeL :=
  ContinuousLinearMap.ext (hardPhotonVacuumEmbedding_apply BF κ)

/-- Vacuum insertion annihilates the soft energy of every positive hard
normal state, using the actual trace push-forward. -/
theorem hardPhotonVacuumEmbedding_push_softEnergy (κ : ℝ)
    (x : B.Trace (generatedFockSubspace (hardOnePhoton κ)))
    (hx : x ∈ (B.realization (generatedFockSubspace (hardOnePhoton κ))).rank.positive) :
    (NormalPhoton.softEnergyForm (B.normal (H := PhotonFock))
      (B.realization PhotonFock).functional κ).expectation
        (B.push (hardPhotonVacuumEmbedding BF κ).toContinuousLinearMap x) = 0 := by
  have hpure := @hardSupported_normal_softEnergy (B.Trace PhotonFock)
    (B.realization PhotonFock).traceSpace.normed
    (B.realization PhotonFock).traceSpace.space
    (B.realization PhotonFock).traceSpace.complete
    (B.realization PhotonFock).rank (B.normal (H := PhotonFock))
    (B.realization PhotonFock).functional κ
  have he := submodule_push_form_eq_zero B (generatedFockSubspace (hardOnePhoton κ))
    (NormalPhoton.softEnergyForm (B.normal (H := PhotonFock))
      (B.realization PhotonFock).functional κ)
    (fun u hu => hpure u (hardSupported_of_mem_generated κ u hu)) x hx
  exact (congrArg (fun L : generatedFockSubspace (hardOnePhoton κ) →L[ℂ] PhotonFock =>
    (NormalPhoton.softEnergyForm (B.normal (H := PhotonFock))
    (B.realization PhotonFock).functional κ).expectation (B.push L x))
      (hardPhotonVacuumEmbedding_clm BF κ)).trans he

/-- The hard number bound extends to arbitrary positive normal inputs,
without assuming finite total number in advance. -/
theorem hardPhotonVacuumEmbedding_push_number_le {κ : ℝ} (hκ : 0 < κ)
    (x : B.Trace (generatedFockSubspace (hardOnePhoton κ)))
    (hx : x ∈ (B.realization (generatedFockSubspace (hardOnePhoton κ))).rank.positive) :
    (NormalPhoton.numberForm (B.normal (H := PhotonFock))
      (B.realization PhotonFock).functional).expectation
        (B.push (hardPhotonVacuumEmbedding BF κ).toContinuousLinearMap x) ≤
      ENNReal.ofReal κ⁻¹ *
        (NormalPhoton.radiationForm (B.normal (H := PhotonFock))
          (B.realization PhotonFock).functional).expectation
            (B.push (hardPhotonVacuumEmbedding BF κ).toContinuousLinearMap x) := by
  have hpure := @hardSupported_normal_number_le (B.Trace PhotonFock)
    (B.realization PhotonFock).traceSpace.normed
    (B.realization PhotonFock).traceSpace.space
    (B.realization PhotonFock).traceSpace.complete
    (B.realization PhotonFock).rank (B.normal (H := PhotonFock))
    (B.realization PhotonFock).functional κ hκ
  have he := submodule_push_form_le B (generatedFockSubspace (hardOnePhoton κ))
    (NormalPhoton.numberForm (B.normal (H := PhotonFock))
      (B.realization PhotonFock).functional)
    (NormalPhoton.radiationForm (B.normal (H := PhotonFock))
      (B.realization PhotonFock).functional) (ENNReal.ofReal κ⁻¹)
    (fun u hu => hpure u (hardSupported_of_mem_generated κ u hu)) x hx
  exact (congrArg (fun L : generatedFockSubspace (hardOnePhoton κ) →L[ℂ] PhotonFock =>
    (NormalPhoton.numberForm (B.normal (H := PhotonFock))
    (B.realization PhotonFock).functional).expectation (B.push L x) ≤
      ENNReal.ofReal κ⁻¹ *
        (NormalPhoton.radiationForm (B.normal (H := PhotonFock))
          (B.realization PhotonFock).functional).expectation (B.push L x))
            (hardPhotonVacuumEmbedding_clm BF κ)).mpr he

end PositiveTrace

end GptLean.PhysicalFock
