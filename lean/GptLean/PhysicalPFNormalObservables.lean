import GptLean.PhysicalPFObservables

/-! The actual finite-energy reference source supplies a normal form observable. -/

noncomputable section
namespace GptLean.PhysicalPFSource
open MeasureTheory PhysicalFock PhysicalPFReference PhysicalNormalTrace
  PhysicalClosedForms PhysicalGraphForms PhotonLocalizationChannel PhotonLocalization
open scoped ENNReal NNReal InnerProductSpace
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000
variable (I : Type) [Fintype I] [DecidableEq I]
  (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground) (e : ℝ)

theorem reference_source_summable (x : B.Trace (WaveSpace I))
    (hx : x ∈ (B.traceData (H := WaveSpace I)).positive)
    (he : (normalEnergy I V C κ hκ M hbound B S e).expectation x < ⊤) :
    ∃ u : ℕ → Reference I V,
      HasSum (fun n => (B.realization (WaveSpace I)).rank.rankOne (inclusion I V (u n))) x ∧
        Summable (fun n => ‖u n‖ ^ 2) := by
  have hx' : x ∈ (B.realization (WaveSpace I)).rank.positive := hx
  have hex : Nonempty (Source I V B x) :=
    source_exists I V C κ hκ M hbound B S e (x := x) hx' he
  obtain ⟨s⟩ := hex
  exact ⟨s.vector, s.hasSum, s.reference_summable C κ hκ M hbound S e he⟩

def observable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (L R : Reference I V →L[ℂ] F) :=
  (coerciveGraph I V C κ hκ M hbound e).crossObservable_of_source B S L R
    (normalEnergy I V C κ hκ M hbound B S e)
    (reference_source_summable I V C κ hκ M hbound B S e)

theorem observable_rankOne {F : Type} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F]
    (L R : Reference I V →L[ℂ] F) (u : Reference I V) :
    (observable I V C κ hκ M hbound B S e L R).value
      ((B.realization (WaveSpace I)).rank.rankOne (inclusion I V u)) = (⟪L u, R u⟫_ℂ).re :=
  (coerciveGraph I V C κ hκ M hbound e).crossValue_rankOne B S L R u

end GptLean.PhysicalPFSource
