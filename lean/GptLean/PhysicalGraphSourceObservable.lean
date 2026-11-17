import GptLean.PhysicalGraphCrossObservable

/-! Construct a graph observable directly from finite-energy source vectors. -/

noncomputable section

namespace GptLean.PhysicalGraphForms.CoerciveGraph

open PhysicalClosedForms PhysicalNormalTrace
open scoped ENNReal

variable {E H K F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  (G : CoerciveGraph E H K)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground)

def crossObservable_of_source (L R : E →L[ℂ] F)
    (energy : RemovalState.PositiveForm (B.traceData (H := H)))
    (hsource : ∀ x ∈ (B.traceData (H := H)).positive, energy.expectation x < ⊤ →
      ∃ u : ℕ → E, HasSum (fun n => (B.realization H).rank.rankOne (G.value (u n))) x ∧
        Summable (fun n => ‖u n‖ ^ 2)) : RemovalState.FormObservable energy :=
  G.crossObservable B S L R energy (by
    intro x hx he
    obtain ⟨u, hu, hs⟩ := hsource x hx he
    exact ⟨(G.append (L + R)).normalForm_source_finite B S hu hs,
      (G.append (L - R)).normalForm_source_finite B S hu hs⟩)

end GptLean.PhysicalGraphForms.CoerciveGraph
