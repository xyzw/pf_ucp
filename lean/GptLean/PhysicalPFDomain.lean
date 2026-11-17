import GptLean.PhysicalPFForm

/-! The exact pure-state finite domain of the constructed normal PF form. -/

noncomputable section

namespace GptLean.PhysicalPFRadiation

open MeasureTheory PhysicalFock PhysicalNormalTrace PhysicalClosedForms PhysicalPFReference
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000

private theorem domain_iff_of_graph_range {Q H K : Type*}
    [AddCommGroup H] [Module ℂ H] [AddCommGroup K] [Module ℂ K]
    (g : Q → H × K) (D : H →ₗ.[ℂ] K)
    (hD : (D.graph : Set (H × K)) = Set.range g) (v : H) :
    v ∈ D.domain ↔ ∃ q, (g q).1 = v := by
  constructor
  · intro hv
    obtain ⟨w, hw⟩ := LinearPMap.mem_domain_iff.mp hv
    change (v, w) ∈ (D.graph : Set (H × K)) at hw
    rw [hD] at hw
    obtain ⟨q, hq⟩ := hw
    exact ⟨q, congrArg Prod.fst hq⟩
  · rintro ⟨q, hq⟩
    apply LinearPMap.mem_domain_iff.mpr
    refine ⟨(g q).2, ?_⟩
    change (v, (g q).2) ∈ (D.graph : Set (H × K))
    rw [hD]
    exact ⟨q, Prod.ext hq rfl⟩

variable (I : Type) [Fintype I] [DecidableEq I]
  (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground)

theorem normalEnergy_operator_domain (e : ℝ) (v : WaveSpace I) :
    v ∈ (energyOperator I V C κ hκ M hbound e).domain ↔
      ∃ u : Reference I V, inclusion I V u = v := by
  have hg : ((energyOperator I V C κ hκ M hbound e).graph :
      Set (WaveSpace I × EnergyOutput I)) = Set.range (energyGraphMap I V C κ hκ M hbound e) :=
    congrArg (fun G : Submodule ℂ (WaveSpace I × EnergyOutput I) =>
      (G : Set (WaveSpace I × EnergyOutput I))) (energyOperator_graph I V C κ hκ M hbound e)
  exact domain_iff_of_graph_range (Q := Reference I V) (H := WaveSpace I) (K := EnergyOutput I)
    (g := energyGraphMap I V C κ hκ M hbound e)
    (D := energyOperator I V C κ hκ M hbound e) hg v

theorem normalEnergy_rankOne_finite_iff (e : ℝ) (v : WaveSpace I) :
    (normalEnergy I V C κ hκ M hbound B S e).expectation
      ((B.realization (WaveSpace I)).rank.rankOne v) < ⊤ ↔
      ∃ u : Reference I V, inclusion I V u = v := by
  exact (positiveForm_finite_iff
    (S.resolve (WaveSpace I) (EnergyOutput I) (energyOperator I V C κ hκ M hbound e)
      (energyOperator_closed I V C κ hκ M hbound e))
    B.normal (B.realization (WaveSpace I)).functional v).trans
      (normalEnergy_operator_domain I V C κ hκ M hbound e v)


end GptLean.PhysicalPFRadiation
