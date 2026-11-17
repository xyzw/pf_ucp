import GptLean.PhysicalFockRadiationSlices
import GptLean.PhysicalFockFullFormCalculus
import GptLean.PhysicalSpatialRadiationDomain

/-!
The channel form calculus and the physical normal number/radiation forms
agree on the same positive trace states. Both electronic constructions
use the identical spatial coefficient marginal. The existing integral,
radiation graph and finite-domain identifications therefore apply to the
constructed channel observables without another analytic assumption.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory PhotonLocalizationChannel PhysicalNormalTrace PhysicalL2HilbertSum
  RemovalState PhotonLocalizationFormBounds PhysicalPhotonMarginal
  PhysicalNormalTrace.StandardNormalTraceBackground
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types false

section Normal
variable {H T : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : Gaussian.RankOneData H T} (normal : NormalTraceData R) (F : NormalFunctionalData R)

private theorem form_eq_of_rankOne (E G : PositiveForm (positiveTrace normal F))
    (h : ∀ v, E.expectation (R.rankOne v) = G.expectation (R.rankOne v))
    {x : T} (hx : x ∈ R.positive) : E.expectation x = G.expectation x := by
  obtain ⟨v, hv⟩ := normal.positive_decomposition x hx
  rw [← hv.tsum_eq, E.expectation_tsum hv.summable (fun n => R.rankOne_positive (v n)),
    G.expectation_tsum hv.summable (fun n => R.rankOne_positive (v n))]
  exact tsum_congr (fun n => h (v n))
end Normal

section Photon
variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : Gaussian.RankOneData PhotonFock T} (normal : NormalTraceData R) (F : NormalFunctionalData R)

theorem familyNumber_eq_physical {x : T} (hx : x ∈ R.positive) :
    (familyObservable normal F numberFamily).expectation x =
      (NormalPhoton.numberForm normal F).expectation x :=
  form_eq_of_rankOne normal F _ _ (fun v =>
    (numberObservable_rankOne normal F v).trans (NormalPhoton.numberForm_rankOne normal F v).symm) hx

theorem familyRadiation_eq_physical {x : T} (hx : x ∈ R.positive) :
    (familyObservable normal F radiationFamily).expectation x =
      (NormalPhoton.radiationForm normal F).expectation x :=
  form_eq_of_rankOne normal F _ _ (fun v =>
    (radiationObservable_rankOne normal F v).trans (NormalPhoton.radiationForm_rankOne normal F v).symm) hx
end Photon

section Spatial
variable {X : Type} [MeasurableSpace X] (μ : Measure X) [IsSeparable μ]
  (BT : StandardNormalTraceBackground)

theorem partialTraceFamily_radiation_eq {x : BT.Trace (Lp PhotonFock 2 μ)}
    (hx : x ∈ (BT.realization (Lp PhotonFock 2 μ)).rank.positive) :
    (partialTraceForm BT (spatialCoefficients μ PhotonFock)
      (familyObservable BT.normal (BT.realization PhotonFock).functional radiationFamily)).expectation x =
      (fullForm BT μ (NormalPhoton.radiationForm BT.normal (BT.realization PhotonFock).functional)).expectation x :=
  familyRadiation_eq_physical BT.normal (BT.realization PhotonFock).functional
    (BT.partialTrace_positive (spatialCoefficients μ PhotonFock) hx)

theorem partialTraceFamily_number_eq {x : BT.Trace (Lp PhotonFock 2 μ)}
    (hx : x ∈ (BT.realization (Lp PhotonFock 2 μ)).rank.positive) :
    (partialTraceForm BT (spatialCoefficients μ PhotonFock)
      (familyObservable BT.normal (BT.realization PhotonFock).functional numberFamily)).expectation x =
      (fullForm BT μ (NormalPhoton.numberForm BT.normal (BT.realization PhotonFock).functional)).expectation x :=
  familyNumber_eq_physical BT.normal (BT.realization PhotonFock).functional
    (BT.partialTrace_positive (spatialCoefficients μ PhotonFock) hx)

end Spatial

section Full
variable (BF : StandardSymmetricFockExponential) (CCR : CanonicalSectorCCR photonMeasure)
  (BT : StandardNormalTraceBackground) {h : Type} [NormedAddCommGroup h] [InnerProductSpace ℂ h]
  (e : h ≃ₗᵢ[ℂ] Lp ℂ 2 photonMeasure) (N : ℕ)

theorem fullFormCalculus_radiation_eq {x : BT.FullTrace N}
    (hx : x ∈ (BT.realization (FullHilbert N)).rank.positive) :
    ((fullFormCalculus BF CCR BT e N).observable radiationFamily).expectation x =
      (fullForm BT (volume : Measure (SymmetricLift.Configuration N))
        (NormalPhoton.radiationForm BT.normal (BT.realization PhotonFock).functional)).expectation x :=
  partialTraceFamily_radiation_eq (volume : Measure (SymmetricLift.Configuration N)) BT hx

theorem fullFormCalculus_number_eq {x : BT.FullTrace N}
    (hx : x ∈ (BT.realization (FullHilbert N)).rank.positive) :
    ((fullFormCalculus BF CCR BT e N).observable numberFamily).expectation x =
      (fullForm BT (volume : Measure (SymmetricLift.Configuration N))
        (NormalPhoton.numberForm BT.normal (BT.realization PhotonFock).functional)).expectation x :=
  partialTraceFamily_number_eq (volume : Measure (SymmetricLift.Configuration N)) BT hx

theorem fullFormCalculus_radiation_rankOne (u : FullHilbert N) :
    ((fullFormCalculus BF CCR BT e N).observable radiationFamily).expectation
      ((BT.realization (FullHilbert N)).rank.rankOne u) = ∫⁻ x, radiationForm (u x) :=
  (fullFormCalculus_radiation_eq BF CCR BT e N
    ((BT.realization (FullHilbert N)).rank.rankOne_positive u)).trans
    (fullRadiationForm_rankOne BT volume u)

theorem fullFormCalculus_radiation_graph (u r : FullHilbert N)
    (hgraph : ∀ᵐ x ∂volume, (u x, r x) ∈ radiationRoot.graph) :
    ((fullFormCalculus BF CCR BT e N).observable radiationFamily).expectation
      ((BT.realization (FullHilbert N)).rank.rankOne u) = ENNReal.ofReal (‖r‖ ^ 2) :=
  (fullFormCalculus_radiation_eq BF CCR BT e N
    ((BT.realization (FullHilbert N)).rank.rankOne_positive u)).trans
    (fullRadiationForm_graph BT volume u r hgraph)

theorem fullFormCalculus_radiation_finite_iff (u : FullHilbert N) :
    ((fullFormCalculus BF CCR BT e N).observable radiationFamily).expectation
      ((BT.realization (FullHilbert N)).rank.rankOne u) < ⊤ ↔
        ∃ s : SpatialRadiationGraph (volume : Measure (SymmetricLift.Configuration N)),
          spatialRadiationInclusion volume s = u := by
  have he := congrArg (fun t : ℝ≥0∞ => t < ⊤)
    (fullFormCalculus_radiation_eq BF CCR BT e N
      ((BT.realization (FullHilbert N)).rank.rankOne_positive u))
  exact (Iff.of_eq he).trans (PhysicalSpatialRadiationDomain.fullRadiationForm_finite_iff volume BT u)

end Full
end GptLean.PhysicalFock
