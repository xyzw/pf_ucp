import PfHk.PhysicalUCPBackgrounds
import PfHk.PhysicalOpenUniformCarleman
import PfHk.ScalarSobolevFromWeak
import PfHk.PhysicalUniqueContinuationFlat
import PfHk.NonvanishingDensity
import GptLean.PhysicalFockSeparable

/-! Public physical unique-continuation and density consequences.

The imported background record lists exactly the ordinary inputs of the
proved uniform physical Carleman theorem. It contains no Carleman estimate,
negative-form estimate, scalar recurrence Sobolev bound, or UCP assertion.
Those inputs are derived internally, with alpha fixed to one half.
-/

noncomputable section
namespace PfHk.PhysicalOpenUCPConsequences

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.Representability GptLean.SymmetricLift
  PfHk.CenteredPhysicalReference PfHk.PhysicalFieldRegularity PfHk.PhysicalLocalEnergy
  PfHk.PhysicalOperatorDomain PfHk.PhysicalCarlemanInput PfHk.PhysicalCutoffCommutator
  PfHk.PhysicalExternalOperator PfHk.KatoRellichBackground PfHk.FriedrichsDivergenceBackground
  PfHk.WeylGraphC1Calculus PfHk.PolarCalculus PfHk.SphereCoreGeometry
  PfHk.OrdinaryPolarSobolevChart PfHk.UniqueContinuationDensity
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 40000

local instance endpointConsequencesPhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  PfHk.PhysicalDyadicEnergy.dyadicEnergyPhotonRealInner

attribute [local irreducible] inclusion PhysicalPFReference.covariant radiation roughMultiply externalCovariant
  PhysicalPFReference.referenceSubspace FreeGraph IsOperatorPair IsLocalOperatorPair IsExternalWeakEigenstate

variable {N : ℕ} {F : Frame} {χ : ArticleCutoff} {C : CanonicalSectorCCR photonMeasure} {e : ℝ}

private theorem dimension_gt_two (hN : 0 < N) : 2 < Fintype.card (Fin N × Fin 3) := by
  simp only [Fintype.card_prod, Fintype.card_fin]
  omega

private theorem physical_nonempty (hN : 0 < N) : Nonempty (Fin N × Fin 3) :=
  ⟨(⟨0, hN⟩, 0)⟩

variable (B : PhysicalUCPConsequences.Backgrounds (N := N) F χ C e)
  {U : Set (Configuration N)} (a : PhysicalOpenUCPCoefficients.Data N U)
  (hN : 0 < N) (hU : IsOpen U) (hconnected : IsPreconnected U)
  (hfull : ∀ᵐ X : Configuration N ∂volume, X ∈ U)

include B hN hU hconnected hfull

/-- One infinite-order zero of an actual weak eigenstate forces global
almost-everywhere vanishing. All analytic continuation inputs are derived. -/
theorem zero_of_infinite_order {E : ℝ}
    {u : Reference (Fin N × Fin 3) (fun _ => 0)}
    {hu : ExternalDomain (fun _ => 0) a.vector a.positive a.negative u}
    (heigen : IsExternalWeakEigenstate (fun _ => 0) C (profile (N := N) F χ 0)
      (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0)
      e a.vector a.positive a.negative E u hu)
    {X₀ : Configuration N} (hX₀ : X₀ ∈ U)
    (hflat : InfiniteOrder.FlatAtZero
      (localMass (μ := volume) (inclusion (Fin N × Fin 3) (fun _ => 0) u) X₀)) :
    ∀ᵐ X ∂volume, inclusion (Fin N × Fin 3) (fun _ => 0) u X = 0 := by
  let : Nonempty (Fin N × Fin 3) := physical_nonempty hN
  let C₀ := Classical.choose a.negative_quarter_form
  have hnegative := (Classical.choose_spec a.negative_quarter_form).2
  exact PhysicalCarlemanInput.zero_of_infinite_order (fun _ => 0) C (profile F χ 0)
    (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0)
    e a.vector a.positive a.negative (PhysicalOpenUCP.from_backgrounds F χ C e a B hN hU E)
    (by norm_num : (0 : ℝ) < 1 / 2) hconnected hfull heigen C₀ hnegative hX₀ hflat

/-- A positive-measure zero set of an actual weak eigenstate forces global
almost-everywhere vanishing. The scalar Sobolev estimate is proved internally. -/
theorem zero_of_positive_zero_measure {E : ℝ}
    {u : Reference (Fin N × Fin 3) (fun _ => 0)}
    {hu : ExternalDomain (fun _ => 0) a.vector a.positive a.negative u}
    (heigen : IsExternalWeakEigenstate (fun _ => 0) C (profile (N := N) F χ 0)
      (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0)
      e a.vector a.positive a.negative E u hu)
    (hpositive : 0 < volume {X | inclusion (Fin N × Fin 3) (fun _ => 0) u X = 0}) :
    ∀ᵐ X ∂volume, inclusion (Fin N × Fin 3) (fun _ => 0) u X = 0 := by
  let : Nonempty (Fin N × Fin 3) := physical_nonempty hN
  let C₀ := Classical.choose a.negative_quarter_form
  have hnegative := (Classical.choose_spec a.negative_quarter_form).2
  have hex := ScalarSobolevFromWeak.exists_scalarSobolevBound (dimension_gt_two hN)
  let p := Classical.choose hex
  have hp := Classical.choose_spec hex
  let q := Classical.choose hp
  have hq := Classical.choose_spec hp
  let S := Classical.choose hq
  have hS := Classical.choose_spec hq
  exact PhysicalCarlemanInput.zero_of_positive_zero_measure (fun _ => 0) C (profile F χ 0)
    (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0)
    e a.vector a.positive a.negative (PhysicalOpenUCP.from_backgrounds F χ C e a B hN hU E)
    (by norm_num : (0 : ℝ) < 1 / 2) hconnected hfull heigen C₀ hnegative
    (p := p) (q := q) (S := S) hS.1 hS.2.1 hS.2.2.1 hS.2.2.2 hpositive

/-- A nonzero actual weak eigenstate has a null configuration-space zero set. -/
theorem ae_nonzero {E : ℝ}
    {u : Reference (Fin N × Fin 3) (fun _ => 0)}
    {hu : ExternalDomain (fun _ => 0) a.vector a.positive a.negative u}
    (heigen : IsExternalWeakEigenstate (fun _ => 0) C (profile (N := N) F χ 0)
      (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0)
      e a.vector a.positive a.negative E u hu) (hu_ne : u ≠ 0) :
    ∀ᵐ X ∂volume, inclusion (Fin N × Fin 3) (fun _ => 0) u X ≠ 0 := by
  rw [ae_iff]
  simp only [not_not]
  by_contra hzero
  have hz := zero_of_positive_zero_measure B a hN hU hconnected hfull heigen
    (bot_lt_iff_ne_bot.mpr hzero)
  have hψ : inclusion (Fin N × Fin 3) (fun _ => 0) u = 0 := Lp.eq_zero_iff_ae_eq_zero.mpr hz
  exact hu_ne (inclusion_injective (Fin N × Fin 3) (fun _ => 0)
    (hψ.trans ((map_zero (inclusion (Fin N × Fin 3) (fun _ => 0))).symm)))

theorem ae_norm_pos {E : ℝ}
    {u : Reference (Fin N × Fin 3) (fun _ => 0)}
    {hu : ExternalDomain (fun _ => 0) a.vector a.positive a.negative u}
    (heigen : IsExternalWeakEigenstate (fun _ => 0) C (profile (N := N) F χ 0)
      (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0)
      e a.vector a.positive a.negative E u hu) (hu_ne : u ≠ 0) :
    ∀ᵐ X ∂volume, 0 < ‖inclusion (Fin N × Fin 3) (fun _ => 0) u X‖ :=
  (ae_nonzero B a hN hU hconnected hfull heigen hu_ne).mono fun _ hx => norm_pos_iff.mpr hx

/-- Positivity of the actual electronic L1 density, derived by the checked
configuration-space nonvanishing and the actual Fubini marginal construction. -/
theorem electronic_density_pos {E : ℝ}
    {u : Reference (Fin N × Fin 3) (fun _ => 0)}
    {hu : ExternalDomain (fun _ => 0) a.vector a.positive a.negative u}
    (heigen : IsExternalWeakEigenstate (fun _ => 0) C (profile (N := N) F χ 0)
      (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0)
      e a.vector a.positive a.negative E u hu) (hu_ne : u ≠ 0) :
    ∀ᵐ x ∂volume, 0 < PhysicalElectronicDensity.density
      (inclusion (Fin N × Fin 3) (fun _ => 0) u) x :=
  NonvanishingDensity.density_pos_ae ⟨0, hN⟩ (inclusion (Fin N × Fin 3) (fun _ => 0) u)
    (ae_nonzero B a hN hU hconnected hfull heigen hu_ne)

set_option maxHeartbeats 200000 in
/-- Positivity in the constructed density-current pair. The current
arguments are arbitrary and do not enter the density conclusion. -/
theorem pair_density_pos (i : Fin N) {E : ℝ}
    {u : Reference (Fin N × Fin 3) (fun _ => 0)}
    {hu : ExternalDomain (fun _ => 0) a.vector a.positive a.negative u}
    (heigen : IsExternalWeakEigenstate (fun _ => 0) C (profile (N := N) F χ 0)
      (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0)
      e a.vector a.positive a.negative E u hu) (hu_ne : u ≠ 0)
    (d : Fin 3 → WaveSpace (Fin N × Fin 3)) :
    ∀ᵐ x ∂volume, 0 < PhysicalPairSpace.densityL1
      (PhysicalSourcePair.ofWaveFunction i
        (ElectronicH1Complex.realEquiv (E := PhotonFock) (I := Fin N × Fin 3)
          (electronic (Fin N × Fin 3) (fun _ => 0) u)) d) x := by
  have hvalue : ElectronicH1Space.value
      (ElectronicH1Complex.realEquiv (E := PhotonFock) (I := Fin N × Fin 3)
        (electronic (Fin N × Fin 3) (fun _ => 0) u)) =
      inclusion (Fin N × Fin 3) (fun _ => 0) u := by
    unfold inclusion
    rfl
  apply NonvanishingDensity.pair_density_pos_ae i
    (ElectronicH1Complex.realEquiv (E := PhotonFock) (I := Fin N × Fin 3)
      (electronic (Fin N × Fin 3) (fun _ => 0) u)) d
  exact (congrArg (fun ψ : WaveSpace (Fin N × Fin 3) =>
    ∀ᵐ X ∂volume, ψ X ≠ 0) hvalue).mpr
    (ae_nonzero B a hN hU hconnected hfull heigen hu_ne)

end PfHk.PhysicalOpenUCPConsequences
