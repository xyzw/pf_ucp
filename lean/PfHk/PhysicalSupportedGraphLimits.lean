import PfHk.PhysicalOperatorDomain
import PfHk.PhysicalCoreSpatialIntegrability
import PfHk.CompactWeightMultipliers

/-! Support of the covariant derivative, radiation coordinate, and
operator source follows from supported core approximation and graph
convergence. No derivative-support premise is added to the operator vector. -/

noncomputable section
namespace PfHk.PhysicalOperatorDomain

open MeasureTheory Set GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.Representability GptLean.SymmetricLift PfHk.PhysicalFieldRegularity
  PfHk.CenteredPhysicalReference PfHk.PhysicalPolarDensity

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000

local instance supportedGraphPhotonDirectInner : InnerProductSpace ℂ PhotonFock :=
  { (inferInstance : InnerProductSpace ℂ PhotonFock) with
    toNormedSpace := (inferInstance : NormedSpace ℂ PhotonFock) }

attribute [local irreducible] PhysicalPFReference.covariant PhysicalPFReference.inclusion
  PhysicalPFReference.radiation PhysicalPFReference.referenceSubspace SmoothCore.reference
  FreeGraph

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (O : Configuration N)
  (C : CanonicalSectorCCR photonMeasure) (e : ℝ)

private theorem source_supported {s : Set (Configuration N)} {f : WaveSpace (Fin N × Fin 3)}
    (hf : CompactSource s f) : ∀ᵐ X ∂volume, X ∉ s → f X = 0 := by
  filter_upwards [hf.agrees] with X hX hs
  exact hX.trans (image_eq_zero_of_notMem_tsupport (fun h => hs (hf.support h)))

/-- A physical operator vector supported in a compact subset of an open
region has every form coordinate and its operator source supported there. -/
theorem centered_freeGraph_supported
    (hcore : AnnularCoreApproximation C (profile F χ O) (profile_measurable F χ O)
      (profileBound F χ) (profile_bound F χ O) e)
    {u : Reference (Fin N × Fin 3) (fun _ => 0)} {f : WaveSpace (Fin N × Fin 3)}
    {K s : Set (Configuration N)}
    (hu : FreeGraph C (profile F χ O) (profile_measurable F χ O)
      (profileBound F χ) (profile_bound F χ O) e u f)
    (hK : IsCompact K) (hs : IsOpen s) (hKs : K ⊆ s)
    (hsupp : ∀ᵐ X ∂volume, X ∉ K → inclusion (Fin N × Fin 3) (fun _ => 0) u X = 0) :
    (∀ j, ∀ᵐ X ∂volume, X ∉ s →
      covariant (Fin N × Fin 3) (fun _ => 0) C (profile F χ O) (profile_measurable F χ O)
        (profileBound F χ) (profile_bound F χ O) e j u X = 0) ∧
      (∀ᵐ X ∂volume, X ∉ s → PhysicalPFReference.radiation (Fin N × Fin 3) (fun _ => 0) u X = 0) ∧
      (∀ᵐ X ∂volume, X ∉ s → f X = 0) := by
  let a := hcore.approximants C (profile F χ O) (profile_measurable F χ O)
    (profileBound F χ) (profile_bound F χ O) e hu hK hs hKs hsupp
  let g := hcore.sources C (profile F χ O) (profile_measurable F χ O)
    (profileBound F χ) (profile_bound F χ O) e hu hK hs hKs hsupp
  have hg := hcore.properties C (profile F χ O) (profile_measurable F χ O)
    (profileBound F χ) (profile_bound F χ O) e hu hK hs hKs hsupp
  exact ⟨fun j => CompactWeightMultipliers.supported_limit s hs.measurableSet
        (fun n => core_covariant_supported (a n) F χ e O C j)
        ((freeGraph_form_convergence C (profile F χ O) (profile_measurable F χ O)
          (profileBound F χ) (profile_bound F χ O) e hg.1 hu hg.2.2.1 hg.2.2.2).1 j),
      CompactWeightMultipliers.supported_limit s hs.measurableSet
        (fun n => core_radiation_supported (a n))
        (freeGraph_form_convergence C (profile F χ O) (profile_measurable F χ O)
          (profileBound F χ) (profile_bound F χ O) e hg.1 hu hg.2.2.1 hg.2.2.2).2,
      CompactWeightMultipliers.supported_limit s hs.measurableSet
        (fun n => source_supported (hg.2.1 n).some) hg.2.2.2⟩

end PfHk.PhysicalOperatorDomain
