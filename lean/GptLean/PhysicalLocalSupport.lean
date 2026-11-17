import GptLean.PhysicalFockSupportLift
import GptLean.PhysicalFockFiniteOperators
import GptLean.PhysicalFockRadiationCore
import GptLean.PhysicalOnePhotonFourier
import GptLean.PhysicalFreeHilbert
import GptLean.PhysicalFiniteSectorCoordinates
import GptLean.PhotonLocalizationPhysicalCompactness

/-!
The actual photon, electronic and number support subspaces for local
compactness. Number projections preserve the closed creation-word span.
The physical electronic multiplier and the same Fock localization channel
therefore have the required support, before any compactness theorem is used.
-/

noncomputable section
namespace GptLean.PhysicalLocalSupport

open MeasureTheory Filter Topology PhysicalFock PhotonLocalization
  PhotonLocalizationFockChannel SymmetricLift
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 200000
set_option Elab.async false

section ClosedSupport
variable {X H : Type*} [MeasurableSpace X] (μ : Measure X)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem spatialSupport_closed (s : Set X) :
    IsClosed (spatialSupport (K := H) (μ := μ) s : Set (Lp H 2 μ)) := by
  apply isSeqClosed_iff_isClosed.mp
  intro u v hu huv
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp huv).exists_seq_tendsto_ae
  filter_upwards [hae, ae_all_iff.mpr hu] with x hx hs
  intro hxs
  exact tendsto_nhds_unique hx (tendsto_const_nhds.congr fun n => (hs (ns n) hxs).symm)

theorem fibreSupport_closed (W : Submodule ℂ H) (hW : IsClosed (W : Set H)) :
    IsClosed (fibreSupport (μ := μ) W : Set (Lp H 2 μ)) := by
  apply isSeqClosed_iff_isClosed.mp
  intro u v hu huv
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp huv).exists_seq_tendsto_ae
  filter_upwards [hae, ae_all_iff.mpr hu] with x hx hs
  exact hW.mem_of_tendsto hx (Eventually.of_forall fun n => hs (ns n))

end ClosedSupport

section Generated
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]
  (V : Submodule ℂ (Lp ℂ 2 μ))

theorem sector_mem_generated (n : ℕ) (u : Fock μ)
    (hu : u ∈ generatedSubspace μ V) :
    photonSector μ n u ∈ generatedSubspace μ V := by
  let W := (generatedSubspace μ V).comap (photonSector μ n).toLinearMap
  have hspan : Submodule.span ℂ {v | ∃ w : List (Lp ℂ 2 μ),
      (∀ f ∈ w, f ∈ V) ∧ v = creationWord μ w} ≤ W := by
    apply Submodule.span_le.mpr
    rintro v ⟨w, hw, rfl⟩
    change photonSector μ n (creationWord μ w) ∈ generatedSubspace μ V
    rw [photonSector_word]
    split_ifs
    · exact creationWord_mem_generated μ V w hw
    · exact Submodule.zero_mem _
  have hclosed : IsClosed (W : Set (Fock μ)) :=
    (Submodule.isClosed_topologicalClosure _).preimage (photonSector μ n).continuous
  exact (Submodule.topologicalClosure_minimal _ hspan hclosed) hu

theorem cutoff_mem_generated (M : ℕ) (u : Fock μ)
    (hu : u ∈ generatedSubspace μ V) :
    cutoff (Sector μ) M u ∈ generatedSubspace μ V := by
  simp only [cutoff, sum_apply]
  exact Submodule.sum_mem _ fun n _ => sector_mem_generated μ V n u hu

end Generated

/-- Photon support is transported by the same actual Fourier map as the channel. -/
def photonSubspace (r : ℝ) : Submodule ℂ PhotonFock :=
  generatedFockSubspace ((supportedOnePhoton
    (E := PhysicalOnePhotonFourier.Polarization) (μ := volume) r).map
      PhysicalOnePhotonFourier.fourier.toLinearEquiv.toLinearMap)

theorem photonSubspace_closed (r : ℝ) :
    IsClosed (photonSubspace r : Set PhotonFock) :=
  Submodule.isClosed_topologicalClosure _

instance photonSubspaceComplete (r : ℝ) : CompleteSpace (photonSubspace r) :=
  (photonSubspace_closed r).completeSpace_coe

def photonSupport (N : ℕ) (r : ℝ) : Submodule ℂ (PhysicalFreeForm.WaveSpace (Fin N × Fin 3)) :=
  fibreSupport (μ := volume) (photonSubspace r)

def electronicSupport (N L : ℕ) : Submodule ℂ (PhysicalFreeForm.WaveSpace (Fin N × Fin 3)) :=
  spatialSupport (electronicConfigurationRegion ((L : ℝ) + 1))

def numberSupport (N M : ℕ) : Submodule ℂ (PhysicalFreeForm.WaveSpace (Fin N × Fin 3)) :=
  fibreSupport (LinearMap.range (cutoff (Sector photonMeasure) M).toLinearMap)

def localSupport (N : ℕ) (r : ℝ) (L M : ℕ) :
    Submodule ℂ (PhysicalFreeForm.WaveSpace (Fin N × Fin 3)) :=
  photonSupport N r ⊓ electronicSupport N L ⊓ numberSupport N M

theorem photonSupport_closed (N : ℕ) (r : ℝ) :
    IsClosed (photonSupport N r : Set (PhysicalFreeForm.WaveSpace (Fin N × Fin 3))) :=
  fibreSupport_closed volume _ (photonSubspace_closed r)

theorem electronicSupport_closed (N L : ℕ) :
    IsClosed (electronicSupport N L : Set (PhysicalFreeForm.WaveSpace (Fin N × Fin 3))) :=
  spatialSupport_closed volume _

theorem numberSupport_closed (N M : ℕ) :
    IsClosed (numberSupport N M : Set (PhysicalFreeForm.WaveSpace (Fin N × Fin 3))) := by
  apply fibreSupport_closed volume
  exact ContinuousLinearMap.IsIdempotentElem.isClosed_range
    (numberSectorCutoff_projection (photonSector photonMeasure)
      (photonSector_isStarProjection photonMeasure)
      (photonSector_orthogonal photonMeasure) M).isIdempotentElem

theorem localSupport_closed (N : ℕ) (r : ℝ) (L M : ℕ) :
    IsClosed (localSupport N r L M : Set (PhysicalFreeForm.WaveSpace (Fin N × Fin 3))) :=
  ((photonSupport_closed N r).inter (electronicSupport_closed N L)).inter
    (numberSupport_closed N M)

theorem number_preserves_photon (N : ℕ) (r : ℝ) (M : ℕ)
    (u : PhysicalFreeForm.WaveSpace (Fin N × Fin 3)) (hu : u ∈ photonSupport N r) :
    (cutoff (Sector photonMeasure) M).compLpL 2 volume u ∈ photonSupport N r :=
  compLpL_mem_fibreSupport _ _ (fun v hv => cutoff_mem_generated photonMeasure _ M v hv) u hu

theorem electronic_mem (N L : ℕ) (u : PhysicalFreeForm.WaveSpace (Fin N × Fin 3)) :
    (physicalElectronicFamily L).operator u ∈ electronicSupport N L :=
  (physicalElectronicFamily L).mem_spatialSupport _
    (physicalElectronicCutoff_support (by positivity)) u

/-- The two physical cutoffs land in the closed local support intersection. -/
theorem cut_mem (N : ℕ) (r : ℝ) (L M : ℕ)
    (u : PhysicalFreeForm.WaveSpace (Fin N × Fin 3)) (hu : u ∈ photonSupport N r) :
    (physicalElectronicFamily L).operator
      ((cutoff (Sector photonMeasure) M).compLpL 2 volume u) ∈ localSupport N r L M := by
  refine ⟨⟨?_, electronic_mem N L _⟩, ?_⟩
  · exact (physicalElectronicFamily L).mem_fibreSupport _ _ (number_preserves_photon N r M u hu)
  · exact (physicalElectronicFamily L).mem_fibreSupport _ _ (compLpL_mem_range _ u)

/-- The actual channel has precisely the photon support used by the local graph. -/
theorem kraus_mem_photonSupport (BF : StandardSymmetricFockExponential)
    (N m : ℕ) (u : PhysicalFreeForm.WaveSpace (Fin N × Fin 3)) (a : ℕ) :
    (fullFactorization BF PhysicalOnePhotonFourier.fourier N).factor
      (PhotonLocalizationKernelCutoffs.complexOnePhotonIsometry
        (PhotonLocalizationKernelCutoffs.radius m)) u a ∈
        photonSupport N (PhotonLocalizationKernelCutoffs.radius m) := by
  have h := kraus_mem_supported (fullFactorization BF PhysicalOnePhotonFourier.fourier N)
    (fullFockSubspaces BF PhysicalOnePhotonFourier.fourier N) m u a
  exact (mem_spatialSubspace volume (photonSubspace _) _).mp h

/-- Range support implies the canonical finite-sector coordinate predicate. -/
theorem numberSupport_le_finite (N M : ℕ) :
    numberSupport N M ≤ PhysicalFiniteSectorCoordinates.numberSubspace
      (Sector photonMeasure) (volume : Measure (Configuration N)) M := by
  intro u hu n hn
  apply Lp.ext
  filter_upwards [hu, PhysicalFiniteSectorCoordinates.coordinate_ae
    (Sector photonMeasure) volume n u, Lp.coeFn_zero (Sector photonMeasure n) 2 volume]
    with x hx hc hz
  obtain ⟨v, hv⟩ := hx
  exact hc.trans ((congrArg (fun w : PhotonFock => w n) hv.symm).trans
    ((cutoff_coordinate_zero M n hn v).trans hz.symm))

end GptLean.PhysicalLocalSupport
