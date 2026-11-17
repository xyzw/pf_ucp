import GptLean.PhysicalSectorPositionInsertion
import GptLean.PhysicalLocalSupport
import GptLean.PhysicalInvariantProjection

/-!
Actual photon position support through bosonic symmetrization. Position
support is a closed subspace pulled back by the concrete inverse Fourier
coordinates. Particle permutations preserve this subspace, so the Hilbert
projection onto symmetric sectors preserves it as well.
-/

noncomputable section
namespace GptLean.PhysicalFockPositionSupport

open MeasureTheory Filter Topology PhysicalFock PhysicalSectorCoordinates
  PhotonLocalization SymmetricLift
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 200000
set_option Elab.async false

section Permutations
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]

theorem permutation_symm_apply (n : ℕ) (π : Equiv.Perm (Fin n)) (u : FullSector μ n) :
    permutation μ n π.symm (permutation μ n π u) = u := by
  apply Lp.ext
  filter_upwards [permutation_ae μ n π.symm (permutation μ n π u),
    (measurePreserving_piCongrLeft (fun _ : Fin n => μ) π.symm).quasiMeasurePreserving.ae
      (permutation_ae μ n π u)] with k h₁ h₂
  refine h₁.trans (h₂.trans ?_)
  apply congrArg (fun t : Fin n → Ω => u t)
  funext i
  have ho : (MeasurableEquiv.piCongrLeft (fun _ : Fin n => Ω) π)
      ((MeasurableEquiv.piCongrLeft (fun _ : Fin n => Ω) π.symm) k) i =
      (MeasurableEquiv.piCongrLeft (fun _ : Fin n => Ω) π.symm) k (π.symm i) := by
    simpa only [Equiv.apply_symm_apply] using
      MeasurableEquiv.piCongrLeft_apply_apply π (β := fun _ : Fin n => Ω)
        ((MeasurableEquiv.piCongrLeft (fun _ : Fin n => Ω) π.symm) k) (π.symm i)
  exact ho.trans (MeasurableEquiv.piCongrLeft_apply_apply π.symm
    (β := fun _ : Fin n => Ω) k i)

def permutationEquiv (n : ℕ) (π : Equiv.Perm (Fin n)) :
    FullSector μ n ≃ₗᵢ[ℂ] FullSector μ n where
  toFun := permutation μ n π
  invFun := permutation μ n π.symm
  map_add' := (permutation μ n π).map_add
  map_smul' := (permutation μ n π).map_smul
  left_inv := permutation_symm_apply μ n π
  right_inv := by
    intro u
    simpa only [Equiv.symm_symm] using permutation_symm_apply μ n π.symm u
  norm_map' := (permutation μ n π).norm_map

/-- Any closed subspace preserved by the actual particle permutations is
preserved by the actual bosonic projection. -/
theorem symmetrizer_mem (n : ℕ) (W : Submodule ℂ (FullSector μ n))
    (hW : IsClosed (W : Set (FullSector μ n)))
    (hperm : ∀ π u, u ∈ W → permutation μ n π u ∈ W)
    {u : FullSector μ n} (hu : u ∈ W) : symmetrizer μ n u ∈ W := by
  let : CompleteSpace W := hW.completeSpace_coe
  exact PhysicalInvariantProjection.fixed_projection_mem (symmetricSubspace μ n) W
    (permutationEquiv μ n) (fun _ => Iff.rfl) hperm
    (fun π v hv => hperm π.symm v hv) hu

end Permutations

def fullSupport (n : ℕ) (r : ℝ) : Submodule ℂ (FullSector photonMeasure n) :=
  (spatialSupport (electronicConfigurationRegion (N := n) r)).comap
    (fullPosition n).toLinearMap

theorem fullSupport_closed (n : ℕ) (r : ℝ) :
    IsClosed (fullSupport n r : Set (FullSector photonMeasure n)) :=
  (PhysicalLocalSupport.spatialSupport_closed volume _).preimage (fullPosition n).continuous

theorem configurationRegion_permutation (n : ℕ) (r : ℝ)
    (π : Equiv.Perm (Fin n)) (x : Configuration n) :
    permuteConfiguration π x ∈ electronicConfigurationRegion r ↔
      x ∈ electronicConfigurationRegion r := by
  constructor
  · intro h i
    have hi := h (π i)
    change ‖particle x (π.symm (π i))‖ ≤ 2 * r at hi
    simpa only [Equiv.symm_apply_apply] using hi
  · intro h i
    exact h (π.symm i)

theorem permutation_mem_fullSupport (n : ℕ) (r : ℝ)
    (π : Equiv.Perm (Fin n)) (u : FullSector photonMeasure n) (hu : u ∈ fullSupport n r) :
    permutation photonMeasure n π u ∈ fullSupport n r := by
  apply (fullPosition_supported_iff n _ _).mpr
  have h := (fullPosition_supported_iff n u _).mp hu
  intro p
  rw [positionComponent_permutation]
  filter_upwards [Lp.coeFn_compMeasurePreserving
    (positionComponent n u (fun j => p (π.symm j)))
    (permuteConfiguration π).measurePreserving,
    (permuteConfiguration π).measurePreserving.quasiMeasurePreserving.ae
      (h (fun j => p (π.symm j)))] with x hx hs
  intro hout
  exact hx.trans (hs ((configurationRegion_permutation n r π x).not.mpr hout))

theorem symmetrizer_mem_fullSupport (n : ℕ) (r : ℝ)
    (u : FullSector photonMeasure n) (hu : u ∈ fullSupport n r) :
    symmetrizer photonMeasure n u ∈ fullSupport n r :=
  symmetrizer_mem photonMeasure n (fullSupport n r) (fullSupport_closed n r)
    (permutation_mem_fullSupport n r) hu

theorem vacuum_mem_fullSupport (r : ℝ) (u : FullSector photonMeasure 0) :
    u ∈ fullSupport 0 r := by
  apply ae_of_all
  intro x hx
  exact False.elim (hx (fun i => Fin.elim0 i))

/-- The actual head insertion preserves the product position support. -/
theorem tensorInsertion_mem_fullSupport (n : ℕ) (r : ℝ)
    (f : Lp ℂ 2 photonMeasure)
    (hf : PhysicalOnePhotonFourier.fourier.symm f ∈
      PhotonLocalizationFockChannel.supportedOnePhoton r)
    (u : FullSector photonMeasure n) (hu : u ∈ fullSupport n r) :
    tensorInsertion photonMeasure n f u ∈ fullSupport (n + 1) r := by
  apply (fullPosition_supported_iff (n + 1) _ _).mpr
  intro p
  have hs := PhysicalSectorHeadCoordinates.split_measurePreserving n
  have hhead := hs.quasiMeasurePreserving.ae
    ((Measure.quasiMeasurePreserving_fst
      (ν := (volume : Measure (Configuration n)))).ae hf)
  have htail := hs.quasiMeasurePreserving.ae
    ((Measure.quasiMeasurePreserving_snd
      (μ := (volume : Measure Gaussian.FieldSpace))).ae hu)
  filter_upwards [positionComponent_tensorInsertion_ae n f u p, hhead, htail]
    with x hx hh ht
  intro hout
  by_cases hheadbound : ‖(PhysicalSectorHeadCoordinates.split n x).fst‖ ≤ 2 * r
  · have htailout : (PhysicalSectorHeadCoordinates.split n x).snd ∉
        electronicConfigurationRegion (N := n) r := by
      intro hin
      apply hout
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hheadbound
      · exact hin j
    have hz : fullPosition n u (PhysicalSectorHeadCoordinates.split n x).snd
        (fun j => p j.succ) = 0 :=
      (congrArg (fun c : Coefficient n => c (fun j => p j.succ)) (ht htailout)).trans
        (Measure.ae_count_iff.mp (Lp.coeFn_zero ℂ 2
          (Measure.count : Measure (PhysicalSectorMeasures.Polarization n))) _)
    exact hx.trans (by rw [hz, mul_zero])
  · have hz : PhysicalOnePhotonFourier.fourier.symm f
        (PhysicalSectorHeadCoordinates.split n x).fst (p 0) = 0 :=
      (congrArg (fun c : PhysicalOnePhotonFourier.Polarization => c (p 0))
        (hh (le_of_lt (lt_of_not_ge hheadbound)))).trans
          (Measure.ae_count_iff.mp (Lp.coeFn_zero ℂ 2
            (Measure.count : Measure (Fin 2))) _)
    exact hx.trans (by rw [hz, zero_mul])

theorem creationSector_mem_fullSupport (n : ℕ) (r : ℝ)
    (f : Lp ℂ 2 photonMeasure)
    (hf : PhysicalOnePhotonFourier.fourier.symm f ∈
      PhotonLocalizationFockChannel.supportedOnePhoton r)
    (u : Sector photonMeasure n) (hu : u.val ∈ fullSupport n r) :
    (creationSector photonMeasure n f u).val ∈ fullSupport (n + 1) r := by
  change (Real.sqrt (n + 1 : ℝ) : ℂ) •
    symmetrizer photonMeasure (n + 1) (tensorInsertion photonMeasure n f u.val) ∈ _
  exact Submodule.smul_mem _ _ (symmetrizer_mem_fullSupport (n + 1) r _
    (tensorInsertion_mem_fullSupport n r f hf u.val hu))

theorem creationWordSector_mem_fullSupport (r : ℝ)
    (w : List (Lp ℂ 2 photonMeasure))
    (hw : ∀ f ∈ w, PhysicalOnePhotonFourier.fourier.symm f ∈
      PhotonLocalizationFockChannel.supportedOnePhoton r) :
    (creationWordSector photonMeasure w).val ∈ fullSupport w.length r := by
  induction w with
  | nil => exact vacuum_mem_fullSupport r _
  | cons f w ih =>
    exact creationSector_mem_fullSupport w.length r f (hw f (List.mem_cons_self ..))
      (creationWordSector photonMeasure w) (ih (fun g hg => hw g (List.mem_cons_of_mem f hg)))

def sectorValue (n : ℕ) : PhotonFock →L[ℂ] FullSector photonMeasure n :=
  (sectorInclusion photonMeasure n).toContinuousLinearMap.comp
    (lp.evalCLM ℂ (Sector photonMeasure) 2 n)

def fockSupport (r : ℝ) : Submodule ℂ PhotonFock :=
  ⨅ n : ℕ, (fullSupport n r).comap (sectorValue n).toLinearMap

theorem fockSupport_closed (r : ℝ) : IsClosed (fockSupport r : Set PhotonFock) := by
  rw [fockSupport, Submodule.coe_iInf]
  exact isClosed_iInter fun n => (fullSupport_closed n r).preimage (sectorValue n).continuous

theorem creationWord_mem_fockSupport (r : ℝ) (w : List (Lp ℂ 2 photonMeasure))
    (hw : ∀ f ∈ w, PhysicalOnePhotonFourier.fourier.symm f ∈
      PhotonLocalizationFockChannel.supportedOnePhoton r) :
    creationWord photonMeasure w ∈ fockSupport r := by
  apply (Submodule.mem_iInf _).mpr
  intro n
  change sectorValue n (creationWord photonMeasure w) ∈ fullSupport n r
  by_cases hn : n = w.length
  · subst n
    change ((lp.single (E := Sector photonMeasure) 2 w.length
      (creationWordSector photonMeasure w)) w.length).val ∈ fullSupport w.length r
    rw [lp.single_apply_self]
    exact creationWordSector_mem_fullSupport r w hw
  · change ((lp.single (E := Sector photonMeasure) 2 w.length
      (creationWordSector photonMeasure w)) n).val ∈ fullSupport n r
    rw [lp.single_apply_ne _ _ _ hn]
    exact Submodule.zero_mem _

/-- Generated photon support implies support of every actual inverse-Fourier sector. -/
theorem photonSubspace_le_fockSupport (r : ℝ) :
    PhysicalLocalSupport.photonSubspace r ≤ fockSupport r := by
  apply Submodule.topologicalClosure_minimal _ _ (fockSupport_closed r)
  apply Submodule.span_le.mpr
  rintro v ⟨w, hw, rfl⟩
  apply creationWord_mem_fockSupport r w
  intro f hf
  obtain ⟨g, hg, hgf⟩ := hw f hf
  have he : PhysicalOnePhotonFourier.fourier.symm f = g :=
    (congrArg PhysicalOnePhotonFourier.fourier.symm hgf).symm.trans
      (PhysicalOnePhotonFourier.fourier.symm_apply_apply g)
  exact he.symm ▸ hg

theorem sectorPosition_supported (r : ℝ) (u : PhotonFock)
    (hu : u ∈ PhysicalLocalSupport.photonSubspace r) (n : ℕ) :
    ∀ᵐ x ∂volume, x ∉ electronicConfigurationRegion (N := n) r →
      sectorPosition n (u n) x = 0 :=
  (Submodule.mem_iInf _).mp (photonSubspace_le_fockSupport r hu) n

end GptLean.PhysicalFockPositionSupport
