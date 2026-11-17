import GptLean.PhysicalFockWienerSegal
import GptLean.PhysicalPolarizationRealStructure
import GptLean.PhysicalDipoleKernel
import GptLean.PhysicalGaussianGraphSource

/-!
The full photon Gaussian representation for the constant dipole field.
Creation-word density identifies the generated top subspace with the
physical Fock space. The article's real structure fixes each constant
kernel, so the universal WIS theorem gives the actual field multiplication
identities without a physical matching assumption.
-/

noncomputable section

namespace GptLean.PhysicalDipoleGaussian

open MeasureTheory Filter Topology PhysicalFock PhysicalPolarization
  PhysicalGaussianCoordinates PhysicalDivergenceKernel Gaussian
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

abbrev OnePhotonTop := (⊤ : Submodule ℂ (Lp ℂ 2 photonMeasure))
abbrev FockTop := generatedSubspace photonMeasure OnePhotonTop

variable (F : Frame)

/-- The physical conjugation on the full one-photon subspace. -/
def fullRealStructure : RealStructure OnePhotonTop where
  conjugation :=
    { toFun u := ⟨F.conjugation u, Submodule.mem_top⟩
      invFun u := ⟨F.conjugation u, Submodule.mem_top⟩
      map_add' u v := Subtype.ext (map_add F.conjugation (u : Lp ℂ 2 photonMeasure) v)
      map_smul' c u := Subtype.ext (F.conjugation.map_smulₛₗ c (u : Lp ℂ 2 photonMeasure))
      left_inv u := Subtype.ext (F.conjugation_involutive u)
      right_inv u := Subtype.ext (F.conjugation_involutive u)
      norm_map' u := F.conjugation.norm_map u }
  involutive u := Subtype.ext (F.conjugation_involutive u)

variable (BF : StandardSymmetricFockExponential)

include BF in
theorem mem_fockTop (u : PhotonFock) : u ∈ FockTop := by
  have hs : Submodule.span ℂ (Set.range (creationWord photonMeasure)) ≤ FockTop := by
    apply Submodule.span_le.mpr
    rintro v ⟨w, rfl⟩
    exact creationWord_mem_generated photonMeasure OnePhotonTop w (by simp)
  exact (closure_minimal hs (Submodule.isClosed_topologicalClosure _))
    ((photonExponential BF).words_total u)

/-- Inclusion of the generated top subspace is an onto isometry. -/
def fockTopEquiv : FockTop ≃ₗᵢ[ℂ] PhotonFock :=
  LinearIsometryEquiv.ofSurjective FockTop.subtypeₗᵢ
    (fun u => ⟨⟨u, mem_fockTop BF u⟩, rfl⟩)

theorem fockTopEquiv_apply (u : FockTop) : fockTopEquiv BF u = u.val := rfl

theorem fockTopEquiv_symm_val (u : PhotonFock) :
    (fockTopEquiv BF |>.symm u).val = u :=
  (fockTopEquiv BF).apply_symm_apply u

abbrev Realization := ScalarWienerSegal photonMeasure OnePhotonTop (fullRealStructure F)

theorem realization_exists (BW : StandardWienerSegal) : Nonempty (Realization F) :=
  BW.realization PhotonMode photonMeasure OnePhotonTop isClosed_univ (fullRealStructure F)

variable (W : Realization F)

/-- The actual full Fock space represented by scalar Gaussian functions. -/
def fullGaussianUnitary : PhotonFock ≃ₗᵢ[ℂ] Lp ℂ 2 W.space.measure :=
  (fockTopEquiv BF).symm.trans W.unitary

/-- The real one-photon label of the constant field component. -/
def constantLabel (χ : ArticleCutoff) (i : Fin 3) : (fullRealStructure F).fixedSpace :=
  ⟨⟨(formFactors F χ).fourierKernel (i, 0), Submodule.mem_top⟩,
    (RealStructure.mem_fixedSpace _ _).mpr
      (Subtype.ext (F.fourierKernel_fixed χ i 0))⟩

theorem constantKernel_label (χ : ArticleCutoff) (i : Fin 3) :
    (kernel F χ (i, 0)).val.1 =
      ((constantLabel F χ i : OnePhotonTop) : Lp ℂ 2 photonMeasure) :=
  TransformationsKernelCovariance.momentumKernel_fst (formFactors F χ) rfl
    (LinearIsometryEquiv.refl ℝ _) (i, 0)

/-- Each component of the constant field is a real first-chaos function. -/
def coefficient (χ : ArticleCutoff) (i : Fin 3) : Lp ℝ 2 W.space.measure :=
  W.firstChaos (constantLabel F χ i)

theorem fullGaussianUnitary_field (C : CanonicalSectorCCR photonMeasure)
    (χ : ArticleCutoff) (i : Fin 3) (u : RadiationGraphSpace) :
    fullGaussianUnitary F BF W (kernelField C (kernel F χ (i, 0)) u) =ᵐ[W.space.measure]
      fun q => coefficient F W χ i q •
        fullGaussianUnitary F BF W (radiationGraphInclusion u) q := by
  have hg := kernelField_segalGraph C (kernel F χ (i, 0)) u
  rw [constantKernel_label F χ i] at hg
  have h := W.intertwining (constantLabel F χ i)
    ((fockTopEquiv BF).symm (radiationGraphInclusion u))
    ((fockTopEquiv BF).symm (kernelField C (kernel F χ (i, 0)) u))
    (by simpa only [fockTopEquiv_symm_val] using hg)
  exact h

variable {X : Type*} [MeasurableSpace X] (ν : Measure X) [SFinite ν]

local instance fullPhotonDirectInner : InnerProductSpace ℂ PhotonFock :=
  { (inferInstance : InnerProductSpace ℂ PhotonFock) with
    toNormedSpace := (inferInstance : NormedSpace ℂ PhotonFock) }

attribute [local irreducible] fullGaussianUnitary productSource radiationGraphInclusion

set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 1200000 in
/-- Constant field multiplication holds on the actual product source. -/
theorem productSource_field (C : CanonicalSectorCCR photonMeasure)
    (χ : ArticleCutoff) (i : Fin 3) (u : SpatialRadiationGraph ν) :
    productSource (X := X) (Q := W.space.Q) (H := PhotonFock) (K := ℂ)
      ν W.space.measure (fullGaussianUnitary F BF W)
      ((kernelField C (kernel F χ (i, 0))).compLpL 2 ν u) =ᵐ[W.space.measure.prod ν]
      fun qx : W.space.Q × X => (coefficient F W χ i qx.1 : ℂ) •
        productSource (X := X) (Q := W.space.Q) (H := PhotonFock) (K := ℂ)
          ν W.space.measure (fullGaussianUnitary F BF W)
          (spatialRadiationInclusion ν u) qx := by
  exact productSource_graph ν W.space.measure (fullGaussianUnitary F BF W)
    (kernelField C (kernel F χ (i, 0))) radiationGraphInclusion
    (coefficient F W χ i) (Lp.stronglyMeasurable _)
    (fun v => fullGaussianUnitary_field F BF W C χ i v) u

end GptLean.PhysicalDipoleGaussian
