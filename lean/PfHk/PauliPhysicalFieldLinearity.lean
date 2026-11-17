import PfHk.PauliPhysicalFieldCommutation

/-! Real linearity of the physical field multipliers, including their
actual L2 representatives and the charge in the covariant derivative. -/

noncomputable section
namespace PfHk.PauliPhysicalFieldLinearity

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.SymmetricLift GptLean.Representability
  PfHk.PauliPhysicalFieldCommutation
open scoped InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
attribute [local instance]
  PfHk.PhysicalFormProductRules.instInnerProductSpaceRealSubtypePreLpNatSectorPhotonModePhotonMeasureMemAddSubgroupPhotonFock_pfHk
  PfHk.PauliMagneticWeakCore.weakCoreRadiationComplex
  PfHk.PauliMagneticWeakCore.weakCoreRadiationReal
  PfHk.PauliMagneticWeakPairing.referenceComplex
attribute [local irreducible] radiationRoot weightedKernelSubspace
  referenceSubspace inclusion ordinary radiationSource kernelField

variable (C : CanonicalSectorCCR photonMeasure)

theorem kernel_real_smul (c : ℝ) (k : WeightedPhotonKernel) (q : RadiationGraphSpace) :
    kernelField C (c • k) q = (c : ℂ) • kernelField C k q := by
  have h := congrArg (fun L : RadiationGraphSpace →L[ℂ] PhotonFock => L q)
    ((kernelFieldMap C).map_smul c k)
  change kernelField C (c • k) q = c • kernelField C k q at h
  exact h.trans (RCLike.real_smul_eq_coe_smul (K := ℂ) c (kernelField C k q))

theorem kernel_sub_eq_smul (k l m : WeightedPhotonKernel) (c : ℝ)
    (h : k - l = c • m) (q : RadiationGraphSpace) :
    kernelField C k q - kernelField C l q = (c : ℂ) • kernelField C m q := by
  have hs := congrArg (fun L : RadiationGraphSpace →L[ℂ] PhotonFock => L q)
    ((kernelFieldMap C).map_sub k l)
  change kernelField C (k - l) q = kernelField C k q - kernelField C l q at hs
  exact hs.symm.trans ((congrArg (fun a : WeightedPhotonKernel => kernelField C a q) h).trans
    (kernel_real_smul C c m q))

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem spatial_real_smul
    (κ η : X → WeightedPhotonKernel) (hκ : AEStronglyMeasurable κ μ)
    (hη : AEStronglyMeasurable η μ) (M L c : ℝ)
    (hM : ∀ᵐ x ∂μ, ‖κ x‖ ≤ M) (hL : ∀ᵐ x ∂μ, ‖η x‖ ≤ L)
    (hηκ : ∀ᵐ x ∂μ, η x = c • κ x) (q : SpatialRadiationGraph μ) :
    spatialField μ C η hη L hL q = (c : ℂ) • spatialField μ C κ hκ M hM q := by
  apply Lp.ext
  filter_upwards [spatialField_ae μ C η hη L hL q,
    spatialField_ae μ C κ hκ M hM q,
    Lp.coeFn_smul (c : ℂ) (spatialField μ C κ hκ M hM q), hηκ] with x hηx hκx hs hx
  exact hηx.trans ((congrArg (fun k : WeightedPhotonKernel => kernelField C k (q x)) hx).trans
    ((kernel_real_smul C c (κ x) (q x)).trans
      ((congrArg (fun z : PhotonFock => (c : ℂ) • z) hκx.symm).trans hs.symm)))

theorem spatial_sub_eq_smul
    (κ η ξ : X → WeightedPhotonKernel) (hκ : AEStronglyMeasurable κ μ)
    (hη : AEStronglyMeasurable η μ) (hξ : AEStronglyMeasurable ξ μ)
    (M L R c : ℝ) (hM : ∀ᵐ x ∂μ, ‖κ x‖ ≤ M)
    (hL : ∀ᵐ x ∂μ, ‖η x‖ ≤ L) (hR : ∀ᵐ x ∂μ, ‖ξ x‖ ≤ R)
    (hκξη : ∀ᵐ x ∂μ, κ x - η x = c • ξ x) (q : SpatialRadiationGraph μ) :
    spatialField μ C κ hκ M hM q - spatialField μ C η hη L hL q =
      (c : ℂ) • spatialField μ C ξ hξ R hR q := by
  apply Lp.ext
  filter_upwards [spatialField_ae μ C κ hκ M hM q,
    spatialField_ae μ C η hη L hL q, spatialField_ae μ C ξ hξ R hR q,
    Lp.coeFn_sub (spatialField μ C κ hκ M hM q) (spatialField μ C η hη L hL q),
    Lp.coeFn_smul (c : ℂ) (spatialField μ C ξ hξ R hR q), hκξη]
      with x hk hl hr hsub hsmul hx
  exact hsub.trans ((congrArg₂ (fun z w : PhotonFock => z - w) hk hl).trans
    ((kernel_sub_eq_smul C (κ x) (η x) (ξ x) c hx (q x)).trans
      ((congrArg (fun z : PhotonFock => (c : ℂ) • z) hr.symm).trans hsmul.symm)))

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (e : ℝ)

theorem coupling_eq (j : Fin N × Fin 3)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    couplingField F χ e C j u = ((-e : ℝ) : ℂ) •
      PhysicalPFReference.field (Fin N × Fin 3) (fun _ => 0) C
        (CenteredPhysicalReference.profile F χ 0) (CenteredPhysicalReference.profile_measurable F χ 0)
        (CenteredPhysicalReference.profileBound F χ) (CenteredPhysicalReference.profile_bound F χ 0) j u := by
  have he : ∀ᵐ X ∂(volume : Measure (Configuration N)),
      RadialGauge.couplingKernel F χ e j X =
        (-e) • CenteredPhysicalReference.profile F χ 0 j X :=
    ae_of_all _ (fun X => by
      simp only [RadialGauge.couplingKernel, CenteredPhysicalReference.profile, zero_add])
  exact spatial_real_smul C volume
    (CenteredPhysicalReference.profile F χ 0 j) (RadialGauge.couplingKernel F χ e j)
    (CenteredPhysicalReference.profile_measurable F χ 0 j)
    (RadialGauge.couplingKernel_continuous F χ e j).aestronglyMeasurable
    (CenteredPhysicalReference.profileBound F χ) (couplingBound F χ e) (-e)
    (CenteredPhysicalReference.profile_bound F χ 0 j)
    (ae_of_all _ (coupling_norm_bound F χ e j)) he
    (radiationSource (Fin N × Fin 3) (fun _ => 0) u)

def qP (j : Fin N × Fin 3) :=
  covariant (Fin N × Fin 3) (fun _ => 0) C
    (CenteredPhysicalReference.profile F χ 0) (CenteredPhysicalReference.profile_measurable F χ 0)
    (CenteredPhysicalReference.profileBound F χ) (CenteredPhysicalReference.profile_bound F χ 0) e j

private theorem affine_charge_eq {H : Type*} [AddCommGroup H] [Module ℂ H]
    (p a b : H) (e : ℝ) (h : b = ((-e : ℝ) : ℂ) • a) :
    (-Complex.I) • p - (e : ℂ) • a = (-Complex.I) • p + b := by
  rw [h]
  simp only [Complex.ofReal_neg, neg_smul, sub_eq_add_neg]

theorem qP_eq (j : Fin N × Fin 3) (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    qP C F χ e j u = (-Complex.I) • ordinary (Fin N × Fin 3) (fun _ => 0) j u +
      couplingField F χ e C j u := by
  have h := coupling_eq C F χ e j u
  exact (covariant_apply (Fin N × Fin 3) (fun _ => 0) C
    (CenteredPhysicalReference.profile F χ 0) (CenteredPhysicalReference.profile_measurable F χ 0)
    (CenteredPhysicalReference.profileBound F χ) (CenteredPhysicalReference.profile_bound F χ 0)
    e j u).trans (affine_charge_eq (H := WaveSpace (Fin N × Fin 3)) _ _ _ e h)

end PfHk.PauliPhysicalFieldLinearity

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
