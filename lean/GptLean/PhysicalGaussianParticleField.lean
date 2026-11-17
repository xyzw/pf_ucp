import GptLean.PhysicalGaussianSourceOperations
import GptLean.PhysicalPhotonGaussianField
import GptLean.PhysicalRemovalKernels
import GptLean.PhysicalRemovalSpatialData

/-!
The jointly measurable spatial version of the actual soft field acts by
multiplication on the actual Gaussian product source. The pointwise
Wiener--Segal identity and the spatial modification theorem are combined
before applying Fubini.
-/

noncomputable section
namespace GptLean.PhysicalPolarization

open MeasureTheory Filter Gaussian PhysicalFock PhysicalGaussianCoordinates
  RemovalEnergy SymmetricLift
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

private theorem real_smul_eq_complex_of_eq {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] {a b : ℝ}
    (h : a = b) (v : H) : a • v = (b : ℂ) • v := by
  rw [h, Complex.coe_smul]

variable (F : Frame) (χ : ArticleCutoff) (κ : ℝ) (hκ : 0 ≤ κ)
  (BF : StandardSymmetricFockExponential) (C : CanonicalSectorCCR photonMeasure)
  (W : ScalarWienerSegal photonMeasure (softOnePhoton κ) (F.softRealStructure κ))
  (N : ℕ)
  (φ : SpatialWISField (μ := W.space.measure)
    (fun g : DerivativeLabel => W.firstChaos (realLabel F χ κ hκ g)) removalLabel)

def particleSoftField (i : Fin N × Fin 3) (qx : W.space.Q × Configuration N) : ℝ :=
  φ.field i.2 [] (particle qx.2 i.1) qx.1

theorem particleSoftField_measurable (i : Fin N × Fin 3) :
    Measurable (particleSoftField F χ κ hκ W N φ i) :=
  (φ.measurable i.2 []).comp
    (((particleLinear i.1).continuous_of_finiteDimensional.measurable.comp measurable_snd).prodMk
      measurable_fst)

local instance particleFieldHardNormedAddCommGroup : NormedAddCommGroup (HardPhotonFock κ) :=
  Submodule.normedAddCommGroup (𝕜 := ℂ) (E := PhotonFock) (HardPhotonFock κ)

local instance particleFieldPhotonDirectInner : InnerProductSpace ℂ PhotonFock :=
  { (inferInstance : InnerProductSpace ℂ PhotonFock) with
    toNormedSpace := (inferInstance : NormedSpace ℂ PhotonFock) }

local instance particleFieldHardDirectInner : InnerProductSpace ℂ (HardPhotonFock κ) :=
  { (inferInstance : InnerProductSpace ℂ (HardPhotonFock κ)) with
    toNormedSpace := (inferInstance : NormedSpace ℂ (HardPhotonFock κ)) }

attribute [local irreducible] photonGaussianUnitary productSource

set_option backward.isDefEq.respectTransparency.types true in
set_option diagnostics true in
/-- No spatial matching premise is used. The field modification is the
one produced from the scalar first chaos. -/
theorem productSource_particle_soft (i : Fin N × Fin 3)
    (u : SpatialRadiationGraph (volume : Measure (Configuration N))) :
    photonGaussianSource BF κ W N
      (spatialField volume C (PhysicalRemovalKernels.soft F χ N κ i)
        (PhysicalRemovalKernels.soft_measurable F χ N κ i)
        (PhysicalRemovalKernels.bound F χ)
        (PhysicalRemovalKernels.soft_bound F χ N κ i) u) =ᵐ[W.space.measure.prod volume]
      fun qx => (particleSoftField F χ κ hκ W N φ i qx : ℂ) •
        photonGaussianSource BF κ W N (spatialRadiationInclusion volume u) qx := by
  apply productSource_varying_multiplier (X := Configuration N) (Q := W.space.Q)
    (H := PhotonFock) (K := HardPhotonFock κ)
    volume W.space.measure (photonGaussianUnitary BF κ W)
    (fun qx => (particleSoftField F χ κ hκ W N φ i qx : ℂ))
    (Complex.continuous_ofReal.comp_stronglyMeasurable
      (particleSoftField_measurable F χ κ hκ W N φ i).stronglyMeasurable)
  filter_upwards [radiationGraphInclusion.coeFn_compLpL u,
    spatialField_ae volume C (PhysicalRemovalKernels.soft F χ N κ i)
      (PhysicalRemovalKernels.soft_measurable F χ N κ i)
      (PhysicalRemovalKernels.bound F χ)
      (PhysicalRemovalKernels.soft_bound F χ N κ i) u] with x hi hs
  have hkernel : (PhysicalRemovalKernels.soft F χ N κ i x).val.1 =
      ((realLabel F χ κ hκ (removalLabel i.2 [] (particle x i.1)) : softOnePhoton κ) :
        Lp ℂ 2 photonMeasure) := by
    rw [PhysicalRemovalKernels.soft_eq_label F χ N κ hκ i x]
    rfl
  have hpoint := photonGaussianUnitary_field BF κ W C
    (realLabel F χ κ hκ (removalLabel i.2 [] (particle x i.1)))
    (PhysicalRemovalKernels.soft F χ N κ i x) hkernel (u x)
  filter_upwards [hpoint, φ.modification i.2 [] (particle x i.1)] with q hq hφ
  apply (congrArg₂ (fun a b : PhotonFock => photonGaussianUnitary BF κ W a q =
    (particleSoftField F χ κ hκ W N φ i (q, x) : ℂ) •
      photonGaussianUnitary BF κ W b q) hs hi).mpr
  exact hq.trans (real_smul_eq_complex_of_eq hφ.symm _)

end GptLean.PhysicalPolarization
