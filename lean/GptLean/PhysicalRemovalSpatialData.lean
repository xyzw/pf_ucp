import GptLean.PhysicalSoftSpatialField
import GptLean.PhysicalArticleCutoff
import GptLean.RemovalLatticeOutput

/-!
The article cutoff supplies the actual lattice-removal kernel data and
the two infrared moments. Spatial Gaussian regularity uses only the
universal deterministic Sobolev and countable test backgrounds.
-/

noncomputable section
namespace GptLean.PhysicalPolarization

open MeasureTheory Filter Gaussian PhysicalFock PhysicalGaussianCoordinates
  RemovalEnergy PhysicalNormalTrace PhotonLocalizationChannel SymmetricLift
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

def removalLabel (i : Fin 3) (ds : List (Fin 3)) (x : FieldSpace) : DerivativeLabel :=
  ⟨i, ds, x⟩

def ArticleCutoff.removalA (χ : ArticleCutoff) (κ : ℝ) : ℝ :=
  Real.sqrt (CutoffProfile.asq photonMeasure (fun p => ‖p.1‖) χ.profile κ)

def ArticleCutoff.removalB (χ : ArticleCutoff) (κ : ℝ) : ℝ :=
  Real.sqrt (CutoffProfile.bsq photonMeasure (fun p => ‖p.1‖) χ.profile κ)

variable (F : Frame) (χ : ArticleCutoff) (κ : ℝ) (hκ : 0 ≤ κ)
  (BF : StandardSymmetricFockExponential) (C : CanonicalSectorCCR photonMeasure)
  (W : ScalarWienerSegal photonMeasure (softOnePhoton κ) (F.softRealStructure κ))
  {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : RankOneData PhotonFock T} (normal : NormalTraceData R) (functional : NormalFunctionalData R)
  (N : ℕ)

attribute [local instance] softSpatialPhotonDirectInner softSpatialHardDirectInner
attribute [local irreducible] photonGaussianUnitary spatialUnitary

set_option backward.isDefEq.respectTransparency.types true in
set_option diagnostics true in
/-- Primitive one-photon data derived from the physical ultraviolet and infrared assumptions. -/
def removalKernelData : RemovalKernelData
    (Q := W.space.Q) (G := DerivativeLabel) (Ω := PhotonMode)
    (Hs := SpatialPhotonSpace (volume : Measure (Configuration N))) (H := HardPhotonFock κ)
    (μ := W.space.measure) (ν := photonMeasure) (N := N)
    (weight := fun p : PhotonMode => 1 / ‖p.1‖)
    (spatialWienerSegal F χ κ hκ BF C W (volume : Measure (Configuration N)))
    (spatialKernelFieldData F χ κ hκ BF C W volume normal functional)
    Prod.fst κ (χ.removalA κ) (χ.removalB κ) removalLabel where
  base := base F χ
  kernel _ _ _ := rfl
  weighted_integrable i := softBase_weighted_integrable Prod.fst measurable_fst κ
    (base F χ i) (fun p => 1 / ‖p.1‖) (base_infrared F χ i)
  square_integrable i := by
    simpa only [one_mul] using softBase_weighted_integrable Prod.fst measurable_fst κ
      (base F χ i) (fun _ => 1) (by simpa only [one_mul] using base_ultraviolet F χ i)
  weighted_measurable i ds x := by
    exact ((measurable_const.div measurable_fst.norm).mul
      (((measurable_softDerivativeKernel Prod.fst measurable_fst ds κ
        (base F χ i) (base_measurable F χ i)).comp
          (measurable_const.prodMk measurable_id)).norm.pow_const 2)).aestronglyMeasurable
  square_measurable i ds x := by
    exact (((measurable_softDerivativeKernel Prod.fst measurable_fst ds κ
      (base F χ i) (base_measurable F χ i)).comp
        (measurable_const.prodMk measurable_id)).norm.pow_const 2).aestronglyMeasurable
  cutoff_weighted i := by
    rw [ArticleCutoff.removalA, Real.sq_sqrt (CutoffProfile.asq_nonneg κ)]
    exact softBase_inversefrequency_integral_le_asq F χ i κ
  cutoff_square i := by
    rw [ArticleCutoff.removalB, Real.sq_sqrt (CutoffProfile.bsq_nonneg κ)]
    exact softBase_integral_le_bsq F χ i κ
  zero_domain := ⟨0, map_zero _⟩
  radiation_zero := by
    change spatialGraphApply volume (softRadiationRoot κ) 0 = 0
    have h := spatialGraphApply_of_graph (volume : Measure (Configuration N))
      (softRadiationRoot κ) 0
    simpa only [map_zero] using h

set_option backward.isDefEq.respectTransparency.types true in
set_option diagnostics true in
/-- The spatial first-chaos interface is built from the same physical scalar realization. -/
def removalSpatialData (core : CountableSpatialTestCore) (sobolev : SmoothSobolevBackground) :
    LatticeSpatialData
      (Q := W.space.Q) (Ω := PhotonMode) (G := DerivativeLabel)
      (Ho := PhotonFock) (H := HardPhotonFock κ)
      (μ := W.space.measure) (ν := photonMeasure) (N := N)
      (weight := fun p : PhotonMode => 1 / ‖p.1‖)
      (spatialWienerSegal F χ κ hκ BF C W (volume : Measure (Configuration N)))
      (spatialKernelFieldData F χ κ hκ BF C W volume normal functional)
      Prod.fst κ (χ.removalA κ) (χ.removalB κ) removalLabel where
  kernels := removalKernelData F χ κ hκ BF C W normal functional N
  core := core
  sobolev := sobolev
  firstChaos := F.fullFirstChaos κ W
  momentum_measurable := measurable_fst
  nonnegative := hκ
  base_measurable := base_measurable F χ
  base_integrable := base_ultraviolet F χ
  firstChaos_eq := spatialKernelFieldData_firstChaos F χ κ hκ BF C W volume

end GptLean.PhysicalPolarization
