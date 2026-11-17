import GptLean.PhysicalPhotonGaussianField
import GptLean.PhysicalGaussianLabels
import GptLean.PhysicalSoftDerivativeKernel
import GptLean.PhysicalSpatialRadiationLocality
import GptLean.PhysicalFockSoftRadiationBound

/-!
The Gaussian field interface on electronic L² is instantiated by the
article's actual weighted kernels. The radiation quantity in the bound is
the soft photon square root. It is not replaced by total radiation.
-/

noncomputable section
namespace GptLean.PhysicalPolarization

open MeasureTheory Filter Gaussian PhysicalFock PhysicalGaussianCoordinates
open PhysicalNormalTrace PhotonLocalizationChannel
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

private theorem l2_square_identity {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ν : Measure X) (u v w : Lp H 2 ν) (a : ℝ)
    (h : ∀ᵐ x ∂ν, ‖u x‖ ^ 2 = ‖v x‖ ^ 2 + a * ‖w x‖ ^ 2) :
    ‖u‖ ^ 2 = ‖v‖ ^ 2 + a * ‖w‖ ^ 2 := by
  let : InnerProductSpace ℝ H := InnerProductSpace.complexToReal
  have hi (f : Lp H 2 ν) : Integrable (fun x => ‖f x‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  rw [PhotonKernelLocalization.l2_norm_sq_eq_integral,
    PhotonKernelLocalization.l2_norm_sq_eq_integral,
    PhotonKernelLocalization.l2_norm_sq_eq_integral, ← integral_const_mul,
    ← integral_add (hi v) ((hi w).const_mul a)]
  exact integral_congr_ae h

structure DerivativeLabel where
  component : Fin 3
  derivatives : List (Fin 3)
  position : FieldSpace

variable (F : Frame) (χ : ArticleCutoff) (κ : ℝ) (hκ : 0 ≤ κ)
  (BF : StandardSymmetricFockExponential) (C : CanonicalSectorCCR photonMeasure)
  (W : ScalarWienerSegal photonMeasure (softOnePhoton κ) (F.softRealStructure κ))

def labelKernel (g : DerivativeLabel) : WeightedPhotonKernel :=
  derivativeKernel F χ hκ g.component g.derivatives g.position

def realLabel (g : DerivativeLabel) : (F.softRealStructure κ).fixedSpace :=
  F.softLabel χ κ hκ g.component g.derivatives g.position

theorem labelKernel_realLabel (g : DerivativeLabel) :
    (labelKernel F χ κ hκ g).val.1 =
      ((realLabel F χ κ hκ g : softOnePhoton κ) : Lp ℂ 2 photonMeasure) := rfl

section Spatial

variable {X : Type*} [MeasurableSpace X] (ν : Measure X) [SFinite ν] [IsSeparable ν]

local instance softSpatialHardNormedAddCommGroup :
    NormedAddCommGroup (HardPhotonFock κ) :=
  Submodule.normedAddCommGroup (𝕜 := ℂ) (E := PhotonFock) (HardPhotonFock κ)

local instance softSpatialPhotonDirectInner : InnerProductSpace ℂ PhotonFock :=
  { (inferInstance : InnerProductSpace ℂ PhotonFock) with
    toNormedSpace := (inferInstance : NormedSpace ℂ PhotonFock) }

local instance softSpatialHardDirectInner : InnerProductSpace ℂ (HardPhotonFock κ) :=
  { (inferInstance : InnerProductSpace ℂ (HardPhotonFock κ)) with
    toNormedSpace := (inferInstance : NormedSpace ℂ (HardPhotonFock κ)) }

local instance softSpatialHardL2NormedAddCommGroup :
    NormedAddCommGroup (Lp (HardPhotonFock κ) 2 ν) :=
  Lp.instNormedAddCommGroup (E := HardPhotonFock κ) (p := 2) (μ := ν)

local instance softSpatialHardL2RealNormedSpace :
    NormedSpace ℝ (Lp (HardPhotonFock κ) 2 ν) :=
  Lp.instNormedSpace (𝕜 := ℝ) (E := HardPhotonFock κ) (p := 2) (μ := ν)

attribute [local irreducible] photonGaussianUnitary spatialUnitary spatialGraphApply

set_option backward.isDefEq.respectTransparency.types true in
set_option diagnostics true in
private theorem spatial_field_on_domain (g : DerivativeLabel) (u : SpatialPhotonSpace ν)
    (hu : spatialRadiationDomain ν u) :
    (fun q : W.space.Q =>
      (spatialUnitary (X := X) (Q := W.space.Q) (H := PhotonFock) (K := HardPhotonFock κ)
        ν W.space.measure (photonGaussianUnitary BF κ W)
        (spatialGraphApply ν (kernelField C (labelKernel F χ κ hκ g)) u) q :
          Lp (HardPhotonFock κ) 2 ν)) =ᵐ[W.space.measure]
      fun q : W.space.Q => SMul.smul (M := ℝ) (α := Lp (HardPhotonFock κ) 2 ν)
        (W.firstChaos (realLabel F χ κ hκ g) q)
        (spatialUnitary (X := X) (Q := W.space.Q) (H := PhotonFock) (K := HardPhotonFock κ)
          ν W.space.measure (photonGaussianUnitary BF κ W) u q) := by
  obtain ⟨v, rfl⟩ := hu
  have hgraph := spatialGraphApply_of_graph ν (kernelField C (labelKernel F χ κ hκ g)) v
  have hfield := spatialGaussianUnitary_field BF κ W C ν (realLabel F χ κ hκ g)
    (labelKernel F χ κ hκ g) (labelKernel_realLabel F χ κ hκ g) v
  exact (congrArg (fun w : SpatialPhotonSpace ν =>
    (fun q : W.space.Q =>
      (spatialUnitary (X := X) (Q := W.space.Q) (H := PhotonFock) (K := HardPhotonFock κ)
        ν W.space.measure (photonGaussianUnitary BF κ W) w q : Lp (HardPhotonFock κ) 2 ν))
      =ᵐ[W.space.measure] fun q : W.space.Q =>
        SMul.smul (M := ℝ) (α := Lp (HardPhotonFock κ) 2 ν)
          (W.firstChaos (realLabel F χ κ hκ g) q)
          (spatialUnitary (X := X) (Q := W.space.Q) (H := PhotonFock) (K := HardPhotonFock κ)
            ν W.space.measure (photonGaussianUnitary BF κ W)
            (spatialRadiationInclusion ν v) q)) hgraph).mpr hfield

set_option backward.isDefEq.respectTransparency.types true in
/-- The field acts on the range of the actual electronic radiation graph. -/
def spatialWienerSegal : WienerSegalData W.space.Q (SpatialPhotonSpace ν)
    (Lp (HardPhotonFock κ) 2 ν) DerivativeLabel W.space.measure :=
  WienerSegalData.ofUnitary (Q := W.space.Q) (H := SpatialPhotonSpace ν)
    (K := Lp (HardPhotonFock κ) 2 ν) (μ := W.space.measure) (G := DerivativeLabel)
    (spatialUnitary (X := X) (Q := W.space.Q) (H := PhotonFock) (K := HardPhotonFock κ)
      ν W.space.measure (photonGaussianUnitary BF κ W))
    (fun _ => spatialRadiationDomain ν)
    (fun g => spatialGraphApply ν (kernelField C (labelKernel F χ κ hκ g)))
    (fun g => W.firstChaos (realLabel F χ κ hκ g))
    (spatial_field_on_domain F χ κ hκ BF C W ν)

omit [SFinite ν] [IsSeparable ν] in
private theorem spatial_creation_norm_sq (k : WeightedPhotonKernel)
    (u : SpatialRadiationGraph ν) :
    ‖(kernelCreation C k).compLpL 2 ν u‖ ^ 2 =
      ‖(kernelAnnihilation k).compLpL 2 ν u‖ ^ 2 +
        ‖k.val.1‖ ^ 2 * ‖spatialRadiationInclusion ν u‖ ^ 2 := by
  apply l2_square_identity ν ((kernelCreation C k).compLpL 2 ν u)
    ((kernelAnnihilation k).compLpL 2 ν u) (spatialRadiationInclusion ν u) (‖k.val.1‖ ^ 2)
  filter_upwards [(kernelCreation C k).coeFn_compLpL u,
    (kernelAnnihilation k).coeFn_compLpL u, radiationGraphInclusion.coeFn_compLpL u]
    with x hc ha hr
  exact (congrArg (fun v : PhotonFock => ‖v‖ ^ 2) hc).trans
    ((creationRadiation_norm_sq C k.val.1 k.val.2 k.property (u x)).trans
      (congrArg₂ (fun a b : PhotonFock => ‖a‖ ^ 2 + ‖k.val.1‖ ^ 2 * ‖b‖ ^ 2)
        ha hr).symm)

variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : RankOneData PhotonFock T} (normal : NormalTraceData R) (functional : NormalFunctionalData R)

include BF C normal functional in
omit [SFinite ν] [IsSeparable ν] in
private theorem spatial_annihilation_soft_bound (k : WeightedPhotonKernel)
    (hk : k.val.1 ∈ softOnePhoton κ) (u : SpatialRadiationGraph ν) :
    ‖(kernelAnnihilation k).compLpL 2 ν u‖ ≤
      ‖k.val.2‖ * ‖(softRadiationRoot κ).compLpL 2 ν u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(kernelAnnihilation k).coeFn_compLpL u,
    (softRadiationRoot κ).coeFn_compLpL u] with x ha hr
  exact (congrArg₂ (fun a b : PhotonFock => ‖a‖ ≤ ‖k.val.2‖ * ‖b‖) ha hr).mpr
    (kernelAnnihilation_soft_bound normal functional BF C κ k hk (u x))

set_option backward.isDefEq.respectTransparency.types true in
include BF C normal functional in
omit [SFinite ν] [IsSeparable ν] in
private theorem spatial_annihilation_on_domain (g : DerivativeLabel)
    (u : SpatialPhotonSpace ν) (hu : spatialRadiationDomain ν u) :
    ‖spatialGraphApply ν (kernelAnnihilation (labelKernel F χ κ hκ g)) u‖ ≤
      Real.sqrt (∫ p : PhotonMode, (1 / ‖p.1‖) *
        ‖softDerivativeKernel Prod.fst g.derivatives κ g.position
          (base F χ g.component) p‖ ^ 2 ∂photonMeasure) *
        ‖spatialGraphApply ν (softRadiationRoot κ) u‖ := by
  obtain ⟨v, rfl⟩ := hu
  have ha := congrArg (fun w : SpatialPhotonSpace ν => ‖w‖)
    (spatialGraphApply_of_graph ν (kernelAnnihilation (labelKernel F χ κ hκ g)) v)
  have hr := congrArg (fun w : SpatialPhotonSpace ν => ‖w‖)
    (spatialGraphApply_of_graph ν (softRadiationRoot κ) v)
  have hk := derivativeKernel_snd_norm F χ hκ g.component g.derivatives g.position
  calc
    _ = ‖(kernelAnnihilation (labelKernel F χ κ hκ g)).compLpL 2 ν v‖ := ha
    _ ≤ ‖(labelKernel F χ κ hκ g).val.2‖ * ‖(softRadiationRoot κ).compLpL 2 ν v‖ :=
      spatial_annihilation_soft_bound κ BF C ν normal functional
        (labelKernel F χ κ hκ g)
        (derivativeKernel_fst_mem F χ hκ g.component g.derivatives g.position) v
    _ = _ := congrArg₂ (fun a b : ℝ => a * b) hk hr.symm

set_option backward.isDefEq.respectTransparency.types true in
omit [SFinite ν] [IsSeparable ν] in
private theorem spatial_creation_on_domain (g : DerivativeLabel)
    (u : SpatialPhotonSpace ν) (hu : spatialRadiationDomain ν u) :
    ‖spatialGraphApply ν (kernelCreation C (labelKernel F χ κ hκ g)) u‖ ^ 2 =
      ‖spatialGraphApply ν (kernelAnnihilation (labelKernel F χ κ hκ g)) u‖ ^ 2 +
        (∫ p : PhotonMode, ‖softDerivativeKernel Prod.fst g.derivatives κ g.position
          (base F χ g.component) p‖ ^ 2 ∂photonMeasure) * ‖u‖ ^ 2 := by
  obtain ⟨v, rfl⟩ := hu
  have hc := congrArg (fun w : SpatialPhotonSpace ν => ‖w‖ ^ 2)
    (spatialGraphApply_of_graph ν (kernelCreation C (labelKernel F χ κ hκ g)) v)
  have ha := congrArg (fun w : SpatialPhotonSpace ν => ‖w‖ ^ 2)
    (spatialGraphApply_of_graph ν (kernelAnnihilation (labelKernel F χ κ hκ g)) v)
  have hk := derivativeKernel_fst_norm_sq F χ hκ g.component g.derivatives g.position
  calc
    _ = ‖(kernelCreation C (labelKernel F χ κ hκ g)).compLpL 2 ν v‖ ^ 2 := hc
    _ = ‖(kernelAnnihilation (labelKernel F χ κ hκ g)).compLpL 2 ν v‖ ^ 2 +
        ‖(labelKernel F χ κ hκ g).val.1‖ ^ 2 * ‖spatialRadiationInclusion ν v‖ ^ 2 :=
      spatial_creation_norm_sq C ν (labelKernel F χ κ hκ g) v
    _ = _ := congrArg₂ (fun a b : ℝ => a + b * ‖spatialRadiationInclusion ν v‖ ^ 2)
      ha.symm hk

set_option backward.isDefEq.respectTransparency.types true in
/-- The physical soft-field estimates on the same spatial Gaussian map. -/
def spatialKernelFieldData : KernelFieldData photonMeasure
    (spatialWienerSegal F χ κ hκ BF C W ν) (fun p => 1 / ‖p.1‖) where
  kernel g := softDerivativeKernel Prod.fst g.derivatives κ g.position (base F χ g.component)
  weight_nonneg _ := by positivity
  radiationDomain := spatialRadiationDomain ν
  radiation := spatialGraphApply ν (softRadiationRoot κ)
  ann g := spatialGraphApply ν (kernelAnnihilation (labelKernel F χ κ hκ g))
  cre g := spatialGraphApply ν (kernelCreation C (labelKernel F χ κ hκ g))
  field_domain _ _ h _ _ := h
  field_eq g u _ := spatialGraphApply_add ν _ _ u
  annihilation_bound g u _ hu _ :=
    spatial_annihilation_on_domain F χ κ hκ BF C ν normal functional g u hu
  creation_norm_sq g u hu _ := spatial_creation_on_domain F χ κ hκ C ν g u hu

theorem spatialKernelFieldData_locality :
    RemovalSource.SpatialRadiationLocality
      (spatialKernelFieldData F χ κ hκ BF C W ν normal functional).radiationDomain
      (spatialKernelFieldData F χ κ hκ BF C W ν normal functional).radiation :=
  spatialGraphApply_locality ν (softRadiationRoot κ)

theorem spatialKernelFieldData_firstChaos (i : Fin 3) (ds : List (Fin 3)) (x : FieldSpace) :
    F.fullFirstChaos κ W (softKernelL2 Prod.fst measurable_fst ds hκ
      (base F χ i) (base_measurable F χ i) (base_ultraviolet F χ i) x) =ᵐ[W.space.measure]
      (spatialWienerSegal F χ κ hκ BF C W ν).coordinate ⟨i, ds, x⟩ :=
  F.fullFirstChaos_label_ae χ κ hκ W i ds x

end Spatial
end GptLean.PhysicalPolarization
