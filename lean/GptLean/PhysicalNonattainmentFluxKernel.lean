import GptLean.PhysicalMultiplicationGraph
import GptLean.PhysicalPolarizationRealStructure
import GptLean.TransformationsKernelCovariance
import GptLean.NonattainmentTubeFlux

/-!
The physical weighted one-photon kernel space is complete, since its
defining inverse-frequency relation is a closed multiplication graph.
Its Bochner integrals retain both components and the physical real
structure, so field circulation is an actual weighted photon kernel.
-/

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

namespace GptLean.PhysicalNonattainmentFluxKernel

open MeasureTheory PhysicalFock PhysicalPolarization Gaussian Nonattainment
open scoped ENNReal Interval

theorem weightedKernelSubspace_closed :
    IsClosed (weightedKernelSubspace : Set
      (Lp ℂ 2 photonMeasure × Lp ℂ 2 photonMeasure)) := by
  have he : (weightedKernelSubspace : Set
      (Lp ℂ 2 photonMeasure × Lp ℂ 2 photonMeasure)) =
      Prod.swap ⁻¹' (PhysicalMultiplicationGraph.graph photonMeasure
        (H := ℂ) (fun p => (Real.sqrt ‖p.1‖ : ℂ)) : Set _) := rfl
  rw [he]
  exact (PhysicalMultiplicationGraph.graph_closed photonMeasure
    (H := ℂ) (fun p => (Real.sqrt ‖p.1‖ : ℂ))).preimage continuous_swap

instance : CompleteSpace WeightedPhotonKernel :=
  weightedKernelSubspace_closed.completeSpace_coe

def component (infrared : Bool) : WeightedPhotonKernel →L[ℝ] Lp ℂ 2 photonMeasure :=
  ((if infrared then ContinuousLinearMap.snd ℂ _ _ else ContinuousLinearMap.fst ℂ _ _).comp
    weightedKernelSubspace.subtypeL).restrictScalars ℝ

@[simp] theorem component_false (k : WeightedPhotonKernel) : component false k = k.val.1 := rfl
@[simp] theorem component_true (k : WeightedPhotonKernel) : component true k = k.val.2 := rfl

theorem component_integral (infrared : Bool) (k : ℝ → WeightedPhotonKernel)
    {a b : ℝ} (hk : IntervalIntegrable k volume a b) :
    component infrared (∫ t in a..b, k t) =
      ∫ t in a..b, component infrared (k t) :=
  ((component infrared).intervalIntegral_comp_comm hk).symm

theorem integral_fixed (F : Frame) (k : ℝ → WeightedPhotonKernel)
    {a b : ℝ} (hk : IntervalIntegrable k volume a b)
    (hreal : ∀ t, F.conjugation (k t).val.1 = (k t).val.1) :
    F.conjugation (∫ t in a..b, k t).val.1 = (∫ t in a..b, k t).val.1 := by
  have hc := component_integral false k hk
  simp only [component_false] at hc
  rw [hc]
  exact ((F.realStructure.realIsometry).intervalIntegral_comp_comm
    (fun t => (k t).val.1)).symm.trans
      (intervalIntegral.integral_congr (fun t _ => hreal t))

theorem real_smul_fixed (F : Frame) (c : ℝ) (k : WeightedPhotonKernel)
    (hk : F.conjugation k.val.1 = k.val.1) :
    F.conjugation (c • k).val.1 = (c • k).val.1 := by
  change F.realStructure.realCLM (c • k.val.1) = c • k.val.1
  rw [map_smul]
  exact congrArg (fun v : Lp ℂ 2 photonMeasure => c • v) hk

theorem add_fixed (F : Frame) (k l : WeightedPhotonKernel)
    (hk : F.conjugation k.val.1 = k.val.1)
    (hl : F.conjugation l.val.1 = l.val.1) :
    F.conjugation (k + l).val.1 = (k + l).val.1 := by
  change F.conjugation (k.val.1 + l.val.1) = k.val.1 + l.val.1
  rw [map_add, hk, hl]

def physicalKernel (F : Frame) (χ : ArticleCutoff) (i : Fin 3) (x : FieldSpace) :
    WeightedPhotonKernel :=
  PhysicalProfiles.momentumKernel (formFactors F χ) rfl
    (LinearIsometryEquiv.refl ℝ _) (i, x)

theorem physicalKernel_continuous (F : Frame) (χ : ArticleCutoff) (i : Fin 3) :
    Continuous (physicalKernel F χ i) :=
  (PhysicalProfiles.momentumKernel_continuous (formFactors F χ) rfl
    (LinearIsometryEquiv.refl ℝ _)).comp (continuous_const.prodMk continuous_id)

theorem physicalKernel_component (F : Frame) (χ : ArticleCutoff)
    (infrared : Bool) (i : Fin 3) (x : FieldSpace) :
    component infrared (physicalKernel F χ i x) = weightedFieldKernel F χ infrared i x := by
  cases infrared
  · exact TransformationsKernelCovariance.momentumKernel_fst (formFactors F χ) rfl
      (LinearIsometryEquiv.refl ℝ _) (i, x)
  · exact TransformationsKernelCovariance.momentumKernel_snd (formFactors F χ) rfl
      (LinearIsometryEquiv.refl ℝ _) (i, x)

theorem physicalKernel_fixed (F : Frame) (χ : ArticleCutoff) (i : Fin 3) (x : FieldSpace) :
    F.conjugation (physicalKernel F χ i x).val.1 = (physicalKernel F χ i x).val.1 := by
  have h := physicalKernel_component F χ false i x
  simp only [component_false, weightedFieldKernel_false] at h
  rw [h]
  exact F.fourierKernel_fixed χ i x

private theorem ellipse_integrable (F : Frame) (χ : ArticleCutoff) (a b : ℝ) :
    IntervalIntegrable (fun t =>
      (-a * Real.sin t) • physicalKernel F χ 0 (ellipse a b t) +
      (b * Real.cos t) • physicalKernel F χ 1 (ellipse a b t)) volume
      (-(Real.pi / 2)) (3 * Real.pi / 2) :=
  (((continuous_const.mul Real.continuous_sin).smul
      ((physicalKernel_continuous F χ 0).comp (ellipse_continuous a b))).add
    ((continuous_const.mul Real.continuous_cos).smul
      ((physicalKernel_continuous F χ 1).comp (ellipse_continuous a b)))).intervalIntegrable _ _

def centralKernel (F : Frame) (χ : ArticleCutoff) (a b : ℝ) : WeightedPhotonKernel :=
  ellipseFlux (physicalKernel F χ 0) (physicalKernel F χ 1) a b

theorem centralKernel_component (F : Frame) (χ : ArticleCutoff)
    (infrared : Bool) (a b : ℝ) :
    component infrared (centralKernel F χ a b) = centralFieldFlux F χ infrared a b := by
  change component infrared (∫ t in -(Real.pi / 2)..3 * Real.pi / 2,
    (-a * Real.sin t) • physicalKernel F χ 0 (ellipse a b t) +
    (b * Real.cos t) • physicalKernel F χ 1 (ellipse a b t)) = _
  rw [component_integral infrared _ (ellipse_integrable F χ a b)]
  simp only [map_add, map_smul, physicalKernel_component]
  rfl

theorem centralKernel_fixed (F : Frame) (χ : ArticleCutoff) (a b : ℝ) :
    F.conjugation (centralKernel F χ a b).val.1 = (centralKernel F χ a b).val.1 := by
  apply integral_fixed F _ (ellipse_integrable F χ a b)
  intro t
  exact add_fixed F _ _
    (real_smul_fixed F _ _ (physicalKernel_fixed F χ 0 _))
    (real_smul_fixed F _ _ (physicalKernel_fixed F χ 1 _))

private theorem tube_integrable (F : Frame) (χ : ArticleCutoff)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (r z : ℝ) :
    IntervalIntegrable (fun t =>
      (ellipseTubeFactor a b t r * (-a * Real.sin t)) •
        physicalKernel F χ 0 (ellipseTubePoint a b t r z) +
      (ellipseTubeFactor a b t r * (b * Real.cos t)) •
        physicalKernel F χ 1 (ellipseTubePoint a b t r z)) volume
      (-(Real.pi / 2)) (3 * Real.pi / 2) := by
  have hp : Continuous (fun t => ellipseTubePoint a b t r z) :=
    continuous_iff_continuousAt.mpr fun t =>
      (ellipseTubePoint_hasDerivAt_angle ha hab t r z).continuousAt
  have hc : Continuous (ellipseCurvature a b) :=
    continuous_const.div ((ellipseVelocity_continuous a b).norm.pow 3)
      (fun t => pow_ne_zero 3 (ellipseVelocity_norm_pos ha hab t).ne')
  have hf : Continuous (fun t => ellipseTubeFactor a b t r) :=
    continuous_const.sub (continuous_const.mul hc)
  exact (((hf.mul (continuous_const.mul Real.continuous_sin)).smul
      ((physicalKernel_continuous F χ 0).comp hp)).add
    ((hf.mul (continuous_const.mul Real.continuous_cos)).smul
      ((physicalKernel_continuous F χ 1).comp hp))).intervalIntegrable _ _

def tubeKernel (F : Frame) (χ : ArticleCutoff) (a b r z : ℝ) : WeightedPhotonKernel :=
  ellipseTubeFlux (physicalKernel F χ 0) (physicalKernel F χ 1) a b r z

theorem tubeKernel_component (F : Frame) (χ : ArticleCutoff)
    (infrared : Bool) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (r z : ℝ) :
    component infrared (tubeKernel F χ a b r z) = tubeFieldFlux F χ infrared a b r z := by
  change component infrared (∫ t in -(Real.pi / 2)..3 * Real.pi / 2,
    (ellipseTubeFactor a b t r * (-a * Real.sin t)) •
      physicalKernel F χ 0 (ellipseTubePoint a b t r z) +
    (ellipseTubeFactor a b t r * (b * Real.cos t)) •
      physicalKernel F χ 1 (ellipseTubePoint a b t r z)) = _
  rw [component_integral infrared _ (tube_integrable F χ ha hab r z)]
  simp only [map_add, map_smul, physicalKernel_component]
  rfl

theorem tubeKernel_fixed (F : Frame) (χ : ArticleCutoff)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (r z : ℝ) :
    F.conjugation (tubeKernel F χ a b r z).val.1 = (tubeKernel F χ a b r z).val.1 := by
  apply integral_fixed F _ (tube_integrable F χ ha hab r z)
  intro t
  exact add_fixed F _ _
    (real_smul_fixed F _ _ (physicalKernel_fixed F χ 0 _))
    (real_smul_fixed F _ _ (physicalKernel_fixed F χ 1 _))

end GptLean.PhysicalNonattainmentFluxKernel
