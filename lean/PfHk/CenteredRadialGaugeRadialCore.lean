import PfHk.CenteredRadialGaugeCoreRegularity
import PfHk.PhysicalFormProductRules
import PfHk.PhysicalOperatorCoreFinite
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-! The actual radial derivative on the finite-photon operator core.
Its original-side generator is C1 using only one derivative of g. This
is the mixed regularity route that avoids second angular gauge derivatives. -/

noncomputable section
namespace PfHk.CenteredRadialGauge

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.PhysicalNonattainmentFluxKernel GptLean.SymmetricLift
  GptLean.Representability Gaussian PfHk.PhysicalFieldRegularity
  PfHk.PhysicalOperatorDomain PfHk.WeylGraphC1Calculus
open scoped ENNReal InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 300000
attribute [local irreducible] kernelField unitary graphLift radiationGraphInclusion
  gaugedValue coreValue contraction labelDerivative fullRadiationInclusion fullRootProjection

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (O : Configuration N) (C : CanonicalSectorCCR photonMeasure)
  (W : ConcreteWeylLaw photonMeasure)

include hUV in
theorem contraction_diagonal_contDiff :
    ContDiff ℝ (1 : ℕ∞) (fun X : Configuration N => contraction F χ e O X X) := by
  unfold contraction
  apply ContDiff.sum
  intro j _
  exact (contDiff_piLp_apply 2 : ContDiff ℝ (1 : ℕ∞) (fun X : Configuration N => X j)).smul
    (couplingKernel_contDiff F χ hUV e O j)

def radialGenerator {s : Set (Configuration N)} (a : SmoothCore s) (X : Configuration N) : PhotonFock :=
  Complex.I • kernelField C (contraction F χ e O X X) (a.rootWave X) +
    fderiv ℝ (coreValue a.rootWave) X X

theorem coreValue_fderiv {s : Set (Configuration N)} (a : SmoothCore s)
    (X v : Configuration N) :
    fderiv ℝ (coreValue a.rootWave) X v =
      fullRadiationInclusion (fderiv ℝ a.representative X v) := by
  have h := ((fullRadiationInclusion.restrictScalars ℝ).hasFDerivAt.comp X
    (a.smooth.differentiable (by simp) X).hasFDerivAt).fderiv
  have he : coreValue a.rootWave = fun Y => fullRadiationInclusion (a.representative Y) := by
    funext Y
    unfold coreValue SmoothCore.rootWave fullRadiationInclusion
    rfl
  have hh : fderiv ℝ (fun Y => fullRadiationInclusion (a.representative Y)) X v =
      fullRadiationInclusion (fderiv ℝ a.representative X v) := by
    convert! congrArg (fun L : Configuration N →L[ℝ] PhotonFock => L v) h using 1
  exact (congrArg (fun f : Configuration N → PhotonFock => fderiv ℝ f X v) he).trans hh

private theorem photonFinite_smul_add (u v : PhotonFock) (c : ℂ) (M : ℕ)
    (hu : FiniteNumberSupport photonMeasure M u) (hv : FiniteNumberSupport photonMeasure M v) :
    FiniteNumberSupport photonMeasure M (c • u + v) := by
  intro n hn
  change c • u n + v n = 0
  rw [hu n hn, hv n hn, smul_zero, zero_add]

theorem radialGenerator_photonFinite {s : Set (Configuration N)} (a : SmoothCore s)
    (X : Configuration N) :
    FiniteNumberSupport photonMeasure (a.photonCutoff + 1) (radialGenerator F χ e O C a X) := by
  have hfinite : FiniteNumberSupport photonMeasure a.photonCutoff (radiationGraphInclusion (a.rootWave X)) := by
    have he : radiationGraphInclusion (a.rootWave X) = fullRadiationInclusion (a.representative X) := by
      unfold SmoothCore.rootWave fullRadiationInclusion
      rfl
    rw [he]
    exact a.photonFinite X
  have hf := kernelField_photonFinite C (contraction F χ e O X X) (a.rootWave X) a.photonCutoff hfinite
  have hd : FiniteNumberSupport photonMeasure (a.photonCutoff + 1)
      (fderiv ℝ (coreValue a.rootWave) X X) := by
    rw [coreValue_fderiv]
    intro n hn
    exact a.derivative_photonFinite X X n (by omega)
  exact photonFinite_smul_add _ _ Complex.I (a.photonCutoff + 1) hf hd

include hUV in
theorem radialGenerator_contDiff {s : Set (Configuration N)} (a : SmoothCore s) :
    ContDiff ℝ (1 : ℕ∞) (radialGenerator F χ e O C a) := by
  have hq : ContDiff ℝ (1 : ℕ∞) a.rootWave := a.rootWave_smooth.of_le (by simp)
  have hk := contraction_diagonal_contDiff F χ hUV e O
  have hfield := ((PhysicalFormProductRules.fieldBilinear C).contDiff.comp hk).clm_apply hq
  have hu : ContDiff ℝ (⊤ : ℕ∞) (coreValue a.rootWave) := by
    unfold coreValue
    convert! (radiationGraphInclusion.restrictScalars ℝ).contDiff.comp a.rootWave_smooth using 1
  have hd : ContDiff ℝ (1 : ℕ∞) (fun X => fderiv ℝ (coreValue a.rootWave) X X) :=
    (hu.fderiv_right (by simp)).clm_apply contDiff_id
  convert! (hfield.const_smul Complex.I).add hd using 1

def gaugedRadialValue {s : Set (Configuration N)} (a : SmoothCore s) (X : Configuration N) : PhotonFock :=
  unitary F χ e O W X (radialGenerator F χ e O C a X)

include hUV in
theorem gaugedRadialValue_contDiff (B : StandardWeylGraphC1 W)
    {s : Set (Configuration N)} (a : SmoothCore s) (M : ℕ)
    (hM : ∀ X, FiniteNumberSupport photonMeasure M (radialGenerator F χ e O C a X)) :
    ContDiff ℝ (1 : ℕ∞) (gaugedRadialValue F χ e O C W a) := by
  have hf : ContDiff ℝ (1 : ℕ∞) (fun X => Complex.I • (label F χ e O X).val.1) :=
    (((component false).contDiff).comp (label_contDiff F χ hUV e O)).const_smul Complex.I
  unfold gaugedRadialValue unitary
  convert! B.ambient_c1 (Configuration N) _ _ M hf (radialGenerator_contDiff F χ hUV e O C a) hM using 1

theorem labelDerivative_radial (X : Configuration N) :
    labelDerivative F χ hUV e O X X = contraction F χ e O X X := by
  have h := radialConnection_eq F χ hUV e O X X
  rw [radialConnection_radial] at h
  exact (sub_eq_zero.mp h.symm).symm

include hUV in
/-- The actual Euler radial derivative of the Weyl-transformed core. -/
theorem gaugedValue_radial (B : StandardWeylGraphC1 W)
    {s : Set (Configuration N)} (a : SmoothCore s) (X : Configuration N) :
    fderiv ℝ (gaugedValue F χ e O W a.rootWave) X X =
      gaugedRadialValue F χ e O C W a X := by
  have hu : ContDiff ℝ (1 : ℕ∞) (coreValue a.rootWave) := by
    unfold coreValue
    convert! a.value_smooth using 1
  have hfinite : FiniteNumberSupport photonMeasure a.photonCutoff (coreValue a.rootWave X) := by
    convert! a.photonFinite X using 1
    unfold coreValue SmoothCore.rootWave fullRadiationInclusion
    rfl
  have h := gaugedValue_fderiv F χ hUV e O C W a.rootWave X X
    (hu.differentiable one_ne_zero).differentiableAt
    ((gauged_core_contDiff F χ hUV e O W B a).differentiable one_ne_zero).differentiableAt
    a.photonCutoff hfinite
  rw [labelDerivative_radial] at h
  exact h

theorem sphereGraphWave_inclusion {s : Set (Configuration N)} (a : SmoothCore s)
    (p : ℝ × PfHk.SphereAngularField.Sphere N) :
    radiationGraphInclusion (sphereGraphWave F χ hUV e O W a p) =
      gaugedValue F χ e O W a.rootWave (logarithmicPoint p) := by
  unfold sphereGraphWave gaugedValue coreValue
  exact graphLift_inclusion F χ hUV e O W (logarithmicPoint p) (a.rootWave (logarithmicPoint p))

include hUV in
/-- Actual logarithmic radial differentiation of the gauged core. -/
theorem logarithmic_gauged_hasDerivAt (B : StandardWeylGraphC1 W)
    {s : Set (Configuration N)} (a : SmoothCore s)
    (θ : PfHk.SphereAngularField.Sphere N) (t : ℝ) :
    HasDerivAt (fun v => gaugedValue F χ e O W a.rootWave (Real.exp (-v) • θ.val))
      (-gaugedRadialValue F χ e O C W a (Real.exp (-t) • θ.val)) t := by
  have hw := (gauged_core_contDiff F χ hUV e O W B a).differentiable one_ne_zero
  have h := hw.differentiableAt.hasFDerivAt.comp_hasDerivAt t
    ((PolarCalculus.radius_hasDerivAt t).smul_const θ.val)
  have he : fderiv ℝ (gaugedValue F χ e O W a.rootWave) (Real.exp (-t) • θ.val)
      ((-Real.exp (-t)) • θ.val) =
      -gaugedRadialValue F χ e O C W a (Real.exp (-t) • θ.val) := by
    rw [neg_smul, map_neg, gaugedValue_radial F χ hUV e O C W B a]
  convert! h using 1
  exact he.symm

end PfHk.CenteredRadialGauge
