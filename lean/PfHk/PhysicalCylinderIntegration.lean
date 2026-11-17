import PfHk.SphereCoreCompact
import PfHk.PhysicalWeightedCylinder

/-! The integration conditions of the physical cylinder estimate are
ordinary consequences of compact support and continuity on its core. -/

noncomputable section
namespace PfHk.PhysicalWeightedCylinder
open MeasureTheory Set GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.SymmetricLift GptLean.Representability PfHk.PhysicalFieldRegularity
  PfHk.PolarCalculus PfHk.SphereCoreGeometry PfHk.CarlemanWeights
  PfHk.CylinderIdentity PfHk.CylinderEstimate PfHk.CylinderConjugation
  PfHk.PhysicalCylinderEstimate
open PfHk.SphereAngularField (SpherePhoton)
open scoped ENNReal InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000
local instance cylinderIntegrationPhotonReal : InnerProductSpace ℝ PhotonFock := InnerProductSpace.rclikeToReal ℂ _
attribute [local irreducible] CoreCurve.exponential CoreCurve.scalar CoreCurve.ambient
  CoreCurve.firstAmbient CoreVector.ambient CoreVector.scale CoreVector.add weightedImage

private theorem real_smul_zero_of_eq {H : Type*} [Zero H] [SMulZeroClass ℝ H]
    (a : ℝ) {u : H} (hu : u = 0) : a • u = 0 := by
  rw [hu, smul_zero]

private theorem weightedSecond_continuousOn {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (τ : ℝ) {s : Set ℝ} {f p b : ℝ → ℝ} {u du ddu : ℝ → H}
    (hf : ContinuousOn f s) (hp : ContinuousOn p s) (hb : ContinuousOn b s)
    (hu : ContinuousOn u s) (hdu : ContinuousOn du s) (hddu : ContinuousOn ddu s) :
    ContinuousOn (weightedSecond τ f p b u du ddu) s := by
  unfold weightedSecond
  fun_prop

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (O : Configuration N) (C : CanonicalSectorCCR photonMeasure)

theorem integration_of_compact (τ c α t₀ a b : ℝ) (ht₀ : 2 ≤ t₀) (hta : t₀ < a)
    (u : CoreCurve N) (k q : ℝ → SpherePhoton N)
    (hu : Continuous u.second) (hk : Continuous k) (hq : Continuous q)
    (hs : ∀ t, t ∉ Icc a b → u.ambient t = 0 ∧ k t = 0 ∧ q t = 0) :
    IntegrationConditions τ c t₀ (weightPrime α) (beta α) (betaPrime α) (betaSecond α)
      (fun t => Real.exp (-2*t)) (angularDerivative F χ hUV e C O (u.exponential τ α))
      (radiationDerivative F χ hUV e O (u.exponential τ α))
      (u.exponential τ α).ambient (u.exponential τ α).firstAmbient (u.exponential τ α).second
      (weightedImage τ α k) (weightedImage τ α q) := by
  let z := u.exponential τ α
  have hpos (t : ℝ) (ht : t ∈ Ioi t₀) : 0 < t :=
    lt_trans (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) ht₀) ht
  have ht₂ (t : ℝ) (ht : t ∈ Ioi t₀) : 2 ≤ t := ht₀.trans ht.le
  have hf : ContinuousOn (weight α) (Ioi t₀) := fun t ht =>
    (weight_hasDerivAt α (hpos t ht)).continuousAt.continuousWithinAt
  have hp : ContinuousOn (weightPrime α) (Ioi t₀) := fun t ht =>
    (weightPrime_hasDerivAt α (hpos t ht)).continuousAt.continuousWithinAt
  have hb : ContinuousOn (beta α) (Ioi t₀) := fun t ht =>
    (beta_hasDerivAt α (hpos t ht)).continuousAt.continuousWithinAt
  have hdb : ContinuousOn (betaPrime α) (Ioi t₀) := fun t ht =>
    (betaPrime_hasDerivAt α (hpos t ht)).continuousAt.continuousWithinAt
  have hddb : ContinuousOn (betaSecond α) (Ioi t₀) := by
    intro t ht
    exact continuousWithinAt_const.mul
      (Real.hasDerivAt_rpow_const (x := t) (p := -α-4) (Or.inl (hpos t ht).ne')).continuousAt.continuousWithinAt
  have hr : Continuous (fun t : ℝ => Real.exp (-2*t)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hua : Continuous u.ambient := continuous_iff_continuousAt.mpr
    (fun t => (u.ambient_hasDerivAt t).continuousAt)
  have huda : Continuous u.firstAmbient := by
    unfold CoreCurve.firstAmbient
    exact continuous_iff_continuousAt.mpr (fun t => (u.first_hasDerivAt t).continuousAt)
  have hz : Continuous z.ambient := continuous_iff_continuousAt.mpr
    (fun t => (z.ambient_hasDerivAt t).continuousAt)
  have hdz : Continuous z.firstAmbient := by
    unfold CoreCurve.firstAmbient
    exact continuous_iff_continuousAt.mpr (fun t => (z.first_hasDerivAt t).continuousAt)
  have hddz : ContinuousOn z.second (Ioi t₀) :=
    (weightedSecond_continuousOn τ hf hp hb hua.continuousOn huda.continuousOn hu.continuousOn).congr
      (fun t ht => u.exponential_second τ α (ht₂ t ht))
  have hkz : Continuous (weightedImage τ α k) := by
    unfold weightedImage
    exact (smoothExponential_contDiff τ α).continuous.smul hk
  have hqz : Continuous (weightedImage τ α q) := by
    unfold weightedImage
    exact (smoothExponential_contDiff τ α).continuous.smul hq
  have hkv : Continuous (angularDerivative F χ hUV e C O z) :=
    CenteredSphereAngularField.formDerivative_core_continuous F χ hUV e O C z
  have hqv : Continuous (radiationDerivative F χ hUV e O z) :=
    CenteredSphereRadiationEnergy.formDerivative_core_continuous F χ hUV e O z
  have hzs := u.exponential_support τ α (fun t ht => (hs t ht).1)
  have hds := z.derivatives_support hzs
  apply IntegrationConditions.of_compact τ c t₀ a b _ _ _ _ _ _ _ _ _ _ _ _ hta
    hp hb hdb hddb hr.continuousOn hkv.continuousOn hqv.continuousOn
    hz.continuousOn hdz.continuousOn hddz hkz.continuousOn hqz.continuousOn
  intro t ht
  have hzero : z.ambient t = 0 := hzs t ht
  refine ⟨hzero, (hds t ht).1, (hds t ht).2, ?_, ?_, ?_, ?_⟩
  · unfold weightedImage
    exact real_smul_zero_of_eq _ (hs t ht).2.1
  · unfold weightedImage
    exact real_smul_zero_of_eq _ (hs t ht).2.2
  · unfold CoreCurve.ambient at hzero
    exact angular_formDerivative_zero F χ hUV e O C (z.value t) t hzero
  · unfold CoreCurve.ambient at hzero
    exact radiation_formDerivative_zero F χ hUV e O (z.value t) t hzero

end PfHk.PhysicalWeightedCylinder
