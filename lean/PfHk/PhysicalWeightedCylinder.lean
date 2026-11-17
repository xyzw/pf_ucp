import PfHk.PhysicalCylinderEstimate
import PfHk.SphereCoreWeight
import PfHk.WeightedCylinderDensity
import PfHk.CompactCylinderIntegration

/-! The free Carleman estimate in logarithmic cylinder coordinates for
the actual centered angular and radiation forms. Boundary/integrability
conditions are ordinary core facts, discharged by compact-cylinder
continuity. The physical polar operator realization is a separate step. -/

noncomputable section
namespace PfHk.PhysicalWeightedCylinder

open MeasureTheory Filter Set GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.SymmetricLift GptLean.Representability PfHk.PhysicalFieldRegularity
  PfHk.PolarCalculus PfHk.SphereCoreGeometry PfHk.CylinderIdentity PfHk.CylinderEstimate
  PfHk.CarlemanWeights PfHk.CylinderConjugation PfHk.PhysicalCylinderEstimate
open PfHk.SphereAngularField (SpherePhoton)
open scoped ENNReal Topology InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 100000
local instance physicalWeightedPhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _
attribute [local irreducible] CenteredSphereAngularField.energy CenteredSphereRadiationEnergy.energy
  CoreCurve.exponential CoreCurve.scalar CoreVector.scale CoreVector.add CoreVector.ambient
  IsAngularRepresentative IsRadiationRepresentative angularPair radiationPair CoerciveAt

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (C : CanonicalSectorCCR photonMeasure) (W : ConcreteWeylLaw photonMeasure)

def weightedImage (τ α : ℝ) (k : ℝ → SpherePhoton N) (t : ℝ) : SpherePhoton N :=
  smoothExponential τ α t • k t

theorem weightedImage_eq (τ α : ℝ) (k : ℝ → SpherePhoton N) {t : ℝ} (ht : 2 ≤ t) :
    weightedImage τ α k t = weighted τ (weight α) k t := by
  unfold weightedImage
  exact smoothExponential_weighted τ α k ht

attribute [local irreducible] weightedImage

theorem compact_density_integrable (τ c α t₀ a b : ℝ) (ht₀ : 2 ≤ t₀) (hta : t₀ < a)
    (O : Configuration N) (w : CoreCurve N) (k q : ℝ → SpherePhoton N)
    (hk : ∀ t, IsAngularRepresentative F χ hUV e O C t (w.value t) (k t))
    (hq : ∀ t, IsRadiationRepresentative F χ hUV e O t (w.value t) (q t))
    (hs : ∀ t, t ∉ Icc a b → w.ambient t = 0 ∧ w.firstAmbient t = 0) :
    IntegrableOn (fun t => Real.exp (2*τ*weight α t) *
      originalDensity τ c (beta α) (fun s => Real.exp (-2*s))
        w.ambient w.firstAmbient k q t) (Ioi t₀) := by
  have hpos (t : ℝ) (ht : t ∈ Ioi t₀) : 0 < t :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ)<2) (ht₀.trans ht.le)
  have hf : ContinuousOn (weight α) (Ioi t₀) := fun t ht =>
    (weight_hasDerivAt α (hpos t ht)).continuousAt.continuousWithinAt
  have hb : ContinuousOn (beta α) (Ioi t₀) := fun t ht =>
    (beta_hasDerivAt α (hpos t ht)).continuousAt.continuousWithinAt
  have hr : ContinuousOn (fun t : ℝ => Real.exp (-2*t)) (Ioi t₀) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  have hw : Continuous w.ambient := continuous_iff_continuousAt.mpr fun t =>
    (w.ambient_hasDerivAt t).continuousAt
  have hdw : Continuous w.firstAmbient := continuous_iff_continuousAt.mpr fun t =>
    (w.first_hasDerivAt t).continuousAt
  have hK : Continuous (fun t => inner ℝ (w.ambient t) (k t)) :=
    continuous_iff_continuousAt.mpr fun t => (angular_product_rule F χ hUV e O C w k hk t).continuousAt
  have hT : Continuous (fun t => inner ℝ (w.ambient t) (q t)) :=
    continuous_iff_continuousAt.mpr fun t => (radiation_product_rule F χ hUV e O w q hq t).continuousAt
  exact CylinderEstimate.originalDensity_integrable τ c t₀ a b (weight α) (beta α)
    (fun t => Real.exp (-2*t)) w.ambient w.firstAmbient k q hta hf hb hr
    hw.continuousOn hdw.continuousOn hK.continuousOn hT.continuousOn hs

include W

theorem exists_uniform_estimate (α : ℝ) (hα : 0 < α) :
    ∃ t₀ : ℝ, 2 ≤ t₀ ∧ ∀ (τ c : ℝ), 9 ≤ τ → |c| ≤ τ →
      ∀ (O : Configuration N) (w : CoreCurve N) (k q : ℝ → SpherePhoton N),
      (∀ t, IsAngularRepresentative F χ hUV e O C t (w.value t) (k t)) →
      (∀ t, IsRadiationRepresentative F χ hUV e O t (w.value t) (q t)) →
      IntegrationConditions τ c t₀ (weightPrime α) (beta α) (betaPrime α) (betaSecond α)
        (fun t => Real.exp (-2*t)) (angularDerivative F χ hUV e C O (w.exponential τ α))
        (radiationDerivative F χ hUV e O (w.exponential τ α))
        (w.exponential τ α).ambient (w.exponential τ α).firstAmbient (w.exponential τ α).second
        (weightedImage τ α k) (weightedImage τ α q) →
      IntegrableOn (fun t => Real.exp (2*τ*weight α t) *
        originalDensity τ c (beta α) (fun s => Real.exp (-2*s))
          w.ambient w.firstAmbient k q t) (Ioi t₀) →
      (∫ t in Ioi t₀, Real.exp (2*τ*weight α t) *
        originalDensity τ c (beta α) (fun s => Real.exp (-2*s))
          w.ambient w.firstAmbient k q t) ≤
      16 * ∫ t in Ioi t₀, Real.exp (2*τ*weight α t) *
        ‖-w.second t+k t+c^2 • w.ambient t+Real.exp (-2*t) • q t‖^2 := by
  have hex := exists_uniform_coercivity_packed (N := N) F χ hUV e C W α hα
  let t₀ : ℝ := Classical.choose hex
  have ht₀ : 2 ≤ t₀ := (Classical.choose_spec hex).1
  have hcoercive : CoerciveAt (N := N) F χ hUV e C α t₀ := (Classical.choose_spec hex).2
  refine ⟨t₀, ht₀, ?_⟩
  intro τ c hτ hc O w k q hk hq hi hI
  let z := w.exponential τ α
  let kz := weightedImage τ α k
  let qz := weightedImage τ α q
  have hkz (t : ℝ) : IsAngularRepresentative F χ hUV e O C t (z.value t) (kz t) := by
    simpa only [z, kz, weightedImage, CoreCurve.exponential_value] using
      (hk t).scale F χ hUV e O C (smoothExponential τ α t)
  have hqz (t : ℝ) : IsRadiationRepresentative F χ hUV e O t (z.value t) (qz t) := by
    simpa only [z, qz, weightedImage, CoreCurve.exponential_value] using
      (hq t).scale F χ hUV e O (smoothExponential τ α t)
  unfold CoerciveAt at hcoercive
  have h := hcoercive τ c hτ O z kz qz hkz hqz hi
  have hvalues (t : ℝ) (ht : t ∈ Ioi t₀) : 2 ≤ t := ht₀.trans ht.le
  have hm := integral_mono_ae hI (hi.retained_integrable.const_mul 16) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht₂ := hvalues t ht
    have hK := (CenteredSphereAngularField.energy_nonneg F χ hUV e O C
      (z.value t).gradient (z.value t).radiation t).trans_eq ((hkz t).diagonal F χ hUV e O C).symm
    have hT := (CenteredSphereRadiationEnergy.energy_nonneg F χ hUV e O
      (z.value t).radiation t).trans_eq ((hqz t).diagonal F χ hUV e O).symm
    have hp := weightPrime_pos_le_one hα ht₂
    have hb := (beta_pos hα (by linarith : 0<t)).le
    have hd := physical_density_le_retained τ c t (weightPrime α) (beta α)
      (fun s => Real.exp (-2*s)) z.ambient z.firstAmbient z.second kz qz
      (by linarith) hb (Real.exp_pos _).le (abs_le.mpr ⟨by linarith [hp.1], hp.2⟩) hc hK hT
    have he := recoveredDensity_of_values τ c t (weight α) (weightPrime α) (beta α)
      (fun s => Real.exp (-2*s)) w.ambient w.firstAmbient k q z.ambient z.firstAmbient kz qz
      (w.exponential_ambient τ α ht₂) (w.exponential_first τ α ht₂)
      (weightedImage_eq τ α k ht₂) (weightedImage_eq τ α q ht₂)
    exact he.symm.trans_le hd)
  have hsource : (∫ t in Ioi t₀, ‖symmetricPart τ c (weightPrime α) (fun s => Real.exp (-2*s))
      z.ambient z.second kz qz t + skewPart τ (weightPrime α) (beta α) z.ambient z.firstAmbient t‖^2) =
      ∫ t in Ioi t₀, Real.exp (2*τ*weight α t) *
        ‖-w.second t+k t+c^2 • w.ambient t+Real.exp (-2*t) • q t‖^2 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht₂ := hvalues t ht
    exact source_norm_sq_of_values τ c t (weight α) (weightPrime α) (beta α)
      (fun s => Real.exp (-2*s)) w.ambient w.firstAmbient w.second k q
      z.ambient z.firstAmbient z.second kz qz
      (w.exponential_ambient τ α ht₂) (w.exponential_first τ α ht₂)
      (w.exponential_second τ α ht₂)
      (weightedImage_eq τ α k ht₂) (weightedImage_eq τ α q ht₂)
  rw [integral_const_mul] at hm
  exact (hm.trans (mul_le_mul_of_nonneg_left h (by norm_num))).trans_eq
    (congrArg (fun x : ℝ => 16*x) hsource)

end PfHk.PhysicalWeightedCylinder
