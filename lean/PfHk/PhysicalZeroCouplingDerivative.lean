import PfHk.PhysicalOneParticleState

/-! Zero-coupling covariant derivatives equal the ordinary momentum. -/

noncomputable section
namespace PfHk.PhysicalOneParticleEnergy

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalGroundState GptLean.PhysicalPolarization
  GptLean.PhysicalNormalTrace GptLean.PhysicalClosedForms
  GptLean.PhysicalPairDuality PfHk.PhysicalOneParticleState

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000

local instance derivativePhotonDirectInner : InnerProductSpace ℂ PhotonFock :=
  { (inferInstance : InnerProductSpace ℂ PhotonFock) with
    toNormedSpace := (inferInstance : NormedSpace ℂ PhotonFock) }

attribute [local irreducible] inclusion covariant ordinary radiation potential
  PhysicalPFReference.referenceSubspace ElectronicH1Complex.complexWeakGraph
  ElectronicH1Complex.derivative ElectronicH1Complex.value

private theorem covariant_zero_generic
    {I : Type} [Fintype I] [DecidableEq I] (V : Position I → ℝ)
    (C : CanonicalSectorCCR photonMeasure)
    (κ : I → Position I → WeightedPhotonKernel)
    (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
    (M : ℝ) (hb : ∀ i, ∀ᵐ X ∂volume, ‖κ i X‖ ≤ M)
    (u : Reference I V) (q : I) :
    covariant I V C κ hκ M hb 0 q u = (-Complex.I) • ordinary I V q u :=
  (covariant_apply I V C κ hκ M hb 0 q u).trans
    (by simp only [Complex.ofReal_zero, zero_smul, sub_zero])

variable (F : Frame) (χ : ArticleCutoff)
  (C : CanonicalSectorCCR photonMeasure) (B : StandardNormalTraceBackground)
  (S : StandardClosedFormBackground)

set_option hygiene false in
local notation "Vp" => PhysicalRemoval.potential 1 1
set_option hygiene false in
local notation "Kf" => PhysicalProfiles.momentumKernel (formFactors F χ) rfl
  (LinearIsometryEquiv.refl ℝ _)
set_option hygiene false in
local notation "hKf" => PhysicalProfiles.momentumKernel_continuous (formFactors F χ) rfl
  (LinearIsometryEquiv.refl ℝ _)
set_option hygiene false in
local notation "MK" => PhysicalRemovalKernels.bound F χ
set_option hygiene false in
local notation "hMK" => PhysicalProfiles.momentumKernel_bound (formFactors F χ) rfl
  (LinearIsometryEquiv.refl ℝ _)
set_option hygiene false in
local notation "κP" => PhysicalPFParticle.particleKernel (N := 1) Kf
set_option hygiene false in
local notation "hκP" => PhysicalPFParticle.particleKernel_measurable (N := 1) Kf hKf
set_option hygiene false in
local notation "hbP" => PhysicalPFParticle.particleKernel_bound (N := 1) Kf MK hMK

/-- At zero coupling the field kernel disappears from every covariant
derivative, with the usual momentum sign convention. -/
theorem covariant_zero (u : Ref) (q : Index) :
    covariant Index (fun _ => 0) C κP hκP MK hbP 0 q u =
      (-Complex.I) • ordinary Index (fun _ => 0) q u :=
  covariant_zero_generic (fun _ => 0) C κP hκP MK hbP u q


end PfHk.PhysicalOneParticleEnergy
