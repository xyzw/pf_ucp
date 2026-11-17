import PfHk.C1ReferenceForm
import PfHk.CenteredRadialGaugePolar

/-! The actual translated physical profile in the existing free PF form.
The center changes the evaluation point of every electronic kernel. It
does not assert any photon translation symmetry. -/

noncomputable section
namespace PfHk.CenteredPhysicalReference

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.PhysicalNonattainmentFluxKernel GptLean.SymmetricLift
  GptLean.Representability Gaussian PfHk.PhysicalFieldRegularity
open scoped ENNReal InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 300000
local instance centeredReferencePhotonRealInner : InnerProductSpace ℝ PhotonFock := InnerProductSpace.rclikeToReal ℂ _
attribute [local irreducible] kernelField

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (O : Configuration N)

def profile (j : Fin N × Fin 3) (X : Configuration N) : WeightedPhotonKernel :=
  physicalKernel F χ j.2 (particle (O + X) j.1)

def profileBound : ℝ :=
  PhysicalProfiles.kernelBound (formFactors F χ) rfl (LinearIsometryEquiv.refl ℝ _)

theorem profile_continuous (j : Fin N × Fin 3) : Continuous (profile F χ O j) :=
  (physicalKernel_continuous F χ j.2).comp
    ((particleLinear j.1).continuous_of_finiteDimensional.comp (continuous_const.add continuous_id))

theorem profile_measurable (j : Fin N × Fin 3) :
    AEStronglyMeasurable (profile F χ O j) volume := (profile_continuous F χ O j).aestronglyMeasurable

theorem profile_bound (j : Fin N × Fin 3) :
    ∀ᵐ X ∂volume, ‖profile F χ O j X‖ ≤ profileBound F χ :=
  ae_of_all _ fun X => PhysicalProfiles.momentumKernel_bound (formFactors F χ) rfl
    (LinearIsometryEquiv.refl ℝ _) (j.2, particle (O + X) j.1)

theorem couplingKernel_eq (e : ℝ) (j : Fin N × Fin 3) (X : Configuration N) :
    CenteredRadialGauge.couplingKernel F χ e O j X = (-e) • profile F χ O j X := rfl

theorem covariantFunction_eq (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
    (q : Configuration N → RadiationGraphSpace) (j : Fin N × Fin 3) (X : Configuration N) :
    C1ReferenceCore.covariantFunction C (profile F χ O) e q j X =
      CenteredRadialGauge.coreCovariant F χ e O C q j X := by
  have h := congrArg (fun L : RadiationGraphSpace →L[ℂ] PhotonFock => L (q X))
    ((kernelFieldMap C).map_smul (-e) (profile F χ O j X))
  change kernelField C ((-e) • profile F χ O j X) (q X) =
    (-e) • kernelField C (profile F χ O j X) (q X) at h
  unfold C1ReferenceCore.covariantFunction CenteredRadialGauge.coreCovariant
  rw [couplingKernel_eq, h]
  simp only [Complex.coe_smul, Complex.ofReal_neg, neg_smul, sub_eq_add_neg]
  rfl

def physicalFormDensity (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
    (q p : Configuration N → RadiationGraphSpace) (X : Configuration N) : ℝ :=
  (1 / 2 : ℝ) * ∑ j, inner ℝ (CenteredRadialGauge.coreCovariant F χ e O C q j X)
    (CenteredRadialGauge.coreCovariant F χ e O C p j X) +
      inner ℝ (radiationGraphDerivative (q X)) (radiationGraphDerivative (p X))

/-- The physical form on the concrete free Reference core has the
pointwise density used by the proved radial-gauge substitution. -/
theorem form_eq_integral (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
    (q p : Configuration N → RadiationGraphSpace) (hq : MemLp q 2 volume) (hp : MemLp p 2 volume)
    (hfq : ContDiff ℝ (1 : ℕ∞) (C1ReferenceCore.valueFunction q))
    (hfp : ContDiff ℝ (1 : ℕ∞) (C1ReferenceCore.valueFunction p))
    (hsq : HasCompactSupport (C1ReferenceCore.valueFunction q))
    (hsp : HasCompactSupport (C1ReferenceCore.valueFunction p)) :
    (PhysicalLocalEnergy.form (fun _ => 0) C (profile F χ O) (profile_measurable F χ O)
      (profileBound F χ) (profile_bound F χ O) e
        (C1ReferenceCore.reference q hq hfq hsq) (C1ReferenceCore.reference p hp hfp hsp)).re =
      ∫ X, physicalFormDensity F χ O C e q p X := by
  rw [C1ReferenceCore.form_eq_integral]
  apply integral_congr_ae
  apply ae_of_all
  intro X
  simp only [C1ReferenceCore.formDensity, physicalFormDensity, covariantFunction_eq]

end PfHk.CenteredPhysicalReference
