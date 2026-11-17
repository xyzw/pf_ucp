import GptLean.PhysicalFockProfileDilation
import GptLean.PhysicalPFLocalizationControl

/-!
The actual kinetic dilation is measured in PF energy plus mass. This
matches the common energy and current control, and its constants follow
from the physical mass, radiation and covariant derivative estimates.
-/

noncomputable section
namespace GptLean.PhysicalPFLocalization

open MeasureTheory Gaussian PhysicalFock PhysicalPFReference PhysicalPFSource PhysicalNormalTrace PhysicalClosedForms
  PhotonLocalization PhotonLocalizationChannel PhotonLocalizationPhysicalKernels SymmetricLift
open PhysicalNormalTrace.StandardNormalTraceBackground
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000
set_option Elab.async false

section Rebase
variable {H X ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [Fintype ι]
  {A : Gaussian.RankOneData H X} {Tr : RemovalState.PositiveTraceData X}
  {kinetic control : RemovalState.PositiveForm Tr} {U : KrausIsometry H}
  {v : H} {charge ε B K : ℝ}

private def rebaseKineticControl
    (s : KineticDilationSource (A := A) (ι := ι) kinetic control U v charge ε B K)
    (control' : RemovalState.PositiveForm Tr) (c B' K' : ℝ)
    (hc : 0 ≤ c) (hvalue : control'.expectation (A.rankOne v) = ENNReal.ofReal c)
    (hscale : 2 * s.radiationNorm + s.massNorm ≤ B' * Real.sqrt c)
    (hmass : s.massNorm ^ 2 ≤ c)
    (hderivative : ∑ i, ‖s.derivative i‖ ≤ K' * Real.sqrt c) :
    KineticDilationSource (A := A) (ι := ι) kinetic control' U v charge ε B' K' where
  control := c
  control_nonneg := hc
  control_eq := hvalue
  derivative := s.derivative
  annihilated := s.annihilated
  created := s.created
  noise := s.noise
  localized := s.localized
  radiationNorm := s.radiationNorm
  massNorm := s.massNorm
  radiationNorm_nonneg := s.radiationNorm_nonneg
  massNorm_nonneg := s.massNorm_nonneg
  annihilation := s.annihilation
  creation := s.creation
  scale_le := hscale
  mass_le := hmass
  derivative_le := hderivative
  noise_le := s.noise_le
  intertwining := s.intertwining
  orthogonality := s.orthogonality
  original_form := s.original_form
  coordinate_form := s.coordinate_form
end Rebase

variable {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  (F : FormFactors photonMeasure (Fin 3)) (hF : F.momentum = Prod.fst)
  (J : Lp ℂ 2 photonMeasure ≃ₗᵢ[ℝ] Z) (Bsob : SobolevMultiplierBackground Z)
  (hmult : ∀ (χ : FieldSpace → ℝ) (_hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (_hc : HasCompactSupport χ)
    (hχm : AEStronglyMeasurable χ (volume : Measure FieldSpace))
    (hb : ∀ᵐ y ∂(volume : Measure FieldSpace), |χ y| ≤ 1) a w,
    physicalRadiationCoordinates.representative J a w →
    physicalRadiationCoordinates.representative J
      (PhotonKernelLocalization.l2Multiplier χ hχm hb a) (Bsob.multiplier χ w))
  (BF : StandardSymmetricFockExponential) (C : CanonicalSectorCCR photonMeasure)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground) (N : ℕ) (e : ℝ)

def physicalControl := currentControl (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N)
  C (PhysicalProfiles.particleKernel F hF J N) (PhysicalProfiles.particleKernel_measurable F hF J N)
  (PhysicalProfiles.kernelBound F hF J) (PhysicalProfiles.particleKernel_bound F hF J N) B S e

def derivativeConstant : ℝ := (Fintype.card (Fin N × Fin 3) : ℝ) * Real.sqrt 2

theorem derivativeConstant_nonneg : 0 ≤ derivativeConstant N := by
  unfold derivativeConstant
  positivity

set_option maxHeartbeats 200000 in
/-- The original physical dilation, with the exact common PF control. -/
def kineticSource (l m : ℕ) (q : PhysicalFreeForm.Reference (Fin N × Fin 3))
    (hsupport : ∀ j : Fin N × Fin 3, ∀ᵐ x ∂volume,
      PhysicalFreeReferenceCore.radiationSource (Fin N × Fin 3) q x ≠ 0 →
        ‖particle x j.1‖ ≤ l) :
    KineticDilationSource (A := (B.realization (FullHilbert N)).rank) (ι := Fin N × Fin 3)
      (PhysicalCovariantKinetic.normalEnergy N C (PhysicalProfiles.particleKernel F hF J N)
        (PhysicalProfiles.particleKernel_measurable F hF J N) (PhysicalProfiles.kernelBound F hF J)
        (PhysicalProfiles.particleKernel_bound F hF J N) e B S)
      (physicalControl F hF J C B S N e)
      (physicalKraus BF N m) (PhysicalFreeForm.inclusion (Fin N × Fin 3) q)
      e (PhysicalProfiles.cutoffError F J Bsob l m) 3 (derivativeConstant N) := by
  let u := PhysicalCoulombReferenceCore.attach N 1 zero_le_one q
  let R := (physicalControl F hF J C B S N e).expectation
    ((B.realization (FullHilbert N)).rank.rankOne
      (inclusion (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N) u))
  let s := PhysicalProfiles.kineticDilation F hF J Bsob hmult BF C B S N e l m q hsupport
  have hvalue : inclusion (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N) u =
      PhysicalFreeForm.inclusion (Fin N × Fin 3) q := rfl
  have hcontrol : (physicalControl F hF J C B S N e).expectation
      ((B.realization (FullHilbert N)).rank.rankOne
        (PhysicalFreeForm.inclusion (Fin N × Fin 3) q)) = R :=
    (congrArg (fun v : FullHilbert N => (physicalControl F hF J C B S N e).expectation
      ((B.realization (FullHilbert N)).rank.rankOne v)) hvalue).symm
  have hf : R < ⊤ := control_rankOne_finite (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N)
    C (PhysicalProfiles.particleKernel F hF J N) (PhysicalProfiles.particleKernel_measurable F hF J N)
    (PhysicalProfiles.kernelBound F hF J) (PhysicalProfiles.particleKernel_bound F hF J N) B S e u
  have hm := norm_le_sqrt_control (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N)
    C (PhysicalProfiles.particleKernel F hF J N) (PhysicalProfiles.particleKernel_measurable F hF J N)
    (PhysicalProfiles.kernelBound F hF J) (PhysicalProfiles.particleKernel_bound F hF J N) B S e
    (inclusion (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N) u) hf
  have hr := radiation_norm_le_sqrt_control (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N)
    C (PhysicalProfiles.particleKernel F hF J N) (PhysicalProfiles.particleKernel_measurable F hF J N)
    (PhysicalProfiles.kernelBound F hF J) (PhysicalProfiles.particleKernel_bound F hF J N) B S e u
  have hmass : s.massNorm = ‖PhysicalFreeForm.inclusion (Fin N × Fin 3) q‖ := rfl
  have hradiation : s.radiationNorm =
      ‖radiation (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N) u‖ := rfl
  have hm' : s.massNorm ≤ Real.sqrt R.toReal :=
    hmass.trans_le ((congrArg (fun v : FullHilbert N => ‖v‖) hvalue).symm.trans_le hm)
  have hr' : s.radiationNorm ≤ Real.sqrt R.toReal := hradiation.trans_le hr
  have hd (i : Fin N × Fin 3) : s.derivative i =
      covariant (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N)
        C (PhysicalProfiles.particleKernel F hF J N) (PhysicalProfiles.particleKernel_measurable F hF J N)
        (PhysicalProfiles.kernelBound F hF J) (PhysicalProfiles.particleKernel_bound F hF J N) e i u := rfl
  apply rebaseKineticControl s (physicalControl F hF J C B S N e) R.toReal 3
    (derivativeConstant N) ENNReal.toReal_nonneg
    (hcontrol.trans (ENNReal.ofReal_toReal hf.ne).symm)
  · linarith only [hm', hr']
  · exact (pow_le_pow_left₀ s.massNorm_nonneg hm' 2).trans_eq
      (Real.sq_sqrt ENNReal.toReal_nonneg)
  · exact (Finset.sum_congr rfl fun i _ => congrArg (fun v : FullHilbert N => ‖v‖) (hd i)).trans_le
      (covariant_sum_le_control (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N)
      C (PhysicalProfiles.particleKernel F hF J N) (PhysicalProfiles.particleKernel_measurable F hF J N)
      (PhysicalProfiles.kernelBound F hF J) (PhysicalProfiles.particleKernel_bound F hF J N) B S e u)

end GptLean.PhysicalPFLocalization
