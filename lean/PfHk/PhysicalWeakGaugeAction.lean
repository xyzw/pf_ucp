import PfHk.WeakGaugeStates
import GptLean.PhysicalGroundState
import PfHk.WeakGaugePotentials

/-! The full weak gauge action on the actual physical pure states,
including inverse, density, and internal-energy covariance. -/

noncomputable section
namespace PfHk.PhysicalWeakGauge

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalGroundState GptLean.PhysicalPairDuality GptLean.PhysicalPolarization
  GptLean.PhysicalNormalTrace GptLean.PhysicalClosedForms GptLean.TransformationsGauge

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff)
  (C : CanonicalSectorCCR photonMeasure) (B : StandardNormalTraceBackground)
  (S : StandardClosedFormBackground) (e : ℝ)

set_option hygiene false in
local notation "Vp" => PhysicalRemoval.potential N 1
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

def gaugeState (G : WeakSpatialGauge) (p : State F χ C B S e (N := N)) :
    State F χ C B S e (N := N) :=
  WeakGaugeStates.gaugeState Vp C Kf hKf MK hMK B S e G p

theorem gaugeState_value (G : WeakSpatialGauge) (p : State F χ C B S e (N := N)) :
    (gaugeState F χ C B S e G p).val = G.wavePhase p.val := rfl

theorem neg_gaugeState (G : WeakSpatialGauge) (p : State F χ C B S e (N := N)) :
    gaugeState F χ C B S e G.neg (gaugeState F χ C B S e G p) = p :=
  WeakGaugeStates.neg_gaugeState Vp C Kf hKf MK hMK B S e G p

theorem gaugeState_neg (G : WeakSpatialGauge) (p : State F χ C B S e (N := N)) :
    gaugeState F χ C B S e G (gaugeState F χ C B S e G.neg p) = p :=
  WeakGaugeStates.gaugeState_neg Vp C Kf hKf MK hMK B S e G p

theorem gaugeState_surjective (G : WeakSpatialGauge) :
    Function.Surjective (gaugeState F χ C B S e G (N := N)) :=
  WeakGaugeStates.gaugeState_surjective Vp C Kf hKf MK hMK B S e G

theorem density_gaugeState (i : Fin N) (G : WeakSpatialGauge)
    (p : State F χ C B S e (N := N)) :
    (model i F χ C B S e).density (gaugeState F χ C B S e G p) =
      G.shiftPair ((model i F χ C B S e).density p) :=
  WeakGaugeStates.density_gaugeState Vp C Kf hKf MK hMK B S e i G p

theorem internalEnergy_gaugeState (i : Fin N) (G : WeakSpatialGauge)
    (p : State F χ C B S e (N := N)) :
    (model i F χ C B S e).energy (gaugeState F χ C B S e G p) =
    (model i F χ C B S e).energy p +
      G.energyShift ((model i F χ C B S e).density p) :=
  WeakGaugeStates.internalEnergy_gaugeState Vp C Kf hKf MK hMK B S e i G p

end PfHk.PhysicalWeakGauge
