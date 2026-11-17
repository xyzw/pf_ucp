import GptLean.PhysicalPFConstraintRealization
import GptLean.PhysicalInfraredRemoval

/-!
The physical compactness construction on the same article model as infrared
removal. The Coulomb coefficient is one. The localization identification is
the identity on one-photon momentum space, so its kernels and reference form
are exactly the removal kernels and form. Full photon number is the number
form evaluated on the actual photon marginal in both constructions.
-/

noncomputable section

namespace GptLean.PhysicalAttainmentCompactness

open MeasureTheory PhysicalFock PhysicalNormalTrace PhysicalClosedForms
  PhysicalPolarization PhysicalSobolevRealization PhysicalPhotonLocalizedNumber

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000

attribute [local irreducible] PhysicalPFReference.normalEnergy

variable {N : ℕ} (i : Fin N) (F : Frame) (χ : ArticleCutoff)
  (Sob : StandardHomogeneousSobolev) (BF : StandardSymmetricFockExponential)
  (C : CanonicalSectorCCR photonMeasure) (B : StandardNormalTraceBackground)
  (S : StandardClosedFormBackground) (e : ℝ)
  (Rellich : PhysicalRellichFourier.StandardSupportedHalfRellich)
  (Hardy : StandardFractionalHardy)

/-- The constructed localization and constraint realization use the very same
mixed-state model and full number as the physical infrared-removal theorem. -/
def constraintRealization : PhotonLoss.ConstraintRealization
    (PhysicalPFLocalization.localizationEstimates i (formFactors F χ) rfl
      Sob BF C B S e Rellich Hardy)
    (PhysicalRemoval.model i F χ 1 C B S e)
    (PhysicalRemoval.number F χ 1 C B S e (N := N)) :=
  PhysicalPFLocalization.constraintRealization i (formFactors F χ) rfl
    Sob BF C B S e Rellich Hardy

include Sob BF Rellich Hardy in
/-- Norm closure for converging physical pairs under uniform energy and
full-photon-number bounds. -/
theorem physical_boundedConstraintClosure :
    Closure.BoundedConstraintClosure (PhysicalRemoval.model i F χ 1 C B S e)
      (PhysicalRemoval.number F χ 1 C B S e (N := N)) :=
  (constraintRealization i F χ Sob BF C B S e Rellich Hardy).boundedConstraintClosure

include Sob BF Rellich Hardy in
/-- The fixed-pair photon-loss input required by infrared-repair attainment,
with the original mean-number bound retained. -/
theorem physical_photonLossInput (p : PhysicalPairSpace.Pair) :
    Attainment.PhotonLossInput (PhysicalRemoval.mixedState F χ 1 C B S e (N := N))
      (fun s => (PhysicalRemoval.model i F χ 1 C B S e).density s = p)
      (PhysicalRemoval.model i F χ 1 C B S e).energy
      (PhysicalRemoval.number F χ 1 C B S e (N := N)) :=
  (constraintRealization i F χ Sob BF C B S e Rellich Hardy).photonLossInput p

end GptLean.PhysicalAttainmentCompactness
