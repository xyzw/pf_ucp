import PfHk.PhysicalWeakGaugeAction
import PfHk.WeakGaugeEnergy

/-! Weak spatial gauges act on the article's actual physical pure states.
The shifted Hamiltonian energy is invariant, and the action transports
variational ground states in both directions. -/

noncomputable section
namespace PfHk.PhysicalWeakGauge

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalGroundState GptLean.PhysicalPairDuality GptLean.PhysicalPolarization
  GptLean.PhysicalNormalTrace GptLean.PhysicalClosedForms GptLean.TransformationsGauge
  PfHk.PhysicalDiamagneticPotential

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff)
  (C : CanonicalSectorCCR photonMeasure) (B : StandardNormalTraceBackground)
  (S : StandardClosedFormBackground) (e : ℝ)

theorem energy_gaugeState (i : Fin N) (G : WeakSpatialGauge)
    (v : ScalarPotential) (A : VectorPotential) (p : State F χ C B S e (N := N)) :
    shiftedEnergy i F χ C B S e (shifted v (G.gaugeVector A))
      (gaugeState F χ C B S e G p) =
    shiftedEnergy i F χ C B S e (shifted v A) p := by
  exact (congrArg₂ (· + ·) (internalEnergy_gaugeState F χ C B S e i G p)
    (congrArg (pairPotential (shifted v (G.gaugeVector A)))
      (density_gaugeState F χ C B S e i G p))).trans
    (WeakGaugeEnergy.gauge_shifted_pairEnergy G v A (G.gaugeVector A)
      ((model i F χ C B S e).energy p) ((model i F χ C B S e).density p)
      (G.coeFn_gaugeVector A))

theorem groundState_gauge (i : Fin N) (G : WeakSpatialGauge)
    (v : ScalarPotential) (A : VectorPotential) (p : State F χ C B S e (N := N))
    (hp : IsGroundState i F χ C B S e (shifted v A) p) :
    IsGroundState i F χ C B S e (shifted v (G.gaugeVector A))
      (gaugeState F χ C B S e G p) := by
  intro q
  obtain ⟨r, rfl⟩ := gaugeState_surjective F χ C B S e G q
  exact (energy_gaugeState F χ C B S e i G v A p).trans_le
    ((hp r).trans_eq (energy_gaugeState F χ C B S e i G v A r).symm)

theorem groundState_gauge_iff (i : Fin N) (G : WeakSpatialGauge)
    (v : ScalarPotential) (A : VectorPotential) (p : State F χ C B S e (N := N)) :
    IsGroundState i F χ C B S e (shifted v (G.gaugeVector A))
      (gaugeState F χ C B S e G p) ↔
    IsGroundState i F χ C B S e (shifted v A) p := by
  constructor
  · intro hp q
    exact (energy_gaugeState F χ C B S e i G v A p).symm.trans_le
      ((hp (gaugeState F χ C B S e G q)).trans_eq
        (energy_gaugeState F χ C B S e i G v A q))
  · exact groundState_gauge F χ C B S e i G v A p

end PfHk.PhysicalWeakGauge
