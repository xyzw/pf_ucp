import GptLean.AppendixAGaugeForm

/-! The full weak gauge acts bijectively on the actual normalized fermionic
finite-energy pure states. Energy and density transformations are derived
from the existing reference-domain construction. -/

noncomputable section
namespace PfHk.WeakGaugeStates

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.SymmetricLift GptLean.PhysicalPairSpace GptLean.PhysicalNormalTrace
  GptLean.PhysicalClosedForms GptLean.TransformationsGauge
  GptLean.TransformationsPureStates

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 200000

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

variable {N : ℕ} (V : PhysicalPFReference.Position (Fin N × Fin 3) → ℝ)
  (C : CanonicalSectorCCR photonMeasure)
  (K : Fin 3 × Gaussian.FieldSpace → WeightedPhotonKernel) (hK : Continuous K)
  (M : ℝ) (hM : ∀ z, ‖K z‖ ≤ M)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground) (e : ℝ)

theorem gauge_reference_exists (G : WeakSpatialGauge)
    (w : WaveSpace (Fin N × Fin 3))
    (hw : ∃ u : Reference (Fin N × Fin 3) V, inclusion (Fin N × Fin 3) V u = w) :
    ∃ u : Reference (Fin N × Fin 3) V, inclusion (Fin N × Fin 3) V u = G.wavePhase w :=
  hw.elim fun u hu => ⟨G.gaugeReference V u,
    (G.inclusion_gaugeReference V u).trans (congrArg G.wavePhase hu)⟩

def gaugeState (G : WeakSpatialGauge) (p : PureState V C K hK M hM B S e) :
    PureState V C K hK M hM B S e :=
  ofVector V C K hK M hM B S e (G.wavePhase p.val)
    ((G.wavePhase.norm_map p.val).trans p.property.1)
    (G.wavePhase_mem_fermionic (pure_fermionic V C K hK M hM B S e p))
    (gauge_reference_exists V G p.val (pure_reference V C K hK M hM B S e p))

theorem gaugeState_value (G : WeakSpatialGauge) (p : PureState V C K hK M hM B S e) :
    (gaugeState V C K hK M hM B S e G p).val = G.wavePhase p.val := rfl

theorem neg_gaugeState (G : WeakSpatialGauge) (p : PureState V C K hK M hM B S e) :
    gaugeState V C K hK M hM B S e G.neg (gaugeState V C K hK M hM B S e G p) = p :=
  Subtype.ext (G.wavePhase_neg p.val)

theorem gaugeState_neg (G : WeakSpatialGauge) (p : PureState V C K hK M hM B S e) :
    gaugeState V C K hK M hM B S e G (gaugeState V C K hK M hM B S e G.neg p) = p :=
  Subtype.ext (G.wavePhase_neg_left p.val)

theorem gaugeState_surjective (G : WeakSpatialGauge) :
    Function.Surjective (gaugeState V C K hK M hM B S e G) :=
  fun p => ⟨gaugeState V C K hK M hM B S e G.neg p,
    gaugeState_neg V C K hK M hM B S e G p⟩

theorem density_gaugeState (i : Fin N) (G : WeakSpatialGauge)
    (p : PureState V C K hK M hM B S e) :
    (pureModel V C K hK M hM B S e i).density
      (gaugeState V C K hK M hM B S e G p) =
        G.shiftPair ((pureModel V C K hK M hM B S e i).density p) := by
  obtain ⟨u, hu⟩ := pure_reference V C K hK M hM B S e p
  have hv : inclusion (Fin N × Fin 3) V (G.gaugeReference V u) =
      (gaugeState V C K hK M hM B S e G p).val :=
    (G.inclusion_gaugeReference V u).trans (congrArg G.wavePhase hu)
  exact (pure_density V C K hK M hM B S e i _ _ hv).trans
    ((G.pair_gauge V C K hK M hM e i u).trans
      (congrArg G.shiftPair (pure_density V C K hK M hM B S e i p u hu).symm))

theorem internalEnergy_gaugeState (i : Fin N) (G : WeakSpatialGauge)
    (p : PureState V C K hK M hM B S e) :
    (pureModel V C K hK M hM B S e i).energy
      (gaugeState V C K hK M hM B S e G p) =
    (pureModel V C K hK M hM B S e i).energy p +
      G.energyShift ((pureModel V C K hK M hM B S e i).density p) := by
  obtain ⟨u, hu⟩ := pure_reference V C K hK M hM B S e p
  have hv : inclusion (Fin N × Fin 3) V (G.gaugeReference V u) =
      (gaugeState V C K hK M hM B S e G p).val :=
    (G.inclusion_gaugeReference V u).trans (congrArg G.wavePhase hu)
  have hf : inclusion (Fin N × Fin 3) V u ∈
      PhysicalElectronicFermions.fermionicSubspace N PhotonFock :=
    (congrArg (fun w => w ∈ PhysicalElectronicFermions.fermionicSubspace N PhotonFock)
      hu).mpr (pure_fermionic V C K hK M hM B S e p)
  exact (pure_energy V C K hK M hM B S e i _ _ hv).trans
    ((G.energy_gauge V C K hK M hM e i u hf).trans
      (congrArg₂ (· + ·) (pure_energy V C K hK M hM B S e i p u hu).symm
        (congrArg G.energyShift (pure_density V C K hK M hM B S e i p u hu).symm)))

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

end PfHk.WeakGaugeStates
