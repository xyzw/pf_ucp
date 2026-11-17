import PfHk.PauliCarlemanCutoffSource
import PfHk.PauliCarlemanQuantumShift

/-! The actual orbital L2 source has the coupled Pauli perturbation
identity on the target ball. Every representative equality follows from
the L2 operations and the fixed exterior cutoff. -/

noncomputable section
namespace PfHk.PauliCarlemanSourceIdentity

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.SymmetricLift
  PfHk.PauliSpin PfHk.PhysicalLocalEnergy PfHk.SmoothCutoffBounds
  PfHk.PhysicalFieldRegularity

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 40000

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

private theorem four_term_ae {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H]
    {μ : Measure X} (a b c d : Lp H 2 μ) :
    ((a + b - c - d : Lp H 2 μ) : X → H) =ᵐ[μ]
      fun x => a x + b x - c x - d x := by
  filter_upwards [Lp.coeFn_sub (a + b - c) d, Lp.coeFn_sub (a + b) c,
    Lp.coeFn_add a b] with x h₁ h₂ h₃
  exact h₁.trans ((congrArg (fun z : H => z - d x) h₂).trans
    (congrArg (fun z : H => z - c x - d x) h₃))

private theorem source_pointwise {H : Type*} [AddCommGroup H]
    {g a f v v' b q q' : H} (hg : g = a + v - b - q)
    (ha : a = f) (hv : v = v') (hq : q' = q - v') :
    g = f - (b + q') := by
  rw [hg, ha, hv, hq]
  abel

variable {N : ℕ} {O₀ : Configuration N}
  (F : Frame) (χ : ArticleCutoff) (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
  (hUV : CarlemanUV χ)
  (B : Fin N → Fin 3 → PhysicalSourceCoordinates.Position → ℝ)
  (family : BufferedFamily O₀) (ρ E : ℝ) (u : PauliReference.Ref N)
  (hB : ∀ n k s, HasMultiplier (CoordinateSobolev.coordinateCoefficient n (B n k))
    (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)))
  (f : SpinIndex N → WaveSpace (Fin N × Fin 3))

attribute [local irreducible] referenceSubspace inclusion
  PauliMagneticClassicalOperator.zeeman PauliMagneticOperator.quantum

def orbitalSource (s : SpinIndex N) : WaveSpace (Fin N × Fin 3) :=
  (family.cutoff (ρ / 8)).scalar.multiplier (f s) +
    (E : ℂ) • inclusion (Fin N × Fin 3) (fun _ => 0) (u s) -
    PauliMagneticClassicalOperator.zeeman B u hB s -
    PauliMagneticOperator.quantum F χ hUV C e u s

theorem orbitalSource_ae_on_target (hρ : 0 < ρ)
    {O : Configuration N} {r R : ℝ} (hO : O ∈ Metric.ball O₀ r)
    (hR : R ≤ r) (hr : r ≤ ρ / 16) (s : SpinIndex N) :
    orbitalSource F χ C e hUV B family ρ E u hB f s =ᵐ[
      volume.restrict (Metric.ball O R)] fun X =>
      f s X - (PauliMagneticClassicalOperator.zeeman B u hB s X +
        PauliCarlemanQuantumShift.shifted F χ C e hUV E u s X) := by
  have hrep : orbitalSource F χ C e hUV B family ρ E u hB f s =ᵐ[volume]
      fun X => (family.cutoff (ρ / 8)).scalar.multiplier (f s) X +
        ((E : ℂ) • inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) X -
        PauliMagneticClassicalOperator.zeeman B u hB s X -
        PauliMagneticOperator.quantum F χ hUV C e u s X :=
    four_term_ae ((family.cutoff (ρ / 8)).scalar.multiplier (f s))
      ((E : ℂ) • inclusion (Fin N × Fin 3) (fun _ => 0) (u s))
      (PauliMagneticClassicalOperator.zeeman B u hB s)
      (PauliMagneticOperator.quantum F χ hUV C e u s)
  have hcut := PauliCarlemanLocalSource.cutoff_source_ae_on_target hρ family hO hR hr (f s)
  have hsmul := Lp.coeFn_smul (E : ℂ) (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))
  have hshift := PauliCarlemanQuantumShift.shifted_ae F χ C e hUV E u s
  filter_upwards [ae_restrict_of_ae hrep, hcut, ae_restrict_of_ae hsmul,
    ae_restrict_of_ae hshift] with X hg hc hm hq
  exact source_pointwise hg hc hm hq

end PfHk.PauliCarlemanSourceIdentity

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
