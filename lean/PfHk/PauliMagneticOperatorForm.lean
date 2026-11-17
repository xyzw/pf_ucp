import PfHk.PhysicalExternalCoefficients
import PfHk.PauliSquareForm

/-! The actual global orbital and magnetic form sum, defined first on
reference spinors, with its weak L2 source relation. -/
noncomputable section
namespace PfHk.PauliMagneticOperatorRealization
open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.SymmetricLift
  PfHk.PhysicalLocalEnergy PfHk.PhysicalFieldRegularity PfHk.PauliSpin
open scoped InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
attribute [local irreducible] inclusion referenceSubspace PauliMagneticOperator.quantum

variable {N : ℕ}
  (a : PhysicalExternalCoefficients.Data N)
  (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Configuration N → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)
  (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ)
  (B : Fin N → Fin 3 → GptLean.PhysicalSourceCoordinates.Position → ℝ)

/-- The global form sum keeps the classical magnetic coefficient as a
form on H1, independently of any comparison-domain source realization. -/
def form (z u : PauliReference.Ref N)
    (hz : PauliGroundState.Domain a.vector a.positive a.negative z)
    (hu : PauliGroundState.Domain a.vector a.positive a.negative u) : ℂ :=
  PauliOrbitalForm.form C κ hκ M hbound e a.vector a.positive a.negative z u hz hu +
    PauliSquareForm.classicalForm B z u +
    ∑ s, inner ℂ (inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
      (PauliMagneticOperator.quantum F χ hUV C e u s)

def IsOperatorPair (u : PauliReference.Ref N)
    (hu : PauliGroundState.Domain a.vector a.positive a.negative u)
    (f : SpinIndex N → WaveSpace (Fin N × Fin 3)) : Prop :=
  ∀ z hz, form a C κ hκ M hbound e F χ hUV B z u hz hu =
    ∑ s, inner ℂ (inclusion (Fin N × Fin 3) (fun _ => 0) (z s)) (f s)


end PfHk.PauliMagneticOperatorRealization
attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
