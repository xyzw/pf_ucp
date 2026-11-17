import PfHk.PauliGroundState
import PfHk.PauliCurrent

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

noncomputable section
namespace PfHk.PauliGroundState
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000
open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPairSpace GptLean.PhysicalPolarization PfHk.CenteredPhysicalReference
variable {N : ℕ} (C : CanonicalSectorCCR photonMeasure) (e : ℝ) (F : Frame) (χ : ArticleCutoff)

def covariants (u : Ref N) : PauliCurrent.Derivatives (N := N) :=
  fun q s => covariant (Fin N × Fin 3) (fun _ => 0) C (profile F χ 0)
    (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e q (u s)

/-- Spin-summed density and the actual Pauli kinetic current. -/
def data (u : Ref N) : Pair :=
  PauliCurrent.pair (N := N) (fun s => electronic (Fin N × Fin 3) (fun _ => 0) (u s))
    (covariants (N := N) C e F χ u)

theorem data_density_eq (hN : 0 < N) (u : Ref N) :
    PhysicalPairSpace.densityL1 (data (N := N) C e F χ u) = PauliReference.density (N := N) u :=
  PauliCurrent.density_eq (N := N) hN _ _

theorem data_density_pos_ae (hN : 0 < N) (u : Ref N)
    (hu : ∀ᵐ X ∂volume, PauliReference.wave (N := N) u X ≠ 0) :
    ∀ᵐ x ∂volume, 0 < PhysicalPairSpace.densityL1 (data (N := N) C e F χ u) x := by
  rw [data_density_eq (N := N) C e F χ hN u]
  exact PauliReference.density_pos_ae (N := N) hN u hu

end PfHk.PauliGroundState

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
