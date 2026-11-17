import PfHk.PauliCarlemanLocalSource

/-! The fixed exterior source cutoff does not change the L2 source on
any of the nearby target balls. No weighted integrability is required. -/

noncomputable section
namespace PfHk.PauliCarlemanLocalSource

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.SymmetricLift PfHk.SmoothCutoffBounds

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
attribute [local irreducible] referenceSubspace inclusion

theorem cutoff_source_ae_on_target {N : ℕ} {O O' : Configuration N} {ρ r R : ℝ}
    (hρ : 0 < ρ) (family : BufferedFamily O)
    (hO : O' ∈ Metric.ball O r) (hR : R ≤ r) (hr : r ≤ ρ / 16)
    (f : WaveSpace (Fin N × Fin 3)) :
    (((family.cutoff (ρ / 8)).scalar.multiplier f) : Configuration N → PhotonFock) =ᵐ[
      volume.restrict (Metric.ball O' R)] f := by
  let η := (family.cutoff (ρ / 8)).scalar
  have hrep : (η.multiplier f : Configuration N → PhotonFock) =ᵐ[volume]
      fun X => η.weight X • f X :=
    PhotonLocalization.realL2Multiplier_apply η.weight
      η.differentiable.continuous.aestronglyMeasurable η.bound (ae_of_all _ η.bounded) f
  have hone := cutoff_one_on_target hρ family hO hR hr
  filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae hrep] with X hX hrepX
  exact hrepX.trans ((congrArg (fun z : ℝ => z • f X) (hone X hX)).trans (one_smul _ _))

end PfHk.PauliCarlemanLocalSource

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
