import PfHk.PhysicalLocalExternalCoefficients
import PfHk.PauliWeakSquare
import PfHk.PauliLocalEnergy
import PfHk.BufferedCutoffLocality

/-! The local coefficient hypotheses and independent magnetic
truncation used in the Pauli operator-domain argument. -/

noncomputable section
namespace PfHk.PauliLocalDomain

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.SymmetricLift GptLean.ElectronicH1Multiplier
  PfHk.PauliGroundState PfHk.PauliSpin PfHk.PhysicalLocalEnergy
  PfHk.CoordinateCoefficientLocalization PfHk.PauliClassicalCurl
  PfHk.WeylCoreReference PfHk.SmoothCutoffBounds PfHk.PhysicalCutoffCommutator
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
attribute [local irreducible] referenceSubspace inclusion

structure Data {N : ℕ} (O : Configuration N) (ρ : ℝ) where
  orbital : PhysicalLocalExternalCoefficients.Data O ρ
  magnetic : Fin N → Fin 3 → PhysicalSourceCoordinates.Position → ℝ
  exponent : ℝ
  exponent_gt_two : 2 < exponent
  magnetic_memLp : ∀ n k, MemLp (magnetic n k) (ENNReal.ofReal exponent)
    (volume.restrict (Metric.ball (PhysicalSourceCoordinates.split n O).1 ρ))
  weakCurl : ∀ n k, WeakCurlPairOn (Metric.ball (PhysicalSourceCoordinates.split n O).1 ρ)
    (orbital.vectorCoefficient n) (k + 1) (k + 2) (magnetic n k)

variable {N : ℕ} {O : Configuration N} {ρ : ℝ}

/-- The magnetic truncation is independent of the curl of the truncated
vector potential outside the neighborhood under study. -/
def Data.truncatedMagnetic (a : Data O ρ) (n : Fin N) (k : Fin 3) :
    PhysicalSourceCoordinates.Position → ℝ :=
  zeroExtension (PhysicalSourceCoordinates.split n O).1 ρ (a.magnetic n k)

theorem Data.truncatedMagnetic_memLp (a : Data O ρ) (n : Fin N) (k : Fin 3) :
    MemLp (a.truncatedMagnetic n k) (ENNReal.ofReal a.exponent) volume :=
  zeroExtension_memLp _ ρ _ (a.magnetic_memLp n k)

theorem Data.truncatedMagnetic_eq (a : Data O ρ) (hρ : 0 < ρ) (n : Fin N) (k : Fin 3)
    (x : PhysicalSourceCoordinates.Position)
    (hx : x ∈ Metric.ball (PhysicalSourceCoordinates.split n O).1 (ρ / 2)) :
    a.magnetic n k x = a.truncatedMagnetic n k x :=
  (Set.indicator_of_mem (Metric.mem_ball.mpr
    ((Metric.mem_ball.mp hx).trans (by linarith only [hρ]))) (a.magnetic n k)).symm

theorem compact_of_ball_support {r : ℝ}
    (u : Reference (Fin N × Fin 3) (fun _ => 0))
    (hu : ∀ᵐ X ∂volume, X ∉ Metric.ball O r → inclusion (Fin N × Fin 3) (fun _ => 0) u X = 0) :
    CompactlySupportedIn Set.univ u :=
  ⟨Metric.closedBall O r, isCompact_closedBall _ _, Set.subset_univ _,
    hu.mono fun _X hX hnot => hX (fun hx => hnot (Metric.ball_subset_closedBall hx))⟩

theorem coordinate_support_of_ball_support {r R : ℝ} (hr : r ≤ R)
    (u : WaveSpace (Fin N × Fin 3))
    (hu : ∀ᵐ X ∂volume, X ∉ Metric.ball O r → u X = 0) (n : Fin N) :
    SupportedInCoordinate n (Metric.ball (PhysicalSourceCoordinates.split n O).1 R) u :=
  hu.mono fun X hX hnot => hX (fun hx => hnot (Metric.mem_ball.mpr
    ((coordinate_dist_le n X O).trans_lt ((Metric.mem_ball.mp hx).trans_le hr))))

theorem localized_compact (family : BufferedFamily O) {r : ℝ} (hr : 0 < r)
    (z : Ref N) (s : SpinIndex N) :
    CompactlySupportedIn Set.univ (PauliLocalEnergy.localize (family.cutoff r).scalar z s) :=
  compact_of_ball_support _ (localized_supported (fun _ => 0) (family.cutoff r).scalar
    (BufferedCutoffLocality.cutoff_supported family hr) (z s))

theorem localized_coordinate_support (family : BufferedFamily O) {r R : ℝ}
    (hr : 0 < r) (hR : 2 * r ≤ R) (z : Ref N) (n : Fin N) (s : SpinIndex N) :
    SupportedInCoordinate n (Metric.ball (PhysicalSourceCoordinates.split n O).1 R)
      (inclusion (Fin N × Fin 3) (fun _ => 0) (PauliLocalEnergy.localize (family.cutoff r).scalar z s)) :=
  coordinate_support_of_ball_support hR _
    (localized_supported (fun _ => 0) (family.cutoff r).scalar
      (BufferedCutoffLocality.cutoff_supported family hr) (z s)) n

end PfHk.PauliLocalDomain

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
