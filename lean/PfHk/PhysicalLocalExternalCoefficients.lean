import PfHk.PhysicalExternalCoefficients
import PfHk.SmoothVectorTruncation
import PfHk.PhysicalCoefficientLocality

/-! Locally Lp external coefficients admit one fixed global truncation
for all sufficiently small balls near a configuration. The vector field
is cut off smoothly and its divergence includes the cutoff derivative. -/

noncomputable section
namespace PfHk.PhysicalLocalExternalCoefficients

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.SymmetricLift PfHk.CoordinateSobolev PfHk.PhysicalLocalEnergy
  PfHk.FriedrichsDivergenceBackground PfHk.CoordinateCoefficientLocalization
  PfHk.PhysicalCoefficientLocality
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

abbrev ElectronicPosition := GptLean.PhysicalSourceCoordinates.Position

structure Data {N : ℕ} (O : Configuration N) (ρ : ℝ) where
  vectorCoefficient : Fin N → Fin 3 → ElectronicPosition → ℝ
  divergenceCoefficient : Fin N → ElectronicPosition → ℝ
  scalarCoefficient : Fin N → ElectronicPosition → ℝ
  boundedCoefficient : Configuration N → ℝ
  divergenceExponent : ℝ
  scalarExponent : ℝ
  divergenceExponent_gt_two : 2 < divergenceExponent
  scalarExponent_gt_two : 2 < scalarExponent
  vector_memLp : ∀ n i, MemLp (vectorCoefficient n i) 6
    (volume.restrict (Metric.ball (GptLean.PhysicalSourceCoordinates.split n O).1 ρ))
  divergence_memLp : ∀ n, MemLp (divergenceCoefficient n) (ENNReal.ofReal divergenceExponent)
    (volume.restrict (Metric.ball (GptLean.PhysicalSourceCoordinates.split n O).1 ρ))
  scalar_memLp : ∀ n, MemLp (scalarCoefficient n) (ENNReal.ofReal scalarExponent)
    (volume.restrict (Metric.ball (GptLean.PhysicalSourceCoordinates.split n O).1 ρ))
  bounded_memLp : MemLp boundedCoefficient ∞ (volume.restrict (Metric.ball O ρ))
  weakDivergence : ∀ n, WeakDivergenceOn
    (Metric.ball (GptLean.PhysicalSourceCoordinates.split n O).1 ρ)
    (vectorCoefficient n) (divergenceCoefficient n)

variable {N : ℕ} {O : Configuration N} {ρ : ℝ}

def Data.vector (a : Data O ρ) : (Fin N × Fin 3) → Configuration N → ℝ :=
  configurationVector a.vectorCoefficient

def Data.scalar (a : Data O ρ) (x : Configuration N) : ℝ :=
  (∑ n, coordinateCoefficient n (a.scalarCoefficient n) x) + a.boundedCoefficient x

def Data.positive (a : Data O ρ) : Configuration N → ℝ :=
  SignedScalarMultiplier.positiveAmplitude a.scalar

def Data.negative (a : Data O ρ) : Configuration N → ℝ :=
  SignedScalarMultiplier.negativeAmplitude a.scalar

def Data.truncated (a : Data O ρ) (hρ : 0 < ρ) : PhysicalExternalCoefficients.Data N where
  vectorCoefficient := fun n => truncatedVector
    (SmoothVectorTruncation.cutoff (GptLean.PhysicalSourceCoordinates.split n O).1 ρ hρ)
    (a.vectorCoefficient n)
  divergenceCoefficient := fun n => truncatedDivergence
    (SmoothVectorTruncation.cutoff (GptLean.PhysicalSourceCoordinates.split n O).1 ρ hρ)
    (a.vectorCoefficient n) (a.divergenceCoefficient n)
  scalarCoefficient := fun n => zeroExtension (GptLean.PhysicalSourceCoordinates.split n O).1 ρ
    (a.scalarCoefficient n)
  boundedCoefficient := (Metric.ball O ρ).indicator a.boundedCoefficient
  divergenceExponent := min a.divergenceExponent 6
  scalarExponent := a.scalarExponent
  divergenceExponent_gt_two := SmoothVectorTruncation.divergence_exponent a.divergenceExponent_gt_two
  scalarExponent_gt_two := a.scalarExponent_gt_two
  vector_memLp := fun n => SmoothVectorTruncation.vector_memLp _ hρ _ (a.vector_memLp n)
  divergence_memLp := fun n => SmoothVectorTruncation.divergence_memLp _ hρ _ _
    (a.vector_memLp n) (a.divergence_memLp n)
  scalar_memLp := fun n => zeroExtension_memLp _ ρ _ (a.scalar_memLp n)
  bounded_memLp := (memLp_indicator_iff_restrict measurableSet_ball).mpr a.bounded_memLp
  weakDivergence := fun n => SmoothVectorTruncation.weakDivergence_local _ hρ
    a.divergenceExponent_gt_two (a.weakDivergence n) (a.vector_memLp n) (a.divergence_memLp n)

theorem Data.truncated_vector_eq (a : Data O ρ) (hρ : 0 < ρ)
    (i : Fin N × Fin 3) {x : Configuration N} (hx : x ∈ Metric.ball O (ρ / 2)) :
    (a.truncated hρ).vector i x = a.vector i x := by
  exact SmoothVectorTruncation.vector_eq _ hρ (a.vectorCoefficient i.1) i.2
    (Metric.mem_ball.mpr ((coordinate_dist_le i.1 x O).trans_lt (Metric.mem_ball.mp hx)))

theorem Data.truncated_scalar_eq (a : Data O ρ) (hρ : 0 < ρ)
    {x : Configuration N} (hx : x ∈ Metric.ball O (ρ / 2)) :
    (a.truncated hρ).scalar x = a.scalar x := by
  have hxρ : x ∈ Metric.ball O ρ :=
    Metric.mem_ball.mpr ((Metric.mem_ball.mp hx).trans (by linarith only [hρ]))
  have hs : (∑ n, coordinateCoefficient n
      (zeroExtension (GptLean.PhysicalSourceCoordinates.split n O).1 ρ (a.scalarCoefficient n)) x) =
      ∑ n, coordinateCoefficient n (a.scalarCoefficient n) x :=
    Finset.sum_congr rfl fun n _ => coordinate_zeroExtension_eq n O x ρ (a.scalarCoefficient n) hxρ
  exact congrArg₂ (fun z w : ℝ => z + w) hs (Set.indicator_of_mem hxρ a.boundedCoefficient)

theorem Data.truncated_positive_eq (a : Data O ρ) (hρ : 0 < ρ)
    {x : Configuration N} (hx : x ∈ Metric.ball O (ρ / 2)) :
    (a.truncated hρ).positive x = a.positive x :=
  congrArg (fun z : ℝ => Real.sqrt (max z 0)) (a.truncated_scalar_eq hρ hx)

theorem Data.truncated_negative_eq (a : Data O ρ) (hρ : 0 < ρ)
    {x : Configuration N} (hx : x ∈ Metric.ball O (ρ / 2)) :
    (a.truncated hρ).negative x = a.negative x :=
  congrArg (fun z : ℝ => Real.sqrt (max (-z) 0)) (a.truncated_scalar_eq hρ hx)

theorem Data.agreement (a : Data O ρ) (hρ : 0 < ρ) (ψ : WaveSpace (Fin N × Fin 3))
    (hs : ∀ᵐ x ∂volume, x ∉ Metric.ball O (ρ / 2) → ψ x = 0) :
    Agreement a.vector (a.truncated hρ).vector a.positive a.negative
      (a.truncated hρ).positive (a.truncated hρ).negative ψ := by
  have hball : ∀ᵐ x ∂volume, ψ x ≠ 0 → x ∈ Metric.ball O (ρ / 2) :=
    hs.mono fun x hx hn => Classical.byContradiction fun hnot => hn (hx hnot)
  exact ⟨fun i => hball.mono fun x hx hn => (a.truncated_vector_eq hρ i (hx hn)).symm,
    hball.mono fun x hx hn => (a.truncated_positive_eq hρ (hx hn)).symm,
    hball.mono fun x hx hn => (a.truncated_negative_eq hρ (hx hn)).symm⟩

end PfHk.PhysicalLocalExternalCoefficients
