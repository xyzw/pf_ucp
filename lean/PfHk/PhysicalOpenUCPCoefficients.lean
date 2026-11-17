import PfHk.PhysicalLocalExternalCoefficients
import GptLean.PhysicalPairDuality
import PfHk.ScalarPotentialSmallForm

/-! Coefficients regular only near points of an open configuration region.
Local Lp bounds and local distributional divergence supply the actual
Carleman realizations. No bounds across the exceptional set are required. -/

noncomputable section
namespace PfHk.PhysicalOpenUCPCoefficients

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.SymmetricLift PfHk.CoordinateSobolev PfHk.PhysicalLocalEnergy
  PfHk.FriedrichsDivergenceBackground
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 20000

abbrev ElectronicPosition := GptLean.PhysicalSourceCoordinates.Position

/-- Ordinary coefficient bounds on one configuration-centered family of balls. -/
structure LocalBounds {N : ℕ}
    (A : Fin N → Fin 3 → ElectronicPosition → ℝ)
    (d v : Fin N → ElectronicPosition → ℝ)
    (b : Configuration N → ℝ) (ell p : ℝ) (O : Configuration N) (ρ : ℝ) : Prop where
  vector_memLp : ∀ n i, MemLp (A n i) 6
    (volume.restrict (Metric.ball (PhysicalSourceCoordinates.split n O).1 ρ))
  divergence_memLp : ∀ n, MemLp (d n) (ENNReal.ofReal ell)
    (volume.restrict (Metric.ball (PhysicalSourceCoordinates.split n O).1 ρ))
  scalar_memLp : ∀ n, MemLp (v n) (ENNReal.ofReal p)
    (volume.restrict (Metric.ball (PhysicalSourceCoordinates.split n O).1 ρ))
  bounded_memLp : MemLp b ∞ (volume.restrict (Metric.ball O ρ))
  weakDivergence : ∀ n, WeakDivergenceOn
    (Metric.ball (PhysicalSourceCoordinates.split n O).1 ρ) (A n) (d n)

structure Data (N : ℕ) (U : Set (Configuration N)) where
  vectorCoefficient : Fin N → Fin 3 → ElectronicPosition → ℝ
  divergenceCoefficient : Fin N → ElectronicPosition → ℝ
  scalarCoefficient : Fin N → ElectronicPosition → ℝ
  boundedCoefficient : Configuration N → ℝ
  divergenceExponent : ℝ
  scalarExponent : ℝ
  divergenceExponent_gt_two : 2 < divergenceExponent
  scalarExponent_gt_two : 2 < scalarExponent
  scalar_in_sum : ∀ n, ∃ v : PhysicalPairDuality.ScalarPotential,
    scalarCoefficient n =ᵐ[volume] (v.val : ElectronicPosition → ℝ)
  bounded_measurable : AEStronglyMeasurable boundedCoefficient volume
  bounded_nonneg : ∀ᵐ X ∂volume, 0 ≤ boundedCoefficient X
  local_coefficients : ∀ O ∈ U, ∃ ρ : ℝ, 0 < ρ ∧
    LocalBounds vectorCoefficient divergenceCoefficient scalarCoefficient
      boundedCoefficient divergenceExponent scalarExponent O ρ

variable {N : ℕ} {U : Set (Configuration N)}

def Data.vector (a : Data N U) : (Fin N × Fin 3) → Configuration N → ℝ :=
  configurationVector a.vectorCoefficient

def Data.scalar (a : Data N U) (X : Configuration N) : ℝ :=
  (∑ n, coordinateCoefficient n (a.scalarCoefficient n) X) + a.boundedCoefficient X

def Data.positive (a : Data N U) : Configuration N → ℝ :=
  SignedScalarMultiplier.positiveAmplitude a.scalar

def Data.negative (a : Data N U) : Configuration N → ℝ :=
  SignedScalarMultiplier.negativeAmplitude a.scalar

def Data.localData (a : Data N U) (O : Configuration N) (ρ : ℝ)
    (h : LocalBounds a.vectorCoefficient a.divergenceCoefficient a.scalarCoefficient
      a.boundedCoefficient a.divergenceExponent a.scalarExponent O ρ) :
    PhysicalLocalExternalCoefficients.Data O ρ where
  vectorCoefficient := a.vectorCoefficient
  divergenceCoefficient := a.divergenceCoefficient
  scalarCoefficient := a.scalarCoefficient
  boundedCoefficient := a.boundedCoefficient
  divergenceExponent := a.divergenceExponent
  scalarExponent := a.scalarExponent
  divergenceExponent_gt_two := a.divergenceExponent_gt_two
  scalarExponent_gt_two := a.scalarExponent_gt_two
  vector_memLp := h.vector_memLp
  divergence_memLp := h.divergence_memLp
  scalar_memLp := h.scalar_memLp
  bounded_memLp := h.bounded_memLp
  weakDivergence := h.weakDivergence

theorem Data.scalarCoefficient_measurable (a : Data N U) (n : Fin N) :
    AEStronglyMeasurable (a.scalarCoefficient n) volume := by
  obtain ⟨v, hv⟩ := a.scalar_in_sum n
  exact v.val.aestronglyMeasurable.congr hv.symm

theorem Data.scalar_measurable (a : Data N U) : AEStronglyMeasurable a.scalar volume :=
  (Finset.univ.aestronglyMeasurable_fun_sum fun n _ =>
    coordinateCoefficient_measurable n (a.scalarCoefficient_measurable n)).add a.bounded_measurable

theorem Data.negative_measurable (a : Data N U) : AEStronglyMeasurable a.negative volume :=
  (Real.continuous_sqrt.comp (continuous_id.max continuous_const)).comp_aestronglyMeasurable
    a.scalar_measurable.neg

private theorem negative_part_sum_le {J : Type*} [Fintype J] (v : J → ℝ) (b : ℝ)
    (hb : 0 ≤ b) : max (-((∑ j, v j) + b)) 0 ≤ ∑ j, |v j| := by
  apply max_le
  · have h := neg_le_abs (∑ j, v j)
    have hs := Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := v)
    linarith only [h, hs, hb]
  · exact Finset.sum_nonneg fun j _ => abs_nonneg _

theorem Data.negative_sq_le (a : Data N U) :
    ∀ᵐ X ∂volume, a.negative X ^ 2 ≤ ∑ n, |coordinateCoefficient n (a.scalarCoefficient n) X| := by
  filter_upwards [a.bounded_nonneg] with X hB
  exact (SignedScalarMultiplier.negativeAmplitude_sq a.scalar X).trans_le
    (negative_part_sum_le (fun n => coordinateCoefficient n (a.scalarCoefficient n) X)
      (a.boundedCoefficient X) hB)

theorem Data.negative_small_form (a : Data N U) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ScalarMultiplierBound a.negative ε C :=
  ScalarPotentialSmallForm.negative_bound_of_scalarPotential a.scalarCoefficient
    a.scalar_in_sum a.negative a.negative_measurable a.negative_sq_le hε

theorem Data.negative_quarter_form (a : Data N U) :
    ∃ C : ℝ, 0 ≤ C ∧ ScalarMultiplierBound a.negative (1 / 4) C :=
  a.negative_small_form (by norm_num)

end PfHk.PhysicalOpenUCPCoefficients
