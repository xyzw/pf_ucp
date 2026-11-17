import PfHk.PhysicalLocalExternalCoefficients
import GptLean.PhysicalPairDuality

/-! Global coefficients for physical continuation. Their local realizations
reuse the same functions, so the actual vector and scalar form amplitudes
agree definitionally with those in the local Carleman theorem. -/

noncomputable section
namespace PfHk.PhysicalUCPCoefficients

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.SymmetricLift PfHk.CoordinateSobolev PfHk.PhysicalLocalEnergy
  PfHk.FriedrichsDivergenceBackground
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 20000

abbrev ElectronicPosition := GptLean.PhysicalSourceCoordinates.Position

structure Data (N : ℕ) (U : Set (Configuration N)) where
  vectorCoefficient : Fin N → Fin 3 → ElectronicPosition → ℝ
  divergenceCoefficient : Fin N → ElectronicPosition → ℝ
  scalarCoefficient : Fin N → ElectronicPosition → ℝ
  boundedCoefficient : Configuration N → ℝ
  divergenceExponent : ℝ
  scalarExponent : ℝ
  divergenceExponent_gt_two : 2 < divergenceExponent
  scalarExponent_gt_two : 2 < scalarExponent
  vector_local_memLp : ∀ n i (o : ElectronicPosition) (r : ℝ), 0 < r →
    MemLp (vectorCoefficient n i) 6 (volume.restrict (Metric.ball o r))
  divergence_local_memLp : ∀ n (o : ElectronicPosition) (r : ℝ), 0 < r →
    MemLp (divergenceCoefficient n) (ENNReal.ofReal divergenceExponent)
      (volume.restrict (Metric.ball o r))
  scalar_local_memLp : ∀ n (o : ElectronicPosition) (r : ℝ), 0 < r →
    MemLp (scalarCoefficient n) (ENNReal.ofReal scalarExponent)
      (volume.restrict (Metric.ball o r))
  weakDivergence : ∀ n, WeakDivergence (vectorCoefficient n) (divergenceCoefficient n)
  scalar_in_sum : ∀ n, ∃ v : PhysicalPairDuality.ScalarPotential,
    scalarCoefficient n =ᵐ[volume] (v.val : ElectronicPosition → ℝ)
  bounded_measurable : AEStronglyMeasurable boundedCoefficient volume
  bounded_nonneg : ∀ᵐ X ∂volume, 0 ≤ boundedCoefficient X
  bounded_local_memLp : ∀ O ∈ U, ∃ ρ : ℝ, 0 < ρ ∧
    MemLp boundedCoefficient ∞ (volume.restrict (Metric.ball O ρ))

variable {N : ℕ} {U : Set (Configuration N)}

def Data.vector (a : Data N U) : (Fin N × Fin 3) → Configuration N → ℝ :=
  configurationVector a.vectorCoefficient

def Data.scalar (a : Data N U) (X : Configuration N) : ℝ :=
  (∑ n, coordinateCoefficient n (a.scalarCoefficient n) X) + a.boundedCoefficient X

def Data.positive (a : Data N U) : Configuration N → ℝ :=
  SignedScalarMultiplier.positiveAmplitude a.scalar

def Data.negative (a : Data N U) : Configuration N → ℝ :=
  SignedScalarMultiplier.negativeAmplitude a.scalar

def Data.localData (a : Data N U) (O : Configuration N) (ρ : ℝ) (hρ : 0 < ρ)
    (hB : MemLp a.boundedCoefficient ∞ (volume.restrict (Metric.ball O ρ))) :
    PhysicalLocalExternalCoefficients.Data O ρ where
  vectorCoefficient := a.vectorCoefficient
  divergenceCoefficient := a.divergenceCoefficient
  scalarCoefficient := a.scalarCoefficient
  boundedCoefficient := a.boundedCoefficient
  divergenceExponent := a.divergenceExponent
  scalarExponent := a.scalarExponent
  divergenceExponent_gt_two := a.divergenceExponent_gt_two
  scalarExponent_gt_two := a.scalarExponent_gt_two
  vector_memLp := fun n i => a.vector_local_memLp n i _ ρ hρ
  divergence_memLp := fun n => a.divergence_local_memLp n _ ρ hρ
  scalar_memLp := fun n => a.scalar_local_memLp n _ ρ hρ
  bounded_memLp := hB
  weakDivergence := fun n φ hφ hφs _ => a.weakDivergence n φ hφ hφs

@[simp] theorem Data.localData_vector (a : Data N U) (O : Configuration N) (ρ : ℝ)
    (hρ : 0 < ρ) (hB : MemLp a.boundedCoefficient ∞ (volume.restrict (Metric.ball O ρ))) :
    (a.localData O ρ hρ hB).vector = a.vector := rfl

@[simp] theorem Data.localData_scalar (a : Data N U) (O : Configuration N) (ρ : ℝ)
    (hρ : 0 < ρ) (hB : MemLp a.boundedCoefficient ∞ (volume.restrict (Metric.ball O ρ))) :
    (a.localData O ρ hρ hB).scalar = a.scalar := rfl

@[simp] theorem Data.localData_positive (a : Data N U) (O : Configuration N) (ρ : ℝ)
    (hρ : 0 < ρ) (hB : MemLp a.boundedCoefficient ∞ (volume.restrict (Metric.ball O ρ))) :
    (a.localData O ρ hρ hB).positive = a.positive := rfl

@[simp] theorem Data.localData_negative (a : Data N U) (O : Configuration N) (ρ : ℝ)
    (hρ : 0 < ρ) (hB : MemLp a.boundedCoefficient ∞ (volume.restrict (Metric.ball O ρ))) :
    (a.localData O ρ hρ hB).negative = a.negative := rfl

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

end PfHk.PhysicalUCPCoefficients
