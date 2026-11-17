import PfHk.PhysicalCommonFormCoefficients
import PfHk.LpSumCoordinateDomain

/-! Canonical signed scalar amplitudes of the complete one-body plus
repulsive Coulomb potential act on every actual electronic H1 vector. -/

noncomputable section
namespace PfHk.PhysicalCommonFormDomain

open MeasureTheory GptLean GptLean.ElectronicH1Space GptLean.PhysicalPairDuality
open GptLean.PhysicalSourceCoordinates PfHk.CoordinateSobolev
open scoped ENNReal

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

variable {N : ℕ}

theorem scalar_measurable (v : ScalarPotential) (c : ℝ) :
    AEStronglyMeasurable (scalar (N := N) v c) volume :=
  (Finset.univ.aestronglyMeasurable_fun_sum fun n _ =>
    coordinateCoefficient_measurable n v.val.aestronglyMeasurable).add
    ((PhysicalCoulombH1.potential_measurable N).aestronglyMeasurable.const_mul c)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

theorem scalar_density_integrable (v : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)
    (u : H1 H (Fin N × Fin 3)) :
    Integrable (fun X => |scalar v c X| * ‖value u X‖ ^ 2) volume := by
  have hs : Integrable (fun X => ∑ n : Fin N,
      |coordinateCoefficient n (v.val : Position → ℝ) X| * ‖value u X‖ ^ 2) volume :=
    integrable_finsetSum _ fun n _ => LpSumCoordinateDomain.scalar_density v n u
  have hcoul := PhysicalCoulombH1.scaled_potential_integrable c u
  apply (hs.add hcoul).mono'
    ((scalar_measurable v c).norm.mul ((Lp.aestronglyMeasurable (value u)).norm.pow 2))
  filter_upwards [] with X
  change ‖|scalar v c X| * ‖value u X‖ ^ 2‖ ≤
    (∑ n : Fin N, |coordinateCoefficient n (v.val : Position → ℝ) X| * ‖value u X‖ ^ 2) +
    (c * PhysicalCoulombH1.potential N X) * ‖value u X‖ ^ 2
  rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))]
  have hcp : 0 ≤ c * PhysicalCoulombH1.potential N X :=
    mul_nonneg hc (PhysicalCoulombH1.potential_nonneg N X)
  have h := (abs_add_le (∑ n : Fin N, coordinateCoefficient n (v.val : Position → ℝ) X)
    (c * PhysicalCoulombH1.potential N X)).trans
      (add_le_add (Finset.abs_sum_le_sum_abs (s := Finset.univ)
        (f := fun n : Fin N => coordinateCoefficient n (v.val : Position → ℝ) X)) (abs_of_nonneg hcp).le)
  exact (mul_le_mul_of_nonneg_right h (sq_nonneg _)).trans_eq (by
    simp only [add_mul, Finset.sum_mul])

private theorem square_dominated_multiplier (W w : Configuration N → ℝ)
    (hw : AEStronglyMeasurable w volume) (u : L2 H (Fin N × Fin 3))
    (hi : Integrable (fun X => |W X| * ‖u X‖ ^ 2) volume)
    (hb : ∀ X, w X ^ 2 ≤ |W X|) : MemLp (fun X => w X • u X) 2 volume := by
  have hm := hw.smul (Lp.aestronglyMeasurable u)
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  apply hi.mono' (hm.norm.pow 2)
  filter_upwards [] with X
  change ‖‖w X • u X‖ ^ 2‖ ≤ |W X| * ‖u X‖ ^ 2
  rw [Real.norm_of_nonneg (sq_nonneg _), norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  exact mul_le_mul_of_nonneg_right (hb X) (sq_nonneg _)

theorem positive_multiplier (v : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)
    (u : H1 H (Fin N × Fin 3)) :
    MemLp (fun X => positive v c X • value u X) 2 volume := by
  apply square_dominated_multiplier (scalar v c) (positive v c)
    ((Real.continuous_sqrt.comp (continuous_id.max continuous_const)).comp_aestronglyMeasurable
      (scalar_measurable v c)) (value u) (scalar_density_integrable v c hc u)
  intro X
  exact (SignedScalarMultiplier.positiveAmplitude_sq (scalar v c) X).trans_le
    (max_le (le_abs_self _) (abs_nonneg _))

theorem negative_multiplier (v : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)
    (u : H1 H (Fin N × Fin 3)) :
    MemLp (fun X => negative v c X • value u X) 2 volume := by
  apply square_dominated_multiplier (scalar v c) (negative v c)
    ((Real.continuous_sqrt.comp (continuous_id.max continuous_const)).comp_aestronglyMeasurable
      (scalar_measurable v c).neg) (value u) (scalar_density_integrable v c hc u)
  intro X
  exact (SignedScalarMultiplier.negativeAmplitude_sq (scalar v c) X).trans_le
    (max_le (neg_le_abs _) (abs_nonneg _))

end PfHk.PhysicalCommonFormDomain
