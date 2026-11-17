import GptLean.PhysicalPairIntegrability
import GptLean.PhysicalSourceFubini
import GptLean.SymmetricLift.CollisionGeometry
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
The three-dimensional Coulomb form is finite on actual L2-intersect-L6
sources. The proof uses local integrability of the inverse-square
singularity, Holder on the unit ball, and the bounded exterior. Fubini
then transfers this form integrability to an actual product L2 vector.
-/

noncomputable section

namespace GptLean.PhysicalCoulombIntegrability

open MeasureTheory GptLean.PhysicalSourceFubini GptLean.PhysicalPairIntegrability
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types false

abbrev Position := EuclideanSpace ℝ (Fin 3)

theorem inverseNorm_memLp_local :
    MemLp (fun x : Position => ‖x‖⁻¹) (3 / 2)
      (volume.restrict (Metric.closedBall (0 : Position) 1)) := by
  have : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : Position) 1)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : Position) 1).measure_lt_top.ne
  have h₂ : MemLp (fun x : Position => ‖x‖⁻¹) 2
      (volume.restrict (Metric.closedBall (0 : Position) 1)) := by
    apply (memLp_two_iff_integrable_sq_norm
      continuous_norm.measurable.inv.aestronglyMeasurable).mpr
    have hi := SymmetricLift.locallyIntegrable_inverse_square_norm_three.integrableOn_isCompact
      (isCompact_closedBall (0 : Position) 1)
    change Integrable (fun x : Position => (‖x‖ ^ 2)⁻¹)
      (volume.restrict (Metric.closedBall (0 : Position) 1)) at hi
    simpa only [Pi.inv_apply, norm_inv, norm_norm, inv_pow] using hi
  exact h₂.mono_exponent ((ENNReal.div_le_iff (by norm_num) (by norm_num)).mpr (by norm_num))

theorem inverseNorm_bounded_exterior :
    ∀ᵐ x : Position ∂volume.restrict (Metric.closedBall (0 : Position) 1)ᶜ,
      ‖‖x‖⁻¹‖ ≤ (1 : ℝ) := by
  filter_upwards [ae_restrict_mem measurableSet_closedBall.compl] with x hx
  have hn : 1 < ‖x‖ := by simpa only [Set.mem_compl_iff, Metric.mem_closedBall,
    dist_zero_right, not_le] using hx
  simpa only [norm_inv, norm_norm] using inv_le_one_of_one_le₀ hn.le

variable {H : Type*} [NormedAddCommGroup H]

/-- Actual source regularity makes its Coulomb form finite. -/
theorem coulomb_integrable {u : Position → H}
    (hu₂ : MemLp u 2 volume) (hu₆ : MemLp u 6 volume) :
    Integrable (fun x => ‖x‖⁻¹ * ‖u x‖ ^ 2) volume := by
  have hρ₁ : Integrable (fun x => ‖u x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hu₂.aestronglyMeasurable).mp hu₂
  have hρ₃ : MemLp (fun x => ‖u x‖ ^ 2) 3 volume := by
    have hdiv : (6 : ℝ≥0∞) / 2 = 3 :=
      (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
        (by norm_num [ENNReal.toReal_div])
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, hdiv] using hu₆.norm_rpow_div 2
  have hinside : IntegrableOn (fun x => ‖x‖⁻¹ * ‖u x‖ ^ 2)
      (Metric.closedBall (0 : Position) 1) volume := by
    let : ENNReal.HolderTriple (3 / 2) 3 1 :=
      ENNReal.HolderTriple.of_toReal
        ⟨by norm_num [ENNReal.toReal_div], by norm_num, by norm_num⟩
    exact memLp_one_iff_integrable.mp ((hρ₃.restrict _).mul (r := 1) inverseNorm_memLp_local)
  have houtside : IntegrableOn (fun x => ‖x‖⁻¹ * ‖u x‖ ^ 2)
      (Metric.closedBall (0 : Position) 1)ᶜ volume :=
    hρ₁.integrableOn.bdd_mul continuous_norm.measurable.inv.aestronglyMeasurable
      inverseNorm_bounded_exterior
  simpa only [Set.union_compl_self, integrableOn_univ] using hinside.union houtside

variable {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} [SigmaFinite ν]
  [IsSeparable ν] [InnerProductSpace ℂ H] [TopologicalSpace.SeparableSpace H]

/-- Integrability of the relative marginal source is integrability of the
same Coulomb form on its original product wave function. -/
theorem product_coulomb_integrable
    (u : Lp H 2 ((volume : Measure Position).prod ν))
    (hu₆ : MemLp (curry u) 6 volume) :
    Integrable (fun p => ‖p.1‖⁻¹ * ‖u p‖ ^ 2) ((volume : Measure Position).prod ν) := by
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u)
  have hm : AEStronglyMeasurable (fun p : Position × Y => ‖p.1‖⁻¹ * ‖u p‖ ^ 2)
      (volume.prod ν) :=
    continuous_norm.measurable.inv.aestronglyMeasurable.comp_fst.mul
      ((Lp.aestronglyMeasurable u).norm.pow 2)
  apply (integrable_prod_iff hm).mpr
  refine ⟨?_, ?_⟩
  · filter_upwards [hi.prod_right_ae] with x hx
    exact hx.const_mul ‖x‖⁻¹
  · have hsource := coulomb_integrable (Lp.memLp (curry u)) hu₆
    apply hsource.congr
    filter_upwards [curry_norm_sq_ae u] with x hx
    simp only [norm_mul, norm_inv, norm_norm, norm_pow]
    rw [integral_const_mul, hx]

end GptLean.PhysicalCoulombIntegrability
