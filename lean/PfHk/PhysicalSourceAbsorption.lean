import PfHk.PhysicalDyadicPartition
import PfHk.WeightedNorm
import PfHk.CarlemanAlgebra

/-! Absorption for actual Pauli--Fierz L2 sources. Integrability of the
full source follows from the proved free and perturbation estimates. -/

noncomputable section
namespace PfHk.PhysicalSourceAbsorption

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.SymmetricLift PfHk.PhysicalDyadicEnergy

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 20000

private theorem add_integrable_bound {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] {μ : Measure X} {w : X → ℝ} {f g h : X → H}
    (hw : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hm : AEStronglyMeasurable (fun x => w x * ‖h x‖ ^ 2) μ)
    (hf : Integrable (fun x => w x * ‖f x‖ ^ 2) μ)
    (hg : Integrable (fun x => w x * ‖g x‖ ^ 2) μ)
    (heq : h =ᵐ[μ] fun x => f x + g x) :
    Integrable (fun x => w x * ‖h x‖ ^ 2) μ ∧
      (∫ x, w x * ‖h x‖ ^ 2 ∂μ) ≤
        2 * (∫ x, w x * ‖f x‖ ^ 2 ∂μ) + 2 * (∫ x, w x * ‖g x‖ ^ 2 ∂μ) := by
  have hn : Integrable (fun x => w x * ‖-g x‖ ^ 2) μ := by
    simpa only [norm_neg] using hg
  have heq' : h =ᵐ[μ] fun x => f x - -g x := by
    simpa only [sub_neg_eq_add] using heq
  simpa only [norm_neg] using WeightedNorm.sub_integrable_bound hw hm hf hn heq'

private theorem lp_absorb {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] {μ : Measure X} (w : X → ℝ)
    (hw : ∀ᵐ x ∂μ, 0 ≤ w x) (hm : AEStronglyMeasurable w μ)
    (free full error : Lp H 2 μ) (hoperator : full = free + error)
    (hf : Integrable (fun x => w x * ‖free x‖ ^ 2) μ)
    (he : Integrable (fun x => w x * ‖error x‖ ^ 2) μ)
    (hsmall : (∫ x, w x * ‖error x‖ ^ 2 ∂μ) ≤ (∫ x, w x * ‖free x‖ ^ 2 ∂μ) / 4) :
    Integrable (fun x => w x * ‖full x‖ ^ 2) μ ∧
      (∫ x, w x * ‖free x‖ ^ 2 ∂μ) ≤ 4 * ∫ x, w x * ‖full x‖ ^ 2 ∂μ := by
  have hfull : (fun x => full x) =ᵐ[μ] fun x => free x + error x :=
    (Filter.EventuallyEq.of_eq (congrArg (fun z : Lp H 2 μ => ⇑z) hoperator)).trans
      (Lp.coeFn_add free error)
  have hp := add_integrable_bound hw (hm.mul ((Lp.aestronglyMeasurable full).norm.pow 2))
    hf he hfull
  have hfree : (fun x => free x) =ᵐ[μ] fun x => full x - error x := by
    filter_upwards [hfull] with x hx
    rw [hx, add_sub_cancel_right]
  have htriangle := (WeightedNorm.sub_integrable_bound hw hf.aestronglyMeasurable
    hp.1 he hfree).2
  exact ⟨hp.1, CarlemanAlgebra.perturbation_absorption htriangle hsmall⟩

variable {N : ℕ}

theorem centeredSourceWeight_measurable (O : Configuration N) (τ α : ℝ) :
    Measurable (centeredSourceWeight O τ α) := by
  unfold centeredSourceWeight CarlemanSpatialDensity.sourceWeight CarlemanWeights.weight
  fun_prop

theorem centeredSourceWeight_nonneg (O : Configuration N) (τ α : ℝ) (X : Configuration N) :
    0 ≤ centeredSourceWeight O τ α X := by
  unfold centeredSourceWeight CarlemanSpatialDensity.sourceWeight
  positivity

theorem sourceEnergy_nonneg (O : Configuration N) (τ α : ℝ)
    (f : WaveSpace (Fin N × Fin 3)) : 0 ≤ ∫ X, sourceEnergy O τ α f X :=
  integral_nonneg fun X => mul_nonneg (centeredSourceWeight_nonneg O τ α X) (sq_nonneg _)

theorem absorb {O : Configuration N} {τ α : ℝ}
    (free full error : WaveSpace (Fin N × Fin 3))
    (hoperator : full = free + error)
    (hf : Integrable (sourceEnergy O τ α free))
    (he : Integrable (sourceEnergy O τ α error))
    (hsmall : (∫ X, sourceEnergy O τ α error X) ≤
      (∫ X, sourceEnergy O τ α free X) / 4) :
    Integrable (sourceEnergy O τ α full) ∧
      (∫ X, sourceEnergy O τ α free X) ≤ 4 * ∫ X, sourceEnergy O τ α full X := by
  exact lp_absorb (centeredSourceWeight O τ α)
    (ae_of_all volume (centeredSourceWeight_nonneg O τ α))
    (centeredSourceWeight_measurable O τ α).aestronglyMeasurable
    free full error hoperator hf he hsmall

end PfHk.PhysicalSourceAbsorption
