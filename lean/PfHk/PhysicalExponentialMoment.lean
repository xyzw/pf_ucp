import PfHk.WeightedDensity
import PfHk.GroundState
import PfHk.PhysicalGroundStateWeak
import GptLean.PhysicalSourceCurrentBounds

/-!
The exponential density moment in the second cutoff alternative passes
to the actual density-weighted vector-potential difference. The proof
uses the physical L¹ ∩ L³ density class and L³ + L∞ vector potentials.
The cutoff need only be nonzero as an almost-everywhere class.
-/

noncomputable section

namespace PfHk.PhysicalExponentialMoment

open MeasureTheory Filter GptLean GptLean.PhysicalPairSpace
  GptLean.PhysicalPairDuality GptLean.PhysicalGroundState
  GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.PhysicalPFReference
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 300000

/-- The chosen L¹ representative of a physical density is also in L³. -/
theorem density_memLp_three (d : Pair) :
    MemLp (densityL1 d) 3 volume :=
  (Lp.memLp (densityL3 d)).ae_eq (compatible d.1).symm

/-- The exponential moment controls multiplication by any physical
vector potential at half the exponent. -/
theorem density_smul_integrable (A : VectorPotential) (d : Pair) {α : ℝ}
    (hα : 0 ≤ α) (hρ : ∀ᵐ x ∂volume, 0 ≤ densityL1 d x)
    (hmoment : Integrable (fun x => Real.exp (α * ‖x‖) * densityL1 d x) volume) :
    Integrable (fun x => (Real.exp (α * ‖x‖ / 2) * densityL1 d x) • A.val x)
      volume := by
  have hi := WeightedDensity.exponential_current_integrable hα
    (density_memLp_three d) hρ hmoment
    (Lp.memLp (parts A).2) (Lp.memLp (parts A).1)
  apply hi.congr
  filter_upwards [TransformationsPotentials.coeFn_parts A] with x hx
  rw [hx, add_comm ((parts A).1 x) ((parts A).2 x)]

/-- The physical current difference has an exponential moment at half
the density exponent. -/
theorem vectorDifference_integrable (a₁ a₂ : Potential) (d : Pair) {α : ℝ}
    (hα : 0 ≤ α) (hρ : ∀ᵐ x ∂volume, 0 ≤ densityL1 d x)
    (hmoment : Integrable (fun x => Real.exp (α * ‖x‖) * densityL1 d x) volume) :
    Integrable (fun x => Real.exp ((α / 2) * ‖x‖) •
      PfHk.vectorDifference a₁ a₂ d x) volume := by
  have h₁ := density_smul_integrable a₁.2 d hα hρ hmoment
  have h₂ := density_smul_integrable a₂.2 d hα hρ hmoment
  apply (h₁.sub h₂).congr
  exact ae_of_all _ fun x => by
    have hexp : α * ‖x‖ / 2 = (α / 2) * ‖x‖ := by ring
    simp only [Pi.sub_apply, hexp, PfHk.vectorDifference, smul_smul, smul_sub]

/-- Each real component has the absolute exponential moment needed for
Fourier analyticity. -/
theorem component_integrable (a₁ a₂ : Potential) (d : Pair) {α : ℝ}
    (hα : 0 ≤ α) (hρ : ∀ᵐ x ∂volume, 0 ≤ densityL1 d x)
    (hmoment : Integrable (fun x => Real.exp (α * ‖x‖) * densityL1 d x) volume)
    (j : Fin 3) :
    Integrable (fun x => Real.exp ((α / 2) * ‖x‖) *
      |PfHk.vectorDifference a₁ a₂ d x j|) volume := by
  have hi := (EuclideanSpace.proj j : Vector →L[ℝ] ℝ).integrable_comp
    (vectorDifference_integrable a₁ a₂ d hα hρ hmoment)
  have hc : Integrable (fun x => Real.exp ((α / 2) * ‖x‖) *
      PfHk.vectorDifference a₁ a₂ d x j) volume := hi
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using hc.norm

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff)
  (C : CanonicalSectorCCR photonMeasure)
  (B : PhysicalNormalTrace.StandardNormalTraceBackground)
  (S : PhysicalClosedForms.StandardClosedFormBackground) (e : ℝ)

attribute [local irreducible] inclusion covariant PhysicalPFReference.referenceSubspace

/-- Every normalized physical state has nonnegative density. This
requires neither ground-state minimality nor unique continuation. -/
theorem model_density_nonneg (i : Fin N) (p : State F χ C B S e (N := N)) :
    ∀ᵐ x ∂volume, 0 ≤ densityL1 ((model i F χ C B S e).density p) x := by
  let u := PhysicalGroundStateWeak.stateReference F χ C B S e p
  have hv := PhysicalGroundStateWeak.stateReference_value F χ C B S e p
  have hpair := PhysicalGroundStateWeak.pure_density_eq_pair F χ C B S e i p u hv
  rw [hpair]
  exact PhysicalSourceCurrentBounds.density_nonneg i
    (ElectronicH1Complex.realEquiv (E := PhotonFock) (I := Fin N × Fin 3)
      (electronic (Fin N × Fin 3) (fun _ => 0) u)) _

/-- The exponential Fourier input for the actual article model's
density-current pair, with nonnegativity derived from the state. -/
theorem model_component_integrable (i : Fin N) (p : State F χ C B S e (N := N))
    (a₁ a₂ : Potential) {α : ℝ} (hα : 0 ≤ α)
    (hmoment : Integrable (fun x => Real.exp (α * ‖x‖) *
      densityL1 ((model i F χ C B S e).density p) x) volume) (j : Fin 3) :
    Integrable (fun x => Real.exp ((α / 2) * ‖x‖) *
      |PfHk.vectorDifference a₁ a₂ ((model i F χ C B S e).density p) x j|) volume :=
  component_integrable a₁ a₂ _ hα (model_density_nonneg F χ C B S e i p) hmoment j

/-- Reflection preserves the nonzero cutoff class by the reality law. -/
theorem cutoff_not_ae_zero_neg (χ : ArticleCutoff)
    (hχ : ¬ (χ.value =ᵐ[volume] 0)) :
    ¬ ((fun k => χ.value (-k)) =ᵐ[volume] 0) := by
  intro hzero
  apply hχ
  filter_upwards [χ.reality, hzero] with k hr hk
  change χ.value k = 0
  rw [hr, hk]
  simp

/-- A nonzero cutoff class is nonzero on a set of positive measure,
including the momentum reflection in the physical Fourier convention. -/
theorem cutoff_nonzero_set_pos (χ : ArticleCutoff)
    (hχ : ¬ (χ.value =ᵐ[volume] 0)) :
    0 < volume {k : Gaussian.FieldSpace | χ.value (-k) ≠ 0} := by
  apply pos_iff_ne_zero.mpr
  intro hz
  have hzero : ∀ᵐ k ∂volume, χ.value (-k) = 0 := by
    simpa only [Set.mem_ofPred_eq, not_not] using
      (measure_eq_zero_iff_ae_notMem.mp hz)
  exact cutoff_not_ae_zero_neg χ hχ hzero

end PfHk.PhysicalExponentialMoment
