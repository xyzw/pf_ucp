import GptLean.PhotonLossClosure
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
Electronic tightness from the actual spatial tails of L¹ densities.
The decay and difference estimates are derived from measure theory for
every measurable increasing exhaustion. No tail convergence is supplied
as an additional analytic hypothesis.
-/

namespace GptLean.PhotonLocalization

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The electronic mass outside a spatial region. Absolute values also
allow signed L¹ representatives and preserve the norm estimate. -/
noncomputable def densityTail (region : ℕ → Set Ω) (R : ℕ)
    (ρ : Lp ℝ 1 μ) : ℝ :=
  ∫ x in (region R)ᶜ, ‖ρ x‖ ∂μ

theorem densityTail_nonneg (region : ℕ → Set Ω) (R : ℕ) (ρ : Lp ℝ 1 μ) :
    0 ≤ densityTail region R ρ :=
  integral_nonneg fun _ => norm_nonneg _

theorem densityTail_le_norm (region : ℕ → Set Ω) (R : ℕ) (ρ : Lp ℝ 1 μ) :
    densityTail region R ρ ≤ ‖ρ‖ := by
  rw [L1.norm_eq_integral_norm]
  exact setIntegral_le_integral (L1.integrable_coeFn ρ).norm
    (Eventually.of_forall fun _ => norm_nonneg _)

/-- The L¹ triangle inequality controls the same spatial tail for two
densities by their full L¹ distance. -/
theorem densityTail_le_add_dist (region : ℕ → Set Ω) (R : ℕ)
    (ρ σ : Lp ℝ 1 μ) :
    densityTail region R ρ ≤ densityTail region R σ + dist ρ σ := by
  have hρ := L1.integrable_coeFn ρ
  have hσ := L1.integrable_coeFn σ
  have hd := (hρ.sub hσ).norm
  calc
    densityTail region R ρ ≤
        ∫ x in (region R)ᶜ, ‖σ x‖ + ‖ρ x - σ x‖ ∂μ := by
      apply integral_mono hρ.norm.restrict (hσ.norm.add hd).restrict
      intro x
      change ‖ρ x‖ ≤ ‖σ x‖ + ‖ρ x - σ x‖
      calc
        ‖ρ x‖ = ‖σ x + (ρ x - σ x)‖ := by
          congr 1
          abel
        _ ≤ ‖σ x‖ + ‖ρ x - σ x‖ := norm_add_le _ _
    _ = densityTail region R σ + ∫ x in (region R)ᶜ, ‖ρ x - σ x‖ ∂μ :=
      integral_add hσ.norm.restrict hd.restrict
    _ ≤ densityTail region R σ + ∫ x, ‖ρ x - σ x‖ ∂μ :=
      add_le_add_right (setIntegral_le_integral hd
        (Eventually.of_forall fun _ => norm_nonneg _)) _
    _ = densityTail region R σ + dist ρ σ := by
      rw [L1.dist_eq_integral_dist]
      simp only [dist_eq_norm]

/-- Integrability alone makes the tail of each density vanish along any
measurable increasing exhaustion of the spatial domain. -/
theorem densityTail_tendsto_zero (region : ℕ → Set Ω)
    (hmeasurable : ∀ R, MeasurableSet (region R))
    (hmono : Monotone region) (hexhaust : ⋃ R, region R = Set.univ)
    (ρ : Lp ℝ 1 μ) :
    Tendsto (fun R => densityTail region R ρ) atTop (𝓝 0) := by
  have hinter : (⋂ R, (region R)ᶜ) = ∅ := by
    rw [← Set.compl_iUnion, hexhaust, Set.compl_univ]
  have hlim := tendsto_setIntegral_of_antitone
    (fun R => (hmeasurable R).compl)
    (fun _ _ h => Set.compl_subset_compl.mpr (hmono h))
    (⟨0, (L1.integrable_coeFn ρ).norm.restrict⟩ :
      ∃ R, IntegrableOn (fun x => ‖ρ x‖) (region R)ᶜ μ)
  simpa only [densityTail, hinter, Measure.restrict_empty, integral_zero_measure] using hlim

/-- Spatial tightness includes every term of the density sequence. -/
def DensityTight (region : ℕ → Set Ω) (ρ : ℕ → Lp ℝ 1 μ) : Prop :=
  ∀ ε > 0, ∀ᶠ R in atTop, ∀ n, densityTail region R (ρ n) ≤ ε

theorem densityTight_of_tendsto (region : ℕ → Set Ω)
    (hmeasurable : ∀ R, MeasurableSet (region R))
    (hmono : Monotone region) (hexhaust : ⋃ R, region R = Set.univ)
    {ρ : ℕ → Lp ℝ 1 μ} {σ : Lp ℝ 1 μ} (hρ : Tendsto ρ atTop (𝓝 σ)) :
    DensityTight region ρ :=
  PhotonLoss.uniform_tail_bounds_of_tendsto (densityTail region)
    (densityTail_tendsto_zero region hmeasurable hmono hexhaust)
    (densityTail_le_add_dist region) hρ

/-- The concrete scalar electronic error used by a compression witness. -/
noncomputable def densityTailError (region : ℕ → Set Ω)
    (ρ : ℕ → Lp ℝ 1 μ) (R : ℕ) : ℝ :=
  ⨆ n, densityTail region R (ρ n)

theorem densityTail_range_bddAbove_of_norm_bound (region : ℕ → Set Ω)
    {ρ : ℕ → Lp ℝ 1 μ} {C : ℝ} (hC : ∀ n, ‖ρ n‖ ≤ C)
    (R : ℕ) : BddAbove (Set.range fun n => densityTail region R (ρ n)) :=
  ⟨C, by
    rintro _ ⟨n, rfl⟩
    exact (densityTail_le_norm region R (ρ n)).trans (hC n)⟩

theorem densityTail_le_error_of_norm_bound (region : ℕ → Set Ω)
    {ρ : ℕ → Lp ℝ 1 μ} {C : ℝ} (hC : ∀ n, ‖ρ n‖ ≤ C)
    (R n : ℕ) : densityTail region R (ρ n) ≤ densityTailError region ρ R :=
  le_ciSup (densityTail_range_bddAbove_of_norm_bound region hC R) n

/-- The general compression interface only needs tightness and a uniform
mass bound. For physical nonnegative densities the latter is particle
number normalization. -/
theorem densityTailError_tendsto_zero_of_tight (region : ℕ → Set Ω)
    {ρ : ℕ → Lp ℝ 1 μ} {C : ℝ} (hC : ∀ n, ‖ρ n‖ ≤ C)
    (htight : DensityTight region ρ) :
    Tendsto (densityTailError region ρ) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨R, hR⟩ := eventually_atTop.1 (htight (ε / 2) (half_pos hε))
  refine ⟨R, fun S hS => ?_⟩
  have hbound : densityTailError region ρ S ≤ ε / 2 := ciSup_le (hR S hS)
  have hnonneg : 0 ≤ densityTailError region ρ S :=
    (densityTail_nonneg region S (ρ 0)).trans
      (densityTail_le_error_of_norm_bound region hC S 0)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  exact hbound.trans_lt (half_lt_self hε)

theorem densityTail_range_bddAbove (region : ℕ → Set Ω)
    {ρ : ℕ → Lp ℝ 1 μ} {σ : Lp ℝ 1 μ} (hρ : Tendsto ρ atTop (𝓝 σ))
    (R : ℕ) : BddAbove (Set.range fun n => densityTail region R (ρ n)) := by
  obtain ⟨B, hB⟩ := hρ.norm.bddAbove_range
  exact densityTail_range_bddAbove_of_norm_bound region
    (fun n => hB (Set.mem_range_self n)) R

theorem densityTail_le_error (region : ℕ → Set Ω)
    {ρ : ℕ → Lp ℝ 1 μ} {σ : Lp ℝ 1 μ} (hρ : Tendsto ρ atTop (𝓝 σ))
    (R n : ℕ) : densityTail region R (ρ n) ≤ densityTailError region ρ R :=
  le_ciSup (densityTail_range_bddAbove region hρ R) n

theorem densityTailError_nonneg (region : ℕ → Set Ω)
    {ρ : ℕ → Lp ℝ 1 μ} {σ : Lp ℝ 1 μ} (hρ : Tendsto ρ atTop (𝓝 σ))
    (R : ℕ) : 0 ≤ densityTailError region ρ R :=
  (densityTail_nonneg region R (ρ 0)).trans (densityTail_le_error region hρ R 0)

/-- Uniform L¹ tightness produces a vanishing scalar error that bounds
every term, exactly as required by the finite-compression argument. -/
theorem densityTailError_tendsto_zero (region : ℕ → Set Ω)
    (hmeasurable : ∀ R, MeasurableSet (region R))
    (hmono : Monotone region) (hexhaust : ⋃ R, region R = Set.univ)
    {ρ : ℕ → Lp ℝ 1 μ} {σ : Lp ℝ 1 μ} (hρ : Tendsto ρ atTop (𝓝 σ)) :
    Tendsto (densityTailError region ρ) atTop (𝓝 0) := by
  obtain ⟨B, hB⟩ := hρ.norm.bddAbove_range
  exact densityTailError_tendsto_zero_of_tight region
    (fun n => hB (Set.mem_range_self n))
    (densityTight_of_tendsto region hmeasurable hmono hexhaust hρ)

/-- In particular, the usual spatial regions are expanding closed balls.
This applies to Euclidean electronic space with its Lebesgue measure. -/
theorem densityTight_closedBall_of_tendsto [PseudoMetricSpace Ω] [BorelSpace Ω]
    (center : Ω) {ρ : ℕ → Lp ℝ 1 μ} {σ : Lp ℝ 1 μ}
    (hρ : Tendsto ρ atTop (𝓝 σ)) :
    DensityTight (fun R => Metric.closedBall center (R : ℝ)) ρ := by
  apply densityTight_of_tendsto _ (fun _ => measurableSet_closedBall)
    (fun _ _ h => Metric.closedBall_subset_closedBall (Nat.cast_le.mpr h))
    (Metric.iUnion_closedBall_nat center) hρ

/-- A continuous L¹ density component of the constrained pair supplies
the electronic tightness field used by `ConstraintRealization`. The
remaining hypothesis identifies that component on represented states. -/
theorem densityTight_of_pair_tendsto {State Pair X : Type*} [TopologicalSpace Pair]
    (region : ℕ → Set Ω) (hmeasurable : ∀ R, MeasurableSet (region R))
    (hmono : Monotone region) (hexhaust : ⋃ R, region R = Set.univ)
    (pair : State → Pair) (repr : State → X) (density : X → Lp ℝ 1 μ)
    (component : Pair → Lp ℝ 1 μ) (hcomponent : Continuous component)
    (hidentify : ∀ s, density (repr s) = component (pair s))
    {s : ℕ → State} {d : Pair}
    (hpair : Tendsto (fun n => pair (s n)) atTop (𝓝 d)) :
    DensityTight region (fun n => density (repr (s n))) := by
  apply densityTight_of_tendsto region hmeasurable hmono hexhaust
    (σ := component d)
  simpa only [hidentify, Function.comp_def] using (hcomponent.tendsto d).comp hpair

end GptLean.PhotonLocalization
