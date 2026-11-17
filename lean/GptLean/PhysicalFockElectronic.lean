import GptLean.PhysicalFockNumber
import GptLean.PhotonLocalizationLocalFormsOperators
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
The same constructed photon sectors on electronic L² wave functions.

The tensor action is the actual pointwise `compLpL` action. Tonelli's
nonnegative square-norm identity proves sector completeness on this
space, and normal trace decomposition proves the exact mixed-state
sector and number identities used by local trace compactness.
-/

noncomputable section

namespace GptLean.PhysicalFock

open MeasureTheory PhotonLocalizationChannel RemovalState
open scoped ENNReal InnerProductSpace

variable (K : ℕ → Type*) [∀ n, NormedAddCommGroup (K n)]
  [∀ n, InnerProductSpace ℂ (K n)] [∀ n, CompleteSpace (K n)]
  {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

abbrev ElectronicSpace := Lp (Space K) 2 μ

def electronicSector (n : ℕ) : ElectronicSpace K μ →L[ℂ] ElectronicSpace K μ :=
  (sector K n).compLpL 2 μ

theorem electronicSector_isStarProjection (n : ℕ) :
    IsStarProjection (electronicSector K μ n) :=
  PhotonLocalization.compLpL_projection _ (sector_isStarProjection K n)

omit [∀ n, CompleteSpace (K n)] in
theorem electronicSector_mass_integral (n : ℕ) (u : ElectronicSpace K μ) :
    ‖electronicSector K μ n u‖ ^ 2 = ∫ x, ‖u x n‖ ^ 2 ∂μ := by
  let : InnerProductSpace ℝ (Space K) := InnerProductSpace.rclikeToReal ℂ (Space K)
  rw [PhotonKernelLocalization.l2_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [(sector K n).coeFn_compLpL u] with x hx
  change ‖((sector K n).compLpL 2 μ u) x‖ ^ 2 = _
  rw [hx, sector_norm]

omit [∀ n, CompleteSpace (K n)] in
/-- Pure-state sector resolution survives the electronic L² tensor factor. -/
theorem electronicSector_mass_hasSum (u : ElectronicSpace K μ) :
    HasSum (fun n => ‖electronicSector K μ n u‖ ^ 2) (‖u‖ ^ 2) := by
  let : InnerProductSpace ℝ (Space K) := InnerProductSpace.rclikeToReal ℂ (Space K)
  have hi : Integrable (fun x => ‖u x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u)
  have hm (n : ℕ) : AEStronglyMeasurable (fun x => ‖u x n‖ ^ 2) μ := by
    exact (((lp.evalCLM ℂ K 2 n).continuous.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable u)).norm.pow 2)
  have h : HasSum (fun n => ∫ x, ‖u x n‖ ^ 2 ∂μ) (∫ x, ‖u x‖ ^ 2 ∂μ) :=
    hasSum_integral_of_dominated_convergence
    (fun n x => ‖u x n‖ ^ 2)
    hm
    (fun n => ae_of_all _ (fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]))
    (ae_of_all _ (fun x => (coordinate_mass_hasSum K (u x)).summable))
    (show Integrable (fun x => ∑' n, ‖u x n‖ ^ 2) μ from by
      simpa only [(coordinate_mass_hasSum K _).tsum_eq] using hi)
    (ae_of_all _ (fun x => coordinate_mass_hasSum K (u x)))
  simpa only [← electronicSector_mass_integral,
    ← PhotonKernelLocalization.l2_norm_sq_eq_integral] using h

variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : Gaussian.RankOneData (ElectronicSpace K μ) T}

def electronicSectorTrace (F : NormalFunctionalData R) (n : ℕ) : T →L[ℝ] ℝ :=
  Complex.reCLM.comp
    (((ContinuousLinearMap.apply ℂ ℂ (electronicSector K μ n)).restrictScalars ℝ).comp F.repr)

omit [CompleteSpace T] in
@[simp] theorem electronicSectorTrace_apply (F : NormalFunctionalData R) (n : ℕ) (x : T) :
    electronicSectorTrace K μ F n x = (F.repr x (electronicSector K μ n)).re := rfl

omit [CompleteSpace T] in
@[simp] theorem electronicSectorTrace_rankOne (F : NormalFunctionalData R) (n : ℕ)
    (u : ElectronicSpace K μ) :
    electronicSectorTrace K μ F n (R.rankOne u) = ‖electronicSector K μ n u‖ ^ 2 := by
  rw [electronicSectorTrace_apply, F.rankOne]
  have hp := electronicSector_isStarProjection K μ n
  have hn : ‖electronicSector K μ n u‖ ^ 2 =
      (⟪u, (star (electronicSector K μ n) * electronicSector K μ n) u⟫_ℂ).re :=
    (electronicSector K μ n).apply_norm_sq_eq_inner_adjoint_right u
  rw [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem] at hn
  exact hn.symm

theorem electronicSectorTrace_nonneg (N : NormalTraceData R) (F : NormalFunctionalData R)
    (n : ℕ) {x : T} (hx : x ∈ R.positive) : 0 ≤ electronicSectorTrace K μ F n x :=
  N.observable_nonneg _ (fun u => by rw [electronicSectorTrace_rankOne]; positivity) hx

theorem electronicSectorTrace_hasSum (N : NormalTraceData R) (F : NormalFunctionalData R)
    {x : T} (hx : x ∈ R.positive) :
    HasSum (fun n => electronicSectorTrace K μ F n x) (R.trace x) := by
  apply N.measurement_hasSum _ R.trace
    (fun n u => by rw [electronicSectorTrace_rankOne]; positivity) _ hx
  intro u
  simpa only [electronicSectorTrace_rankOne, R.trace_rankOne] using
    electronicSector_mass_hasSum K μ u

/-- The exact `hsectorTrace` identity in the existing physical endpoint. -/
theorem electronicSectorTrace_resolution (N : NormalTraceData R) (F : NormalFunctionalData R)
    {x : T} (hx : x ∈ R.positive) :
    HasSum (fun n => (F.repr x ((sector K n).compLpL 2 μ)).re) (F.repr x 1).re := by
  rw [F.mass N hx]
  exact electronicSectorTrace_hasSum K μ N F hx

def electronicNumberTruncation (F : NormalFunctionalData R) (M : ℕ) : T →L[ℝ] ℝ :=
  ∑ n ∈ Finset.range M, (n : ℝ) • electronicSectorTrace K μ F n

omit [CompleteSpace T] in
@[simp] theorem electronicNumberTruncation_apply (F : NormalFunctionalData R)
    (M : ℕ) (x : T) :
    electronicNumberTruncation K μ F M x =
      ∑ n ∈ Finset.range M, (n : ℝ) * electronicSectorTrace K μ F n x := by
  simp only [electronicNumberTruncation, sum_apply, smul_apply, smul_eq_mul]

/-- The number form on the exact coupled Hilbert space used by compactness. -/
def electronicNumberTraceForm (N : NormalTraceData R) (F : NormalFunctionalData R)
    (Tr : PositiveTraceData T) (hcone : Tr.positive ⊆ R.positive) : PositiveForm Tr where
  truncation := electronicNumberTruncation K μ F
  nonneg := by
    intro M x hx
    rw [electronicNumberTruncation_apply]
    exact Finset.sum_nonneg fun n _ => mul_nonneg (Nat.cast_nonneg _)
      (electronicSectorTrace_nonneg K μ N F n (hcone hx))
  monotone := by
    intro x hx M L hML
    simp only [electronicNumberTruncation_apply]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hML)
      (fun n _ _ => mul_nonneg (Nat.cast_nonneg _)
        (electronicSectorTrace_nonneg K μ N F n (hcone hx)))

/-- The exact `hnumberSeries` identity for the constructed number form. -/
theorem electronicNumberTraceForm_expectation (N : NormalTraceData R)
    (F : NormalFunctionalData R) (Tr : PositiveTraceData T)
    (hcone : Tr.positive ⊆ R.positive) {x : T} (hx : x ∈ R.positive) :
    (electronicNumberTraceForm K μ N F Tr hcone).expectation x =
      ∑' n : ℕ, ENNReal.ofReal ((n : ℝ) * (F.repr x ((sector K n).compLpL 2 μ)).re) := by
  unfold PositiveForm.expectation
  change (⨆ M, ENNReal.ofReal (electronicNumberTruncation K μ F M x)) = _
  simp only [electronicNumberTruncation_apply]
  simp_rw [ENNReal.ofReal_sum_of_nonneg
    (fun n _ => mul_nonneg (Nat.cast_nonneg _) (electronicSectorTrace_nonneg K μ N F n hx))]
  exact ENNReal.tsum_eq_iSup_nat.symm

theorem electronicNumberTraceForm_rankOne (N : NormalTraceData R)
    (F : NormalFunctionalData R) (Tr : PositiveTraceData T)
    (hcone : Tr.positive ⊆ R.positive) (u : ElectronicSpace K μ) :
    (electronicNumberTraceForm K μ N F Tr hcone).expectation (R.rankOne u) =
      ∑' n : ℕ, ENNReal.ofReal ((n : ℝ) * ‖electronicSector K μ n u‖ ^ 2) := by
  rw [electronicNumberTraceForm_expectation K μ N F Tr hcone (R.rankOne_positive u)]
  exact tsum_congr fun n => congrArg ENNReal.ofReal
    (congrArg (fun a => (n : ℝ) * a) (electronicSectorTrace_rankOne K μ F n u))

end GptLean.PhysicalFock
