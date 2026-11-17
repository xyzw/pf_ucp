import GptLean.PhysicalFockSectors
import GptLean.PhotonLocalizationNormalTrace
import GptLean.PhotonLocalizationChannelMeasurement
import GptLean.PositiveForm

/-!
Normal-state sector moments for the constructed Hilbert direct sum.

Only universal normal trace-class representation data remain parameters.
The sector observables, their complete probability resolution and all
nonnegative weighted forms are constructed from coordinate projections.
The number-series identity is consequently a theorem on this same model.
-/

noncomputable section

namespace GptLean.PhysicalFock

open PhotonLocalizationChannel RemovalState
open scoped ENNReal InnerProductSpace

variable (K : ℕ → Type*) [∀ n, NormedAddCommGroup (K n)]
  [∀ n, InnerProductSpace ℂ (K n)] [∀ n, CompleteSpace (K n)]
  {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : Gaussian.RankOneData (Space K) T}

/-- The normal trace of the actual number-sector projection. -/
def sectorTrace (F : NormalFunctionalData R) (n : ℕ) : T →L[ℝ] ℝ :=
  Complex.reCLM.comp
    (((ContinuousLinearMap.apply ℂ ℂ (sector K n)).restrictScalars ℝ).comp F.repr)

omit [CompleteSpace T] in
@[simp] theorem sectorTrace_apply (F : NormalFunctionalData R) (n : ℕ) (x : T) :
    sectorTrace K F n x = (F.repr x (sector K n)).re := rfl

omit [CompleteSpace T] in
@[simp] theorem sectorTrace_rankOne (F : NormalFunctionalData R) (n : ℕ) (u : Space K) :
    sectorTrace K F n (R.rankOne u) = ‖u n‖ ^ 2 := by
  rw [sectorTrace_apply, F.rankOne, sector_inner, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

theorem sectorTrace_nonneg (N : NormalTraceData R) (F : NormalFunctionalData R)
    (n : ℕ) {x : T} (hx : x ∈ R.positive) : 0 ≤ sectorTrace K F n x :=
  N.observable_nonneg _ (fun u => by rw [sectorTrace_rankOne]; positivity) hx

/-- Mixed-state completeness is derived from the actual pure-state Parseval law. -/
theorem sectorTrace_hasSum (N : NormalTraceData R) (F : NormalFunctionalData R)
    {x : T} (hx : x ∈ R.positive) :
    HasSum (fun n => sectorTrace K F n x) (R.trace x) := by
  apply N.measurement_hasSum _ R.trace
    (fun n u => by rw [sectorTrace_rankOne]; positivity) _ hx
  intro u
  simpa only [sectorTrace_rankOne, R.trace_rankOne] using coordinate_mass_hasSum K u

theorem sectorTrace_resolution (N : NormalTraceData R) (F : NormalFunctionalData R)
    {x : T} (hx : x ∈ R.positive) :
    HasSum (fun n => (F.repr x (sector K n)).re) (F.repr x 1).re := by
  rw [F.mass N hx]
  exact sectorTrace_hasSum K N F hx

def boundedWeightTrace (F : NormalFunctionalData R) (w : ℕ → ℝ)
    (hw : ∀ n, |w n| ≤ 1) : T →L[ℝ] ℝ :=
  Complex.reCLM.comp
    (((ContinuousLinearMap.apply ℂ ℂ (boundedWeightOperator K w hw)).restrictScalars ℝ).comp F.repr)

omit [CompleteSpace T] in
@[simp] theorem boundedWeightTrace_apply (F : NormalFunctionalData R) (w : ℕ → ℝ)
    (hw : ∀ n, |w n| ≤ 1) (x : T) :
    boundedWeightTrace K F w hw x = (F.repr x (boundedWeightOperator K w hw)).re := rfl

theorem boundedWeightTrace_hasSum (N : NormalTraceData R) (F : NormalFunctionalData R)
    (w : ℕ → ℝ) (hw : ∀ n, |w n| ≤ 1) (hwpos : ∀ n, 0 ≤ w n)
    {x : T} (hx : x ∈ R.positive) :
    HasSum (fun n => w n * sectorTrace K F n x) (boundedWeightTrace K F w hw x) := by
  apply N.measurement_weighted _ _ w hwpos
    (fun n u => by rw [sectorTrace_rankOne]; positivity) _ hx
  intro u
  simpa only [sectorTrace_rankOne, boundedWeightTrace_apply, F.rankOne] using
    boundedWeightOperator_hasSum K w hw u

def weightedTraceTruncation (F : NormalFunctionalData R) (w : ℕ → ℝ) (M : ℕ) :
    T →L[ℝ] ℝ := ∑ n ∈ Finset.range M, w n • sectorTrace K F n

omit [CompleteSpace T] in
@[simp] theorem weightedTraceTruncation_apply
    (F : NormalFunctionalData R) (w : ℕ → ℝ) (M : ℕ) (x : T) :
    weightedTraceTruncation K F w M x = ∑ n ∈ Finset.range M, w n * sectorTrace K F n x := by
  simp only [weightedTraceTruncation, sum_apply, smul_apply, smul_eq_mul]

/-- The unbounded positive form is built from finite sums of the actual projections. -/
def weightedTraceForm (N : NormalTraceData R) (F : NormalFunctionalData R)
    (Tr : PositiveTraceData T) (hcone : Tr.positive ⊆ R.positive)
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) : PositiveForm Tr where
  truncation := weightedTraceTruncation K F w
  nonneg := by
    intro M x hx
    rw [weightedTraceTruncation_apply]
    exact Finset.sum_nonneg fun n _ => mul_nonneg (hw n)
      (sectorTrace_nonneg K N F n (hcone hx))
  monotone := by
    intro x hx M L hML
    simp only [weightedTraceTruncation_apply]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hML)
      (fun n _ _ => mul_nonneg (hw n) (sectorTrace_nonneg K N F n (hcone hx)))

/-- All nonnegative weighted moment identities, including infinite moments. -/
theorem weightedTraceForm_expectation (N : NormalTraceData R) (F : NormalFunctionalData R)
    (Tr : PositiveTraceData T) (hcone : Tr.positive ⊆ R.positive)
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) {x : T} (hx : x ∈ R.positive) :
    (weightedTraceForm K N F Tr hcone w hw).expectation x =
      ∑' n, ENNReal.ofReal (w n * sectorTrace K F n x) := by
  unfold PositiveForm.expectation
  change (⨆ M, ENNReal.ofReal (weightedTraceTruncation K F w M x)) = _
  simp only [weightedTraceTruncation_apply]
  simp_rw [ENNReal.ofReal_sum_of_nonneg
    (fun n _ => mul_nonneg (hw n) (sectorTrace_nonneg K N F n hx))]
  exact ENNReal.tsum_eq_iSup_nat.symm

theorem weightedTraceForm_rankOne (N : NormalTraceData R) (F : NormalFunctionalData R)
    (Tr : PositiveTraceData T) (hcone : Tr.positive ⊆ R.positive)
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (u : Space K) :
    (weightedTraceForm K N F Tr hcone w hw).expectation (R.rankOne u) =
      weightedForm K w u := by
  unfold PositiveForm.expectation
  change (⨆ M, ENNReal.ofReal (weightedTraceTruncation K F w M (R.rankOne u))) = _
  simp only [weightedTraceTruncation_apply, sectorTrace_rankOne]
  simp_rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => mul_nonneg (hw n) (sq_nonneg _))]
  exact ENNReal.tsum_eq_iSup_nat.symm

def numberTraceForm (N : NormalTraceData R) (F : NormalFunctionalData R)
    (Tr : PositiveTraceData T) (hcone : Tr.positive ⊆ R.positive) : PositiveForm Tr :=
  weightedTraceForm K N F Tr hcone (fun n => n) (fun n => Nat.cast_nonneg n)

theorem numberTraceForm_expectation (N : NormalTraceData R) (F : NormalFunctionalData R)
    (Tr : PositiveTraceData T) (hcone : Tr.positive ⊆ R.positive)
    {x : T} (hx : x ∈ R.positive) :
    (numberTraceForm K N F Tr hcone).expectation x =
      ∑' n : ℕ, ENNReal.ofReal ((n : ℝ) * (F.repr x (sector K n)).re) :=
  weightedTraceForm_expectation K N F Tr hcone _ _ hx

theorem numberTraceForm_rankOne (N : NormalTraceData R) (F : NormalFunctionalData R)
    (Tr : PositiveTraceData T) (hcone : Tr.positive ⊆ R.positive) (u : Space K) :
    (numberTraceForm K N F Tr hcone).expectation (R.rankOne u) = numberForm K u :=
  weightedTraceForm_rankOne K N F Tr hcone _ _ u

end GptLean.PhysicalFock
