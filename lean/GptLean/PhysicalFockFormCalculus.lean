import GptLean.PhysicalFockFormPullback
import GptLean.PhysicalNormalTrace
import GptLean.PhotonLocalizationChannelMeasurement
import GptLean.PhotonLocalizationFormBoundsFock

/-!
Actual additive Fock forms from countable one-photon kernel families.

Their bounded trace approximants are finite sums of actual annihilation
blocks squared. Parseval and the full channel pullback identify these
observables with the concrete one-photon slices. Thus the Fock form
calculus is constructed on the same Fock and normal trace realization.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory PhotonLocalizationChannel PhysicalNormalTrace RemovalState
open PhotonLocalizationFormBounds
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types false

section TraceSquares
variable {H T : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : Gaussian.RankOneData H T} (normal : NormalTraceData R) (F : NormalFunctionalData R)

def squareFunctional (A : H →L[ℂ] H) : T →L[ℝ] ℝ :=
  Complex.reCLM.comp (((ContinuousLinearMap.apply ℂ ℂ (A.adjoint.comp A)).restrictScalars ℝ).comp F.repr)

omit [CompleteSpace T] in
@[simp] theorem squareFunctional_rankOne (A : H →L[ℂ] H) (v : H) :
    squareFunctional F A (R.rankOne v) = ‖A v‖ ^ 2 := by
  change (F.repr (R.rankOne v) (A.adjoint.comp A)).re = _
  rw [F.rankOne]
  change (⟪v, A.adjoint (A v)⟫_ℂ).re = _
  rw [A.adjoint_inner_right]
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) (A v)).symm

def squareSeriesTruncation (A : ℕ → H →L[ℂ] H) (M : ℕ) : T →L[ℝ] ℝ :=
  ∑ n ∈ Finset.range M, squareFunctional F (A n)

omit [CompleteSpace T] in
@[simp] theorem squareSeriesTruncation_rankOne (A : ℕ → H →L[ℂ] H) (M : ℕ) (v : H) :
    squareSeriesTruncation F A M (R.rankOne v) = ∑ n ∈ Finset.range M, ‖A n v‖ ^ 2 := by
  simp only [squareSeriesTruncation, sum_apply, squareFunctional_rankOne]

def squareSeriesForm (A : ℕ → H →L[ℂ] H) : PositiveForm (positiveTrace normal F) where
  truncation := squareSeriesTruncation F A
  nonneg M x hx := normal.observable_nonneg _ (fun v => by
    rw [squareSeriesTruncation_rankOne]
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hx
  monotone x hx M L hML := by
    have hp := normal.observable_nonneg
      (squareSeriesTruncation F A L - squareSeriesTruncation F A M)
      (fun v => by
        simp only [sub_apply, squareSeriesTruncation_rankOne]
        exact sub_nonneg.mpr (Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono hML) (fun _ _ _ => sq_nonneg _))) hx
    exact sub_nonneg.mp hp

theorem squareSeriesForm_rankOne (A : ℕ → H →L[ℂ] H) (v : H) :
    (squareSeriesForm normal F A).expectation (R.rankOne v) =
      ∑' n, ENNReal.ofReal (‖A n v‖ ^ 2) := by
  change (⨆ M, ENNReal.ofReal (squareSeriesTruncation F A M (R.rankOne v))) = _
  simp only [squareSeriesTruncation_rankOne]
  simp_rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => sq_nonneg (‖A n v‖))]
  exact ENNReal.tsum_eq_iSup_nat.symm

end TraceSquares

private theorem ennreal_tsum_unpair (t : ℕ → ℕ → ℝ≥0∞) :
    (∑' n : ℕ, t n.unpair.1 n.unpair.2) = ∑' i, ∑' j, t i j :=
  ((Nat.pairEquiv.symm.tsum_eq (fun p : ℕ × ℕ => t p.1 p.2))).trans ENNReal.tsum_prod'

private theorem fockForm_tsum {h : Type*} (q : ℕ → h → ℝ≥0∞)
    (slice : (m : ℕ) → Fin m → ℕ → h) :
    fockForm (fun u => ∑' k, q k u) slice = ∑' k, fockForm (q k) slice := by
  unfold fockForm sectorForm
  simp_rw [← tsum_fintype (L := SummationFilter.unconditional _)]
  calc
    _ = ∑' m, ∑' i : Fin m, ∑' k, ∑' a, q k (slice m i a) :=
      tsum_congr (fun _ => tsum_congr (fun _ => ENNReal.tsum_comm))
    _ = ∑' m, ∑' k, ∑' i : Fin m, ∑' a, q k (slice m i a) :=
      tsum_congr (fun _ => ENNReal.tsum_comm)
    _ = _ := ENNReal.tsum_comm

abbrev OnePhotonFormFamily := ℕ → Lp ℂ 2 photonMeasure

def onePhotonFamilyValue (q : OnePhotonFormFamily) (u : Lp ℂ 2 photonMeasure) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (‖⟪q i, u⟫_ℂ‖ ^ 2)

def familyBlock (q : OnePhotonFormFamily) (n : ℕ) : PhotonFock →L[ℂ] PhotonFock :=
  annihilationBlock photonMeasure n.unpair.2 (q n.unpair.1)

section Normal
variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : Gaussian.RankOneData PhotonFock T} (normal : NormalTraceData R) (F : NormalFunctionalData R)

def familyObservable (q : OnePhotonFormFamily) : PositiveForm (positiveTrace normal F) :=
  squareSeriesForm normal F (familyBlock q)

theorem familyObservable_rankOne (q : OnePhotonFormFamily) (u : PhotonFock) :
    (familyObservable normal F q).expectation (R.rankOne u) =
      ∑' i, annihilationForm photonMeasure (q i) u := by
  calc
    _ = ∑' n, ENNReal.ofReal (‖familyBlock q n u‖ ^ 2) := squareSeriesForm_rankOne normal F _ u
    _ = ∑' i, ∑' n, ENNReal.ofReal (‖annihilationBlock photonMeasure n (q i) u‖ ^ 2) :=
      ennreal_tsum_unpair (fun i n => ENNReal.ofReal (‖annihilationBlock photonMeasure n (q i) u‖ ^ 2))
    _ = _ := tsum_congr (fun i => (annihilationForm_eq_blocks photonMeasure (q i) u).symm)

theorem familyObservable_slices (q : OnePhotonFormFamily) (u : PhotonFock) :
    (familyObservable normal F q).expectation (R.rankOne u) =
      fockForm (onePhotonFamilyValue q) (fockSlices u) := by
  exact (familyObservable_rankOne normal F q u).trans
    ((tsum_congr (fun i => (fockSlices_annihilationForm (q i) u).symm)).trans
      (fockForm_tsum (fun i g => ENNReal.ofReal (‖⟪q i, g⟫_ℂ‖ ^ 2)) (fockSlices u)).symm)

theorem familyObservable_pullback
    (BF : StandardSymmetricFockExponential) (CCR : CanonicalSectorCCR photonMeasure)
    (j : Lp ℂ 2 photonMeasure →ₗᵢ[ℂ]
      WithLp 2 (Lp ℂ 2 photonMeasure × Lp ℂ 2 photonMeasure))
    (q : OnePhotonFormFamily) (u : PhotonFock) :
    (∑' a, (familyObservable normal F q).expectation
      (R.rankOne ((photonFactorization BF).factor j u a))) =
      fockForm (fun v => onePhotonFamilyValue q (PhotonLocalizationFockChannel.retainedMap j v))
        (fockSlices u) := by
  let q' : OnePhotonFormFamily := fun i => (PhotonLocalizationFockChannel.retainedMap j).adjoint (q i)
  have hval (v : Lp ℂ 2 photonMeasure) : onePhotonFamilyValue q' v =
      onePhotonFamilyValue q (PhotonLocalizationFockChannel.retainedMap j v) := by
    apply tsum_congr
    intro i
    exact congrArg (fun z : ℂ => ENNReal.ofReal (‖z‖ ^ 2))
      ((PhotonLocalizationFockChannel.retainedMap j).adjoint_inner_left v (q i))
  calc
    _ = ∑' a, ∑' i, annihilationForm photonMeasure (q i) ((photonFactorization BF).factor j u a) :=
      tsum_congr (fun a => familyObservable_rankOne normal F q _)
    _ = ∑' i, ∑' a, annihilationForm photonMeasure (q i) ((photonFactorization BF).factor j u a) :=
      ENNReal.tsum_comm
    _ = ∑' i, annihilationForm photonMeasure (q' i) u :=
      tsum_congr (fun i => photonFactorization_annihilationForm BF CCR j (q i) u)
    _ = fockForm (onePhotonFamilyValue q') (fockSlices u) :=
      (familyObservable_rankOne normal F q' u).symm.trans (familyObservable_slices normal F q' u)
    _ = _ := congrArg (fun v => fockForm v (fockSlices u)) (funext hval)

/-- The form calculus on the constructed photon channel and the same normal trace space. -/
def photonFormCalculus (BF : StandardSymmetricFockExponential)
    (CCR : CanonicalSectorCCR photonMeasure) :
    FockFormCalculus R (positiveTrace normal F) (photonFactorization BF) OnePhotonFormFamily where
  value := onePhotonFamilyValue
  observable := familyObservable normal F
  slice := fockSlices
  rankOne := familyObservable_slices normal F
  pullback := familyObservable_pullback normal F BF CCR

end Normal
end GptLean.PhysicalFock
