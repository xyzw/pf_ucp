import GptLean.CompactGraphProjection

/-!
Trace compactness from the actual compact local graph inclusions. Local
graph spaces may vary with both cutoffs. Finite-rank projections and their
trace errors are derived from compactness, without a common eigenbasis.
-/

noncomputable section
namespace GptLean.PhotonLocalization

open Filter Topology MeasureTheory PhotonTrace

variable {H Ω : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [MeasurableSpace Ω] {μ : Measure Ω}

structure GraphLocalFormData
    (region : ℕ → Set Ω) (ρ : ℕ → Lp ℝ 1 μ)
    (φ : ℕ → (H →L[ℂ] H) →L[ℂ] ℂ)
    (V : ℕ → ℕ → Type*) [∀ L M, NormedAddCommGroup (V L M)]
    [∀ L M, NormedSpace ℂ (V L M)] where
  numberCutoff : ℕ → H →L[ℂ] H
  electronicCutoff : ℕ → H →L[ℂ] H
  number_projection : ∀ M, IsStarProjection (numberCutoff M)
  electronic_selfadjoint : ∀ L, IsSelfAdjoint (electronicCutoff L)
  commute : ∀ L M, Commute (electronicCutoff L) (numberCutoff M)
  inclusion : ∀ L M, V L M →L[ℂ] H
  compact : ∀ L M, TotallyBounded (inclusion L M '' Metric.closedBall 0 1)
  source : ℕ → ℕ → H
  localVector : ∀ L M, ℕ → ℕ → V L M
  trace : ∀ n (a : H →L[ℂ] H),
    (φ n (star a * a)).re = ∑' k, ‖a (source n k)‖ ^ 2
  local_identity : ∀ L M n k,
    (electronicCutoff L * numberCutoff M) (source n k) =
      inclusion L M (localVector L M n k)
  local_summable : ∀ L M n, Summable (fun k => ‖localVector L M n k‖ ^ 2)
  energy : ℕ → ℝ
  local_energy : ∀ L M n, ∑' k, ‖localVector L M n k‖ ^ 2 ≤ energy L
  numberBound : ℝ
  number_tail : ∀ M n, (φ n (1 - numberCutoff M)).re ≤ numberBound / (M + 1)
  electronic_tail : ∀ L n,
    (φ n ((1 - electronicCutoff L) ^ 2)).re ≤ densityTail region L (ρ n)

variable {V : ℕ → ℕ → Type*} [∀ L M, NormedAddCommGroup (V L M)]
  [∀ L M, NormedSpace ℂ (V L M)]
  {region : ℕ → Set Ω} {ρ : ℕ → Lp ℝ 1 μ}
  {φ : ℕ → (H →L[ℂ] H) →L[ℂ] ℂ}

namespace GraphLocalFormData

variable (F : GraphLocalFormData region ρ φ V)

def projection (L M s : ℕ) : H →L[ℂ] H :=
  (exists_projection_graph_tail (F.inclusion L M) (F.compact L M) s).choose

theorem projection_finite (L M s : ℕ) : IsFiniteRankProj (F.projection L M s) :=
  (exists_projection_graph_tail (F.inclusion L M) (F.compact L M) s).choose_spec.1

theorem projection_tail (L M s : ℕ) (v : V L M) :
    ‖(1 - F.projection L M s) (F.inclusion L M v)‖ ^ 2 ≤ ‖v‖ ^ 2 / (s + 1) :=
  (exists_projection_graph_tail (F.inclusion L M) (F.compact L M) s).choose_spec.2 v

theorem trace_tail (L M s n : ℕ) :
    (φ n (star (F.electronicCutoff L * F.numberCutoff M) *
      (1 - F.projection L M s) * (F.electronicCutoff L * F.numberCutoff M))).re ≤
        F.energy L / (s + 1) := by
  rw [star_mul_proj_mul (F.projection_finite L M s).isStarProjection.one_sub, F.trace]
  have hpoint (k : ℕ) :
      ‖((1 - F.projection L M s) * (F.electronicCutoff L * F.numberCutoff M))
        (F.source n k)‖ ^ 2 ≤ ‖F.localVector L M n k‖ ^ 2 / (s + 1) := by
    simpa only [mul_apply_eq_comp, F.local_identity] using
      F.projection_tail L M s (F.localVector L M n k)
  have hsum := (F.local_summable L M n).div_const (s + 1 : ℝ)
  have hnonneg (k : ℕ) : 0 ≤
      ‖((1 - F.projection L M s) * (F.electronicCutoff L * F.numberCutoff M))
        (F.source n k)‖ ^ 2 := sq_nonneg _
  apply (Summable.tsum_le_tsum hpoint (hsum.of_nonneg_of_le hnonneg hpoint) hsum).trans
  rw [tsum_div_const]
  exact div_le_div_of_nonneg_right (F.local_energy L M n) (by positivity)

def compressionWitness
    (hφ : ∀ n, IsPosFunctional (φ n)) (hmass : ∀ n, (φ n 1).re ≤ 1)
    {mass : ℝ} (hρmass : ∀ n, ‖ρ n‖ ≤ mass) (htight : DensityTight region ρ) :
    CompressionWitness ((H →L[ℂ] H) →L[ℂ] ℂ) φ :=
  PhotonTrace.compressionWitness_of_density region ρ hρmass htight φ hφ hmass
    F.numberCutoff F.electronicCutoff F.projection
    F.number_projection F.electronic_selfadjoint F.commute F.projection_finite
    F.numberBound F.energy F.number_tail F.electronic_tail F.trace_tail

include F in
theorem totallyBounded
    (hφ : ∀ n, IsPosFunctional (φ n)) (hmass : ∀ n, (φ n 1).re ≤ 1)
    {mass : ℝ} (hρmass : ∀ n, ‖ρ n‖ ≤ mass) (htight : DensityTight region ρ) :
    TotallyBounded (Set.range φ) :=
  (compressionWitness F hφ hmass hρmass htight).totallyBounded

include F in
theorem totallyBounded_of_density_tendsto
    (hφ : ∀ n, IsPosFunctional (φ n)) (hmass : ∀ n, (φ n 1).re ≤ 1)
    (hmeasurable : ∀ L, MeasurableSet (region L))
    (hmono : Monotone region) (hexhaust : ⋃ L, region L = Set.univ)
    {ρlimit : Lp ℝ 1 μ} (hρ : Tendsto ρ atTop (𝓝 ρlimit)) :
    TotallyBounded (Set.range φ) := by
  obtain ⟨mass, hmassρ⟩ := hρ.norm.bddAbove_range
  exact totallyBounded F hφ hmass (fun n => hmassρ (Set.mem_range_self n))
    (densityTight_of_tendsto region hmeasurable hmono hexhaust hρ)

end GraphLocalFormData
end GptLean.PhotonLocalization
