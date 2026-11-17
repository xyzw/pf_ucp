import GptLean.PhotonLocalizationLocalForms
import GptLean.PhotonLocalizationPhysicalTails

/-! The actual L² cutoff operators are commuting self-adjoint contractions.
Number-sector projections lift to the spatial L² space and finite sector
sums agree with the lifted number cutoff. -/

noncomputable section

namespace GptLean.PhotonLocalization

open MeasureTheory
open scoped ENNReal InnerProductSpace

variable {Ω K : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem realL2Multiplier_selfadjoint (a : Ω → ℝ) (ha : AEStronglyMeasurable a μ)
    (B : ℝ) (hb : ∀ᵐ x ∂μ, |a x| ≤ B) :
    IsSelfAdjoint (realL2Multiplier (K := K) a ha B hb) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro u v
  simp only [ContinuousLinearMap.coe_coe, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [realL2Multiplier_apply a ha B hb u,
    realL2Multiplier_apply a ha B hb v] with x hu hv
  rw [hu, hv, inner_smul_left_eq_smul, inner_smul_right_eq_smul]

omit [CompleteSpace K] in
theorem realL2Multiplier_commute_compLpL (a : Ω → ℝ)
    (ha : AEStronglyMeasurable a μ) (B : ℝ) (hb : ∀ᵐ x ∂μ, |a x| ≤ B)
    (P : K →L[ℂ] K) :
    Commute (realL2Multiplier a ha B hb) (P.compLpL 2 μ) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [realL2Multiplier_apply a ha B hb (P.compLpL 2 μ u),
    P.coeFn_compLpL u, P.coeFn_compLpL (realL2Multiplier a ha B hb u),
    realL2Multiplier_apply a ha B hb u] with x h₁ h₂ h₃ h₄
  change ((realL2Multiplier a ha B hb) ((P.compLpL 2 μ) u)) x =
    ((P.compLpL 2 μ) ((realL2Multiplier a ha B hb) u)) x
  rw [h₁, h₂, h₃, h₄, ← Complex.coe_smul, ← Complex.coe_smul, map_smul]

theorem compLpL_selfadjoint (P : K →L[ℂ] K) (hP : IsSelfAdjoint P) :
    IsSelfAdjoint (P.compLpL 2 μ) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro u v
  simp only [ContinuousLinearMap.coe_coe, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [P.coeFn_compLpL u, P.coeFn_compLpL v] with x hu hv
  rw [hu, hv]
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hP) _ _

theorem compLpL_projection (P : K →L[ℂ] K) (hP : IsStarProjection P) :
    IsStarProjection (P.compLpL 2 μ) := by
  refine ⟨?_, compLpL_selfadjoint P hP.isSelfAdjoint⟩
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [P.coeFn_compLpL u, P.coeFn_compLpL (P.compLpL 2 μ u)]
    with x hu hpu
  change ((P.compLpL 2 μ) ((P.compLpL 2 μ) u)) x = ((P.compLpL 2 μ) u) x
  rw [hpu, hu]
  exact congrArg (fun T : K →L[ℂ] K => T (u x)) hP.isIdempotentElem

omit [CompleteSpace K] in
theorem compLpL_zero : (0 : K →L[ℂ] K).compLpL 2 μ = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [(0 : K →L[ℂ] K).coeFn_compLpL u,
    Lp.coeFn_zero K 2 μ] with x hx hz
  simpa only [zero_apply, hz, Pi.zero_apply] using hx

omit [CompleteSpace K] in
theorem compLpL_sum {A : Type*} (s : Finset A) (P : A → K →L[ℂ] K) :
    (∑ a ∈ s, P a).compLpL 2 μ = ∑ a ∈ s, (P a).compLpL 2 μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using compLpL_zero (K := K) (μ := μ)
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        ContinuousLinearMap.add_compLpL, ih]

omit [CompleteSpace K] in
theorem numberSectorCutoff_compLpL (sector : ℕ → K →L[ℂ] K) (M : ℕ) :
    (numberSectorCutoff sector M).compLpL 2 μ =
      numberSectorCutoff (fun k => (sector k).compLpL 2 μ) M :=
  compLpL_sum _ _

theorem projection_norm_le (P : K →L[ℂ] K) (hP : IsStarProjection P) (v : K) :
    ‖P v‖ ≤ ‖v‖ :=
  (P.le_opNorm v).trans (by simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hP.norm_le (norm_nonneg v))

omit [CompleteSpace K] in
/-- Graph commutation for the finite number cutoff follows sector by
sector from the diagonal radiation operator. -/
theorem numberSectorCutoff_graph {R : K →ₗ.[ℂ] K}
    (sector : ℕ → K →L[ℂ] K)
    (hsector : ∀ k v w, (v, w) ∈ R.graph → (sector k v, sector k w) ∈ R.graph)
    (M : ℕ) (v w : K) (hvw : (v, w) ∈ R.graph) :
    (numberSectorCutoff sector M v, numberSectorCutoff sector M w) ∈ R.graph := by
  have h : (∑ k ∈ Finset.range (M + 1), (sector k v, sector k w)) ∈ R.graph :=
    R.graph.sum_mem fun k _ => hsector k v w hvw
  simpa only [numberSectorCutoff, sum_apply, ← prod_mk_sum] using h

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem SmoothElectronicCutoff.operator_selfadjoint (Z : SmoothElectronicCutoff I) :
    IsSelfAdjoint (Z.operator (K := K)) :=
  realL2Multiplier_selfadjoint _ _ _ _

omit [CompleteSpace K] in
theorem SmoothElectronicCutoff.operator_commute (Z : SmoothElectronicCutoff I)
    (P : K →L[ℂ] K) : Commute Z.operator (P.compLpL 2 volume) :=
  realL2Multiplier_commute_compLpL _ _ _ _ _

end GptLean.PhotonLocalization
