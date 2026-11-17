import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Finite spectral cutoffs for the local photon compactness argument.

The orthonormal eigenbasis, positive eigenvalues and finiteness of spectral
sublevels are standard compact-resolvent data. The projection, its residual
norm, and the spectral tail estimate are constructed from those data.
-/

namespace GptLean.PhotonLocalization

open Filter Topology
open scoped InnerProductSpace ENNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A finite part of an orthonormal expansion, as an actual bounded operator. -/
noncomputable def basisProjection (b : HilbertBasis ℕ ℂ H) (t : Finset ℕ) : H →L[ℂ] H :=
  ∑ i ∈ t, (innerSL ℂ (b i)).smulRight (b i)

omit [CompleteSpace H] in
theorem basisProjection_apply (b : HilbertBasis ℕ ℂ H) (t : Finset ℕ) (v : H) :
    basisProjection b t v = ∑ i ∈ t, ⟪b i, v⟫_ℂ • b i := by
  simp [basisProjection]

omit [CompleteSpace H] in
theorem inner_basisProjection (b : HilbertBasis ℕ ℂ H) (t : Finset ℕ)
    (v : H) (i : ℕ) :
    ⟪b i, basisProjection b t v⟫_ℂ = if i ∈ t then ⟪b i, v⟫_ℂ else 0 := by
  classical
  simp [basisProjection_apply, inner_sum, inner_smul_right,
    orthonormal_iff_ite.mp b.orthonormal]

omit [CompleteSpace H] in
theorem basis_norm_sq (b : HilbertBasis ℕ ℂ H) (v : H) :
    ‖v‖ ^ 2 = ∑' i, ‖⟪b i, v⟫_ℂ‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, b.repr.norm_map,
    b.repr_apply_apply] using
    (lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (b.repr v))

omit [CompleteSpace H] in
theorem basisProjection_residual_sq (b : HilbertBasis ℕ ℂ H) (t : Finset ℕ) (v : H) :
    ‖v - basisProjection b t v‖ ^ 2 =
      ∑' i, if i ∈ t then 0 else ‖⟪b i, v⟫_ℂ‖ ^ 2 := by
  rw [basis_norm_sq b]
  apply tsum_congr
  intro i
  rw [inner_sub_right, inner_basisProjection]
  split_ifs <;> simp

omit [CompleteSpace H] in
theorem basisProjection_norm_le (b : HilbertBasis ℕ ℂ H) (t : Finset ℕ) (v : H) :
    ‖basisProjection b t v‖ ≤ ‖v‖ := by
  apply le_of_sq_le_sq _ (norm_nonneg v)
  rw [basis_norm_sq b, basis_norm_sq b]
  apply Summable.tsum_le_tsum
  · intro i
    rw [inner_basisProjection]
    split_ifs <;> simp
  · exact b.orthonormal.inner_products_summable _
  · exact b.orthonormal.inner_products_summable _

omit [CompleteSpace H] in
theorem basisProjection_idempotent (b : HilbertBasis ℕ ℂ H) (t : Finset ℕ) :
    IsIdempotentElem (basisProjection b t) := by
  apply ContinuousLinearMap.ext
  intro v
  apply b.repr.injective
  ext i
  simp only [mul_apply_eq_comp, b.repr_apply_apply, inner_basisProjection]
  split_ifs <;> simp_all

theorem basisProjection_selfAdjoint (b : HilbertBasis ℕ ℂ H) (t : Finset ℕ) :
    IsSelfAdjoint (basisProjection b t) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro u v
  simp only [ContinuousLinearMap.coe_coe, basisProjection_apply, sum_inner,
    inner_sum, inner_smul_left, inner_smul_right, inner_conj_symm]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem basisProjection_isStarProjection (b : HilbertBasis ℕ ℂ H) (t : Finset ℕ) :
    IsStarProjection (basisProjection b t) :=
  ⟨basisProjection_idempotent b t, basisProjection_selfAdjoint b t⟩

omit [CompleteSpace H] in
theorem basisProjection_finite_range (b : HilbertBasis ℕ ℂ H) (t : Finset ℕ) :
    FiniteDimensional ℂ (basisProjection b t).range := by
  let S : Submodule ℂ H := Submodule.span ℂ (b '' (↑t : Set ℕ))
  have : FiniteDimensional ℂ S :=
    FiniteDimensional.span_of_finite ℂ ((Finset.finite_toSet t).image b)
  apply Submodule.finiteDimensional_of_le (S₂ := S)
  rintro _ ⟨v, rfl⟩
  change basisProjection b t v ∈ S
  rw [basisProjection_apply]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨i, hi, rfl⟩

/-- The data provided by the compact-resolvent spectral theorem on the
bounded configuration region. No tail estimate is an input. -/
structure CompactSpectrum (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] where
  basis : HilbertBasis ℕ ℂ H
  eigenvalue : ℕ → ℝ
  one_le : ∀ i, 1 ≤ eigenvalue i
  finite_sublevel : ∀ s : ℕ, {i | eigenvalue i ≤ (s + 1 : ℝ)}.Finite

namespace CompactSpectrum

noncomputable def indices (K : CompactSpectrum H) (s : ℕ) : Finset ℕ :=
  (K.finite_sublevel s).toFinset

omit [CompleteSpace H] in
@[simp] theorem mem_indices (K : CompactSpectrum H) (s i : ℕ) :
    i ∈ K.indices s ↔ K.eigenvalue i ≤ (s + 1 : ℝ) := by
  simp [indices]

noncomputable def projection (K : CompactSpectrum H) (s : ℕ) : H →L[ℂ] H :=
  basisProjection K.basis (K.indices s)

theorem projection_isStarProjection (K : CompactSpectrum H) (s : ℕ) :
    IsStarProjection (K.projection s) :=
  basisProjection_isStarProjection K.basis (K.indices s)

omit [CompleteSpace H] in
theorem projection_finite_range (K : CompactSpectrum H) (s : ℕ) :
    FiniteDimensional ℂ (K.projection s).range :=
  basisProjection_finite_range K.basis (K.indices s)

noncomputable def form (K : CompactSpectrum H) (v : H) : ℝ :=
  ∑' i, K.eigenvalue i * ‖⟪K.basis i, v⟫_ℂ‖ ^ 2

/-- The finite-energy domain for the spectral form. -/
def FiniteEnergy (K : CompactSpectrum H) (v : H) : Prop :=
  Summable (fun i => K.eigenvalue i * ‖⟪K.basis i, v⟫_ℂ‖ ^ 2)

omit [CompleteSpace H] in
theorem residual_sq (K : CompactSpectrum H) (s : ℕ) (v : H) :
    ‖v - K.projection s v‖ ^ 2 =
      ∑' i, if K.eigenvalue i ≤ (s + 1 : ℝ) then 0 else ‖⟪K.basis i, v⟫_ℂ‖ ^ 2 := by
  simpa only [projection, mem_indices] using
    basisProjection_residual_sq K.basis (K.indices s) v

omit [CompleteSpace H] in
theorem spectral_tail_le (K : CompactSpectrum H) (s : ℕ) (v : H)
    (hv : K.FiniteEnergy v) :
    ‖v - K.projection s v‖ ^ 2 ≤ K.form v / (s + 1) := by
  have hd : (0 : ℝ) < s + 1 := by positivity
  rw [residual_sq, form, ← tsum_div_const]
  apply Summable.tsum_le_tsum
  · intro i
    split_ifs with hi
    · exact div_nonneg (mul_nonneg (le_trans zero_le_one (K.one_le i)) (sq_nonneg _)) hd.le
    · rw [le_div_iff₀ hd]
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_right (not_le.mp hi).le (sq_nonneg ‖⟪K.basis i, v⟫_ℂ‖)
  · have hs := K.basis.orthonormal.inner_products_summable v
    exact hs.of_nonneg_of_le (fun i => by split_ifs <;> positivity)
      (fun i => by split_ifs <;> simp)
  · exact hv.div_const _

omit [CompleteSpace H] in
/-- Summing over a spectral ensemble gives the actual mixed-state tail.
The only ensemble bound is its local form energy. -/
theorem ensemble_spectral_tail_le (K : CompactSpectrum H) (s : ℕ) (v : ℕ → H)
    (hv : ∀ a, K.FiniteEnergy (v a))
    (henergy : Summable (fun a => K.form (v a))) {E : ℝ}
    (hbound : ∑' a, K.form (v a) ≤ E) :
    ∑' a, ‖v a - K.projection s (v a)‖ ^ 2 ≤ E / (s + 1) := by
  have hs := henergy.div_const (s + 1 : ℝ)
  have hle := fun a => K.spectral_tail_le s (v a) (hv a)
  have hr : Summable (fun a => ‖v a - K.projection s (v a)‖ ^ 2) :=
    hs.of_nonneg_of_le (fun a => sq_nonneg _) hle
  calc
    _ ≤ ∑' a, K.form (v a) / (s + 1) := Summable.tsum_le_tsum hle hr hs
    _ = (∑' a, K.form (v a)) / (s + 1) := tsum_div_const
    _ ≤ E / (s + 1) := div_le_div_of_nonneg_right hbound (by positivity)

end CompactSpectrum

end GptLean.PhotonLocalization
