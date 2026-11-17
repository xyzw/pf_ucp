import GptLean.ElectronicLocalizationPartition

/-!
Tensor-gradient factorization for the electronic localization. The squared
derivative sum of the ordered tensor products equals the one-particle
derivative sum. The countable passage uses the active supports of the
one-particle partition and proves that derivatives vanish at inactive
labels, including their zero sets.
-/

noncomputable section

namespace GptLean.ElectronicLocalization

open Finset Filter
open scoped Topology

variable {A E : Type*} {N : ℕ}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem product_replace_slot (w d : Fin N → ℝ) (i : Fin N) :
    (∏ j, if j = i then d j else w j) = d i * ∏ j ∈ univ.erase i, w j := by
  classical
  rw [← prod_erase_mul _ _ (mem_univ i)]
  have hp : (∏ j ∈ univ.erase i, if j = i then d j else w j) =
      ∏ j ∈ univ.erase i, w j := by
    apply prod_congr rfl
    intro j hj
    exact ite_eq_right (mem_erase.mp hj).1
  rw [hp, ite_eq_left rfl, mul_comm]

theorem tensorMultiplier_fderiv_single (η : A → E → ℝ)
    (hd : ∀ a, Differentiable ℝ (η a)) (α : Fin N → A) (X : Fin N → E)
    (i : Fin N) (v : E) :
    fderiv ℝ (tensorMultiplier η α) X (Pi.single i v) =
      fderiv ℝ (η (α i)) (X i) v * ∏ j ∈ univ.erase i, η (α j) (X j) := by
  classical
  have hder : HasFDerivAt (tensorMultiplier η α)
      (∑ j, (∏ k ∈ univ.erase j, η (α k) (X k)) •
        (fderiv ℝ (η (α j)) (X j)).comp (ContinuousLinearMap.proj j)) X :=
    HasFDerivAt.finsetProd fun j _ =>
      (hd (α j) (X j)).hasFDerivAt.comp X (hasFDerivAt_apply j X)
  rw [hder.fderiv, _root_.sum_apply, sum_eq_single i]
  · simp [mul_comm]
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · intro hi
    exact False.elim (hi (mem_univ i))

/-- Exact factorization of the countable ordered tensor-gradient sum. -/
theorem tensorMultiplier_single_hasSum_sq (η : A → E → ℝ)
    (hloc : LocallyFinite (fun a => Function.support (η a)))
    (hd : ∀ a, Differentiable ℝ (η a)) (hpos : ∀ a x, 0 ≤ η a x)
    (hpart : ∀ x, HasSum (fun a => η a x ^ 2) 1)
    (X : Fin N → E) (i : Fin N) (v : E) :
    HasSum (fun α : Fin N → A => fderiv ℝ (tensorMultiplier η α) X (Pi.single i v) ^ 2)
      (∑' a, fderiv ℝ (η a) (X i) v ^ 2) := by
  classical
  let s : Fin N → Finset A := fun j => (hloc.point_finite (X j)).toFinset
  have hz : ∀ j a, a ∉ s j → η a (X j) = 0 := by
    intro j a ha
    by_contra h
    exact ha ((hloc.point_finite (X j)).mem_toFinset.mpr h)
  have hdz : ∀ j a, a ∉ s j → fderiv ℝ (η a) (X j) v = 0 := by
    intro j a ha
    rw [fderiv_eq_zero_of_nonneg (hpos a) (hz j a ha)]
    rfl
  have hds : HasSum (fun a => fderiv ℝ (η a) (X i) v ^ 2)
      (∑ a ∈ s i, fderiv ℝ (η a) (X i) v ^ 2) :=
    hasSum_sum_of_ne_finset_zero fun a ha => by simp [hdz i a ha]
  have hs : ∀ j, ∑ a ∈ s j, η a (X j) ^ 2 = 1 := by
    intro j
    exact (hasSum_sum_of_ne_finset_zero (fun a ha => by rw [hz j a ha]; norm_num)).unique
      (hpart (X j))
  have hslot (α : Fin N → A) :
      fderiv ℝ (tensorMultiplier η α) X (Pi.single i v) ^ 2 =
        ∏ j, if j = i then fderiv ℝ (η (α j)) (X j) v ^ 2 else η (α j) (X j) ^ 2 := by
    rw [tensorMultiplier_fderiv_single η hd, mul_pow, ← prod_pow, product_replace_slot]
  have hsum : (∑ α ∈ Fintype.piFinset s,
      fderiv ℝ (tensorMultiplier η α) X (Pi.single i v) ^ 2) =
      ∑' a, fderiv ℝ (η a) (X i) v ^ 2 := by
    simp_rw [hslot]
    rw [← prod_univ_sum s (fun j a =>
      if j = i then fderiv ℝ (η a) (X j) v ^ 2 else η a (X j) ^ 2), prod_eq_single i]
    · simpa using hds.tsum_eq.symm
    · intro j _ hji
      simp only [ite_eq_right hji, hs j]
    · intro hi
      exact False.elim (hi (mem_univ i))
  rw [← hsum]
  apply hasSum_sum_of_ne_finset_zero
  intro α hα
  obtain ⟨j, hj⟩ : ∃ j, α j ∉ s j := by
    simpa only [Fintype.mem_piFinset, not_forall] using hα
  rw [hslot]
  apply prod_eq_zero (mem_univ j)
  split_ifs <;> simp [hz j (α j) hj, hdz j (α j) hj]

theorem permutedTensor_fderiv_single (η : A → E → ℝ)
    (hd : ∀ a, Differentiable ℝ (η a)) (α : Fin N → A) (X : Fin N → E)
    (π : Equiv.Perm (Fin N)) (i : Fin N) (v : E) :
    fderiv ℝ (fun Y : Fin N → E => tensorMultiplier η α (Y ∘ π)) X (Pi.single i v) =
      fderiv ℝ (tensorMultiplier η α) (X ∘ π) (Pi.single (π.symm i) v) := by
  classical
  let P : (Fin N → E) →L[ℝ] (Fin N → E) :=
    ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (π j)
  have ht : Differentiable ℝ (tensorMultiplier η α) := by
    simpa only [Equiv.coe_refl, Function.comp_id] using
      permutedTensor_differentiable η hd α (Equiv.refl (Fin N))
  have h := (ht (X ∘ π)).hasFDerivAt.comp X (P.hasFDerivAt)
  have heq : P (Pi.single i v) = Pi.single (π.symm i) v := by
    ext j
    change (Pi.single i v : Fin N → E) (π j) = (Pi.single (π.symm i) v : Fin N → E) j
    simp only [Pi.single_apply]
    by_cases hj : j = π.symm i
    · simp [hj]
    · have hπ : π j ≠ i := by
        intro heq
        apply hj
        rw [← heq, π.symm_apply_apply]
      simp [hj, hπ]
  change fderiv ℝ (tensorMultiplier η α ∘ P) X (Pi.single i v) = _
  rw [h.fderiv, ContinuousLinearMap.comp_apply, heq]

/-- Symmetrization does not increase the countable derivative metric in
any one-particle direction. -/
theorem symmetricMultiplier_single_metric_le (η : A → E → ℝ)
    (hloc : LocallyFinite (fun a => Function.support (η a)))
    (hd : ∀ a, Differentiable ℝ (η a)) (hpos : ∀ a x, 0 ≤ η a x)
    (hpart : ∀ x, HasSum (fun a => η a x ^ 2) 1)
    (X : Fin N → E) (i : Fin N) (v : E) :
    (∑' α : Fin N → A,
      fderiv ℝ (symmetricMultiplier η α) X (Pi.single i v) ^ 2) ≤
      ∑' a, fderiv ℝ (η a) (X i) v ^ 2 := by
  classical
  have hs : ∀ π : Equiv.Perm (Fin N), HasSum
      (fun α : Fin N → A => fderiv ℝ
        (fun Y : Fin N → E => tensorMultiplier η α (Y ∘ π)) X (Pi.single i v) ^ 2)
      (∑' a, fderiv ℝ (η a) (X i) v ^ 2) := by
    intro π
    simpa only [permutedTensor_fderiv_single η hd, Function.comp_apply,
      Equiv.apply_symm_apply] using
      tensorMultiplier_single_hasSum_sq η hloc hd hpos hpart (X ∘ π) (π.symm i) v
  have hc : (Fintype.card (Equiv.Perm (Fin N)) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := Equiv.Perm (Fin N)))
  have hbound := (hasSum_sum (s := (univ : Finset (Equiv.Perm (Fin N))))
    (fun π _ => hs π)).div_const (Fintype.card (Equiv.Perm (Fin N)) : ℝ)
  have hboundval : (∑ π : Equiv.Perm (Fin N),
      (∑' a, fderiv ℝ (η a) (X i) v ^ 2)) /
      Fintype.card (Equiv.Perm (Fin N)) = ∑' a, fderiv ℝ (η a) (X i) v ^ 2 := by
    simp only [sum_const, card_univ, nsmul_eq_mul]
    field_simp
  rw [hboundval] at hbound
  have hsum : Summable (fun α : Fin N → A =>
      fderiv ℝ (symmetricMultiplier η α) X (Pi.single i v) ^ 2) := by
    apply summable_of_hasFiniteSupport
    apply ((symmetricMultiplier_locallyFinite η hloc).point_finite X).subset
    intro α hα
    change symmetricMultiplier η α X ≠ 0
    intro hzero
    apply hα
    change fderiv ℝ (symmetricMultiplier η α) X (Pi.single i v) ^ 2 = 0
    rw [fderiv_eq_zero_of_nonneg (symmetricMultiplier_nonneg η α) hzero]
    simp
  exact (hsum.tsum_le_tsum
    (fun α => symmetricMultiplier_derivative_sq_le η hd hpos α X (Pi.single i v))
    hbound.summable).trans_eq hbound.tsum_eq

/-- The many-particle RMS metric has the required scale once the standard
one-particle partition has its gradient bound. The factor is exactly N. -/
theorem symmetricMultiplier_total_metric_le {J : Type*} [Fintype J]
    (η : A → E → ℝ) (directions : J → E)
    (hloc : LocallyFinite (fun a => Function.support (η a)))
    (hd : ∀ a, Differentiable ℝ (η a)) (hpos : ∀ a x, 0 ≤ η a x)
    (hpart : ∀ x, HasSum (fun a => η a x ^ 2) 1)
    (B : ℝ) (hmetric : ∀ x, (∑ j, ∑' a, fderiv ℝ (η a) x (directions j) ^ 2) ≤ B)
    (X : Fin N → E) :
    (∑ i, ∑ j, ∑' α : Fin N → A,
      fderiv ℝ (symmetricMultiplier η α) X (Pi.single i (directions j)) ^ 2) ≤ N * B := by
  calc
    _ ≤ ∑ i : Fin N, ∑ j : J, ∑' a, fderiv ℝ (η a) (X i) (directions j) ^ 2 := by
      apply sum_le_sum
      intro i _
      apply sum_le_sum
      intro j _
      exact symmetricMultiplier_single_metric_le η hloc hd hpos hpart X i (directions j)
    _ ≤ ∑ _i : Fin N, B := sum_le_sum fun i _ => hmetric (X i)
    _ = N * B := by simp

end GptLean.ElectronicLocalization
