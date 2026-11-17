import GptLean.ElectronicLocalization
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Data.Fintype.Perm

/-!
The actual symmetric electronic partition, obtained from a standard
nonnegative locally finite one-particle square partition. Ordered spatial
labels retain finite orbit multiplicities. Permutation averaging removes
these multiplicities from the square sum and makes every multiplier
symmetric in the electronic positions.
-/

noncomputable section

namespace GptLean.ElectronicLocalization

open Finset Filter
open scoped Topology

variable {A E : Type*} {N : ℕ}

def tensorMultiplier (η : A → E → ℝ) (α : Fin N → A) (X : Fin N → E) : ℝ :=
  ∏ i, η (α i) (X i)

def symmetricMultiplier (η : A → E → ℝ) (α : Fin N → A) (X : Fin N → E) : ℝ :=
  rms (fun π : Equiv.Perm (Fin N) => tensorMultiplier η α (X ∘ π)) /
    Real.sqrt (Fintype.card (Equiv.Perm (Fin N)))

theorem tensorMultiplier_nonneg (η : A → E → ℝ) (hη : ∀ a x, 0 ≤ η a x)
    (α : Fin N → A) (X : Fin N → E) : 0 ≤ tensorMultiplier η α X :=
  prod_nonneg fun i _ => hη (α i) (X i)

theorem symmetricMultiplier_nonneg (η : A → E → ℝ) (α : Fin N → A)
    (X : Fin N → E) : 0 ≤ symmetricMultiplier η α X :=
  div_nonneg (rms_nonneg _) (Real.sqrt_nonneg _)

theorem symmetricMultiplier_sq (η : A → E → ℝ) (α : Fin N → A) (X : Fin N → E) :
    symmetricMultiplier η α X ^ 2 =
      (∑ π : Equiv.Perm (Fin N), tensorMultiplier η α (X ∘ π) ^ 2) /
        Fintype.card (Equiv.Perm (Fin N)) := by
  rw [symmetricMultiplier, div_pow, rms_sq, Real.sq_sqrt (by positivity)]

theorem symmetricMultiplier_perm (η : A → E → ℝ) (α : Fin N → A)
    (X : Fin N → E) (τ : Equiv.Perm (Fin N)) :
    symmetricMultiplier η α (X ∘ τ) = symmetricMultiplier η α X := by
  unfold symmetricMultiplier rms
  congr 2
  simpa only [Equiv.coe_mulLeft, Equiv.Perm.coe_mul, Function.comp_assoc] using
    Equiv.sum_comp (Equiv.mulLeft τ)
      (fun π : Equiv.Perm (Fin N) => tensorMultiplier η α (X ∘ π) ^ 2)

variable [NormedAddCommGroup E]

theorem tensorMultiplier_hasSum_sq (η : A → E → ℝ)
    (hloc : LocallyFinite (fun a => Function.support (η a)))
    (hpart : ∀ x, HasSum (fun a => η a x ^ 2) 1) (X : Fin N → E) :
    HasSum (fun α : Fin N → A => tensorMultiplier η α X ^ 2) 1 := by
  classical
  let s : Fin N → Finset A := fun i => (hloc.point_finite (X i)).toFinset
  have hz : ∀ i a, a ∉ s i → η a (X i) = 0 := by
    intro i a ha
    by_contra h
    exact ha ((hloc.point_finite (X i)).mem_toFinset.mpr h)
  have hs : ∀ i, ∑ a ∈ s i, η a (X i) ^ 2 = 1 := by
    intro i
    exact (hasSum_sum_of_ne_finset_zero (fun a ha => by rw [hz i a ha]; norm_num)).unique
      (hpart (X i))
  have ht : ∑ α ∈ Fintype.piFinset s, tensorMultiplier η α X ^ 2 = 1 := by
    simp only [tensorMultiplier, ← prod_pow]
    rw [← prod_univ_sum s (fun i a => η a (X i) ^ 2)]
    simp [hs]
  rw [← ht]
  apply hasSum_sum_of_ne_finset_zero
  intro α hα
  have hex : ∃ i, α i ∉ s i := by simpa only [Fintype.mem_piFinset, not_forall] using hα
  obtain ⟨i, hi⟩ := hex
  have hzprod : tensorMultiplier η α X = 0 :=
    prod_eq_zero (mem_univ i) (hz i (α i) hi)
  simp [hzprod]

/-- The infinite square sum is proved from the one-particle partition by
finite active tensor expansion and finite permutation averaging. -/
theorem symmetricMultiplier_hasSum_sq (η : A → E → ℝ)
    (hloc : LocallyFinite (fun a => Function.support (η a)))
    (hpart : ∀ x, HasSum (fun a => η a x ^ 2) 1) (X : Fin N → E) :
    HasSum (fun α : Fin N → A => symmetricMultiplier η α X ^ 2) 1 := by
  have hc : (Fintype.card (Equiv.Perm (Fin N)) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := Equiv.Perm (Fin N)))
  have h := (hasSum_sum (s := (univ : Finset (Equiv.Perm (Fin N))))
    (fun π _ => tensorMultiplier_hasSum_sq η hloc hpart (X ∘ π))).div_const
      (Fintype.card (Equiv.Perm (Fin N)) : ℝ)
  simpa only [symmetricMultiplier_sq, sum_const, card_univ, nsmul_eq_mul, mul_one,
    div_self hc] using h

theorem locallyFinite_support_of_local_active_finset {B Y : Type*}
    [TopologicalSpace Y] (f : B → Y → ℝ)
    (h : ∀ x, ∃ s : Finset B, ∀ᶠ y in 𝓝 x, ∀ b ∉ s, f b y = 0) :
    LocallyFinite (fun b => Function.support (f b)) := by
  classical
  intro x
  obtain ⟨s, hs⟩ := h x
  refine ⟨{y | ∀ b ∉ s, f b y = 0}, hs, s.finite_toSet.subset ?_⟩
  rintro b ⟨y, hy, hy0⟩
  by_contra hb
  exact hy (hy0 b hb)

/-- A finite configuration of locally finite one-particle supports has a
locally finite family of tensor supports, even for infinitely many labels. -/
theorem tensorMultiplier_locallyFinite (η : A → E → ℝ)
    (hloc : LocallyFinite (fun a => Function.support (η a))) :
    LocallyFinite (fun α : Fin N → A => Function.support (tensorMultiplier η α)) := by
  classical
  apply locallyFinite_support_of_local_active_finset
  intro X
  choose s hs using fun i : Fin N => exists_local_active_finset η hloc (X i)
  refine ⟨Fintype.piFinset s, ?_⟩
  have hnear : ∀ᶠ Y : Fin N → E in 𝓝 X, ∀ i a, a ∉ s i → η a (Y i) = 0 :=
    Filter.eventually_all.mpr fun i => (continuous_apply i).continuousAt.eventually (hs i)
  filter_upwards [hnear] with Y hY α hα
  obtain ⟨i, hi⟩ : ∃ i, α i ∉ s i := by
    simpa only [Fintype.mem_piFinset, not_forall] using hα
  exact prod_eq_zero (mem_univ i) (hY i (α i) hi)

/-- A finite RMS combination preserves local finiteness of the label family. -/
theorem rms_locallyFinite {B J Y : Type*} [Fintype J] [TopologicalSpace Y]
    (g : J → B → Y → ℝ)
    (hg : ∀ j, LocallyFinite (fun b => Function.support (g j b))) :
    LocallyFinite (fun b => Function.support (fun y => rms (fun j => g j b y))) := by
  classical
  intro y
  choose U hU hfin using fun j => hg j y
  let s : Finset B := univ.biUnion fun j => (hfin j).toFinset
  have hnear : (⋂ j, U j) ∈ 𝓝 y := Filter.iInter_mem.mpr hU
  refine ⟨⋂ j, U j, hnear, s.finite_toSet.subset ?_⟩
  rintro b ⟨z, hz, hzU⟩
  by_contra hb
  apply hz
  apply (rms_eq_zero_iff _).mpr
  intro j
  by_contra hnonzero
  apply hb
  exact mem_biUnion.mpr ⟨j, mem_univ j,
    (hfin j).mem_toFinset.mpr ⟨z, hnonzero, Set.mem_iInter.mp hzU j⟩⟩

theorem symmetricMultiplier_locallyFinite (η : A → E → ℝ)
    (hloc : LocallyFinite (fun a => Function.support (η a))) :
    LocallyFinite (fun α : Fin N → A => Function.support (symmetricMultiplier η α)) := by
  have ht := tensorMultiplier_locallyFinite (N := N) η hloc
  have hp : ∀ π : Equiv.Perm (Fin N),
      LocallyFinite (fun α => Function.support (fun X : Fin N → E =>
        tensorMultiplier η α (X ∘ π))) := fun π =>
    ht.preimage_continuous (continuous_pi fun i => continuous_apply (π i))
  exact (rms_locallyFinite _ hp).subset fun α X hX hzero =>
    hX (by simp only [symmetricMultiplier, hzero, zero_div])

variable [NormedSpace ℝ E]

theorem permutedTensor_differentiable (η : A → E → ℝ)
    (hd : ∀ a, Differentiable ℝ (η a)) (α : Fin N → A)
    (π : Equiv.Perm (Fin N)) :
    Differentiable ℝ (fun Y : Fin N → E => tensorMultiplier η α (Y ∘ π)) := by
  intro X
  exact (HasFDerivAt.finsetProd (fun i (_ : i ∈ univ) =>
    ((hd (α i)).comp (differentiable_apply (π i)) X).hasFDerivAt)).differentiableAt

theorem symmetricMultiplier_differentiable (η : A → E → ℝ)
    (hd : ∀ a, Differentiable ℝ (η a)) (hpos : ∀ a x, 0 ≤ η a x)
    (α : Fin N → A) : Differentiable ℝ (symmetricMultiplier η α) := by
  intro X
  change DifferentiableAt ℝ (fun Y => rms (fun π : Equiv.Perm (Fin N) =>
    tensorMultiplier η α (Y ∘ π)) / Real.sqrt (Fintype.card (Equiv.Perm (Fin N)))) X
  simpa only [div_eq_mul_inv, mul_comm] using
    ((rms_hasFDerivAt _ (permutedTensor_differentiable η hd α)
      (fun π Y => tensorMultiplier_nonneg η hpos α (Y ∘ π)) X).const_mul
        (Real.sqrt (Fintype.card (Equiv.Perm (Fin N))))⁻¹).differentiableAt

/-- The actual symmetric multiplier obeys the sharp RMS gradient bound
at every configuration, including configurations where it vanishes. -/
theorem symmetricMultiplier_derivative_sq_le (η : A → E → ℝ)
    (hd : ∀ a, Differentiable ℝ (η a)) (hpos : ∀ a x, 0 ≤ η a x)
    (α : Fin N → A) (X V : Fin N → E) :
    fderiv ℝ (symmetricMultiplier η α) X V ^ 2 ≤
      (∑ π : Equiv.Perm (Fin N),
        fderiv ℝ (fun Y : Fin N → E => tensorMultiplier η α (Y ∘ π)) X V ^ 2) /
        Fintype.card (Equiv.Perm (Fin N)) := by
  have h : fderiv ℝ (symmetricMultiplier η α) X =
      (Real.sqrt (Fintype.card (Equiv.Perm (Fin N))))⁻¹ •
        rmsDerivative (fun (π : Equiv.Perm (Fin N)) Y => tensorMultiplier η α (Y ∘ π)) X := by
    change fderiv ℝ (fun Y => rms (fun π : Equiv.Perm (Fin N) =>
      tensorMultiplier η α (Y ∘ π)) / Real.sqrt (Fintype.card (Equiv.Perm (Fin N)))) X = _
    simpa only [div_eq_mul_inv, mul_comm] using
      ((rms_hasFDerivAt _ (permutedTensor_differentiable η hd α)
        (fun π Y => tensorMultiplier_nonneg η hpos α (Y ∘ π)) X).const_mul
          (Real.sqrt (Fintype.card (Equiv.Perm (Fin N))))⁻¹).fderiv
  rw [h]
  simp only [smul_apply, smul_eq_mul, ← div_eq_inv_mul, div_pow,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ Fintype.card (Equiv.Perm (Fin N)))]
  exact div_le_div_of_nonneg_right (rms_derivative_sq_le _ X V) (by positivity)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Every active symmetric label supplies an assignment of particles to
its spatial centers. This is the support fact used by the cluster graph. -/
theorem symmetricMultiplier_active_assignment (η : A → E → ℝ)
    (α : Fin N → A) (X : Fin N → E) (hx : symmetricMultiplier η α X ≠ 0) :
    ∃ π : Equiv.Perm (Fin N), ∀ i, η (α i) (X (π i)) ≠ 0 := by
  have hn : ¬∀ π : Equiv.Perm (Fin N), tensorMultiplier η α (X ∘ π) = 0 := by
    intro h
    apply hx
    rw [symmetricMultiplier, (rms_eq_zero_iff _).mpr h, zero_div]
  push Not at hn
  obtain ⟨π, hπ⟩ := hn
  exact ⟨π, fun i => (prod_ne_zero_iff.mp hπ) i (mem_univ i)⟩

omit [NormedSpace ℝ E] in
theorem symmetricMultiplier_spatial_support (η : A → E → ℝ)
    (c : A → E) (r : ℝ)
    (hsupp : ∀ a x, η a x ≠ 0 → dist x (c a) < r)
    (α : Fin N → A) (X : Fin N → E) (hx : symmetricMultiplier η α X ≠ 0) :
    ∃ π : Equiv.Perm (Fin N), ∀ i, dist (X (π i)) (c (α i)) < r := by
  obtain ⟨π, hπ⟩ := symmetricMultiplier_active_assignment η α X hx
  exact ⟨π, fun i => hsupp (α i) (X (π i)) (hπ i)⟩

/-- Both square normalization and the differentiated cancellation are now
theorems for the constructed symmetric spatial multipliers. -/
theorem symmetricMultiplier_connection (η : A → E → ℝ)
    (hloc : LocallyFinite (fun a => Function.support (η a)))
    (hd : ∀ a, Differentiable ℝ (η a)) (hpos : ∀ a x, 0 ≤ η a x)
    (hpart : ∀ x, HasSum (fun a => η a x ^ 2) 1)
    (X V : Fin N → E) :
    HasSum (fun α : Fin N → A => symmetricMultiplier η α X *
      fderiv ℝ (symmetricMultiplier η α) X V) 0 :=
  square_partition_connection _ (symmetricMultiplier_locallyFinite η hloc)
    (symmetricMultiplier_differentiable η hd hpos)
    (symmetricMultiplier_hasSum_sq η hloc hpart) X V

end GptLean.ElectronicLocalization
