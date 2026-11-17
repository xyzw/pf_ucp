import GptLean.PhysicalFockSoftTag
import GptLean.PhysicalFockRadiationField

/-!
Superpositions of soft tags on the actual photon Fock space.

For `κ ≥ 0` let `P` be the projection onto hard-supported Fock vectors. For a
soft mode `f`, `T_f = a†(f) P` is a bounded operator on the whole Fock space,
equal to the tag on hard vectors. Let `f_j` be soft modes that are
orthonormal and whose truncated frequency matrix is diagonal, as for modes
with disjoint supports. Then, for hard vectors `u_j`,

* `‖∑ⱼ cⱼ T_{f_j} uⱼ‖² = ∑ⱼ |cⱼ|² ‖uⱼ‖²`;
* the radiation energy obeys
  `rad(∑ⱼ cⱼ T_{f_j} uⱼ) ≤ ∑ⱼ |cⱼ|² (κ ‖uⱼ‖² + rad(uⱼ))`.

`T_f` maps the radiation graph to itself (`tagGraph`), so tags of vectors in
the radiation domain remain there.
-/

noncomputable section

namespace GptLean.PhysicalFock.SoftTag

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 800000

section Algebra

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*}

/-- Inner products of two superpositions with a diagonal cross matrix. -/
theorem inner_sum_diagonal (s : Finset ι) (c : ι → ℂ) (X Y : ι → E)
    (h : ∀ j ∈ s, ∀ l ∈ s, j ≠ l → ⟪X j, Y l⟫_ℂ = 0) :
    ⟪∑ j ∈ s, c j • X j, ∑ l ∈ s, c l • Y l⟫_ℂ =
      ∑ j ∈ s, ((‖c j‖ ^ 2 : ℝ) : ℂ) * ⟪X j, Y j⟫_ℂ := by
  rw [sum_inner]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [inner_sum, Finset.sum_eq_single j (fun l hl hlj => by
      rw [inner_smul_left, inner_smul_right, h j hj l hl (Ne.symm hlj), mul_zero, mul_zero])
    (fun hj' => absurd hj hj'), inner_smul_left, inner_smul_right, ← mul_assoc,
    Complex.conj_mul', Complex.ofReal_pow]

/-- Pythagoras for an orthogonal superposition. -/
theorem norm_sq_sum_orthogonal (s : Finset ι) (c : ι → ℂ) (X : ι → E)
    (h : ∀ j ∈ s, ∀ l ∈ s, j ≠ l → ⟪X j, X l⟫_ℂ = 0) :
    ‖∑ j ∈ s, c j • X j‖ ^ 2 = ∑ j ∈ s, ‖c j‖ ^ 2 * ‖X j‖ ^ 2 := by
  have hn : ∀ x : E, (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := fun x => by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) x
  have hr : (⟪∑ j ∈ s, c j • X j, ∑ j ∈ s, c j • X j⟫_ℂ).re =
      ∑ j ∈ s, ‖c j‖ ^ 2 * (⟪X j, X j⟫_ℂ).re := by
    rw [inner_sum_diagonal s c X X h, Complex.re_sum]
    exact Finset.sum_congr rfl fun j _ => Complex.re_ofReal_mul _ _
  rw [hn] at hr
  simp only [hn] at hr
  exact hr

end Algebra

variable (κ : ℝ)

section Projection

/-- The projection onto hard-supported Fock vectors. -/
abbrev hardProjection : PhotonFock →L[ℂ] PhotonFock :=
  MomentumSupport.fockProjection photonMeasure (softMomentumSet κ)ᶜ
    (softMomentumSet_measurable κ).compl

theorem hardProjection_hardSupported (u : PhotonFock) : HardSupported κ (hardProjection κ u) := by
  intro n
  filter_upwards [MomentumSupport.fullProjection_ae photonMeasure (softMomentumSet κ)ᶜ
    (softMomentumSet_measurable κ).compl n (u n).val] with k hk hne i
  change (MomentumSupport.fullProjection photonMeasure (softMomentumSet κ)ᶜ
    (softMomentumSet_measurable κ).compl n (u n).val) k ≠ 0 at hne
  rw [hk] at hne
  have hmem : k ∈ MomentumSupport.productRegion n (softMomentumSet κ)ᶜ := by
    by_contra hout
    exact hne (Set.indicator_of_notMem hout _)
  exact not_lt.mp (hmem i)

theorem hardProjection_mem (BF : StandardSymmetricFockExponential) (u : PhotonFock) :
    hardProjection κ u ∈ generatedFockSubspace (hardOnePhoton κ) :=
  mem_generated_of_hardSupported BF κ _ (hardProjection_hardSupported κ u)

theorem hardProjection_fixed (u : PhotonFock) (hu : u ∈ generatedFockSubspace (hardOnePhoton κ)) :
    hardProjection κ u = u :=
  MomentumSupport.fockProjection_fixed photonMeasure (softMomentumSet κ)ᶜ
    (softMomentumSet_measurable κ).compl u
    (MomentumSupport.generated_le_fockSupport photonMeasure (softMomentumSet κ)ᶜ
      (softMomentumSet_measurable κ).compl hu)

theorem hardProjection_coordinate_norm_le (u : PhotonFock) (n : ℕ) :
    ‖hardProjection κ u n‖ ≤ ‖u n‖ :=
  ((MomentumSupport.sectorProjection photonMeasure (softMomentumSet κ)ᶜ
    (softMomentumSet_measurable κ).compl n).le_opNorm _).trans
    (mul_le_of_le_one_left (norm_nonneg _)
      (MomentumSupport.sectorProjection_norm_le photonMeasure _ _ n))

theorem hardProjection_norm_le (u : PhotonFock) : ‖hardProjection κ u‖ ≤ ‖u‖ := by
  have h := hasSum_le (fun n => pow_le_pow_left₀ (norm_nonneg _)
    (hardProjection_coordinate_norm_le κ u n) 2)
    (coordinate_mass_hasSum (Sector photonMeasure) (hardProjection κ u))
    (coordinate_mass_hasSum (Sector photonMeasure) u)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

theorem sectorRadiationForm_hardProjection_le (u : PhotonFock) (n : ℕ) :
    sectorRadiationForm n (hardProjection κ u n) ≤ sectorRadiationForm n (u n) := by
  unfold sectorRadiationForm
  apply lintegral_mono_ae
  filter_upwards [MomentumSupport.fullProjection_ae photonMeasure (softMomentumSet κ)ᶜ
    (softMomentumSet_measurable κ).compl n (u n).val] with k hk
  refine mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) _
  change ‖(MomentumSupport.fullProjection photonMeasure (softMomentumSet κ)ᶜ
    (softMomentumSet_measurable κ).compl n (u n).val) k‖ ^ 2 ≤ ‖(u n).val k‖ ^ 2
  rw [hk]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_indicator_le_norm_self _ _) 2

theorem radiationForm_hardProjection_le (u : PhotonFock) :
    radiationForm (hardProjection κ u) ≤ radiationForm u :=
  ENNReal.tsum_le_tsum fun n => sectorRadiationForm_hardProjection_le κ u n

end Projection

section TagOperator

variable (C : CanonicalSectorCCR photonMeasure) (BF : StandardSymmetricFockExponential)
  {f : Lp ℂ 2 photonMeasure} (hf : f ∈ softOnePhoton κ)

/-- The soft tag `a†(f) P` as a bounded operator on the whole Fock space. -/
def tagOp : PhotonFock →L[ℂ] PhotonFock :=
  LinearMap.mkContinuous
    ((tagMap C (hardOnePhoton κ) (soft_mem_hard_orthogonal κ hf)).comp
      (LinearMap.codRestrict (generatedFockSubspace (hardOnePhoton κ))
        (hardProjection κ).toLinearMap (hardProjection_mem κ BF)))
    ‖f‖ (fun u => by
      change ‖tag C (hardOnePhoton κ) (soft_mem_hard_orthogonal κ hf)
        ⟨hardProjection κ u, hardProjection_mem κ BF u⟩‖ ≤ ‖f‖ * ‖u‖
      have h := tag_norm_sq C (hardOnePhoton κ) (soft_mem_hard_orthogonal κ hf)
        ⟨hardProjection κ u, hardProjection_mem κ BF u⟩
      rw [← mul_pow] at h
      rw [(pow_left_inj₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        two_ne_zero).mp h]
      exact mul_le_mul_of_nonneg_left (hardProjection_norm_le κ u) (norm_nonneg _))

theorem tagOp_zero_coord (u : PhotonFock) : tagOp κ C BF hf u 0 = 0 := rfl

theorem tagOp_succ_coord (u : PhotonFock) (n : ℕ) :
    tagOp κ C BF hf u (n + 1) = creationSector photonMeasure n f (hardProjection κ u n) := rfl

theorem tagOp_succ_coord_hard (u : PhotonFock) (hu : u ∈ generatedFockSubspace (hardOnePhoton κ))
    (n : ℕ) : tagOp κ C BF hf u (n + 1) = creationSector photonMeasure n f (u n) := by
  rw [tagOp_succ_coord, hardProjection_fixed κ u hu]

theorem tagOp_eq_tag (u : PhotonFock) (hu : u ∈ generatedFockSubspace (hardOnePhoton κ)) :
    tagOp κ C BF hf u = tag C (hardOnePhoton κ) (soft_mem_hard_orthogonal κ hf) ⟨u, hu⟩ := by
  apply lp.ext
  funext n
  cases n with
  | zero => rfl
  | succ n => exact tagOp_succ_coord_hard κ C BF hf u hu n

/-- Inner products of tags of hard vectors. -/
theorem tagOp_inner {g : Lp ℂ 2 photonMeasure} (hg : g ∈ softOnePhoton κ) (u v : PhotonFock)
    (hu : u ∈ generatedFockSubspace (hardOnePhoton κ))
    (hv : v ∈ generatedFockSubspace (hardOnePhoton κ)) :
    ⟪tagOp κ C BF hf u, tagOp κ C BF hg v⟫_ℂ = ⟪f, g⟫_ℂ * ⟪u, v⟫_ℂ := by
  rw [tagOp_eq_tag κ C BF hf u hu, tagOp_eq_tag κ C BF hg v hv]
  exact tag_inner C (hardOnePhoton κ) _ _ ⟨u, hu⟩ ⟨v, hv⟩

/-- Tags are orthogonal to hard vectors. -/
theorem tagOp_inner_hard (u w : PhotonFock) (hw : w ∈ generatedFockSubspace (hardOnePhoton κ)) :
    ⟪tagOp κ C BF hf u, w⟫_ℂ = 0 :=
  tag_inner_hard C (hardOnePhoton κ) (soft_mem_hard_orthogonal κ hf)
    ⟨hardProjection κ u, hardProjection_mem κ BF u⟩ w hw

end TagOperator

section Radiation

variable (C : CanonicalSectorCCR photonMeasure) (BF : StandardSymmetricFockExponential)

private theorem inner_real_smul_self' (r : ℝ) (z : ℂ) :
    ⟪z, r • z⟫_ℂ = ((r * ‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [RCLike.inner_apply, Complex.real_smul, mul_assoc, Complex.mul_conj', Complex.ofReal_mul,
    Complex.ofReal_pow]

private theorem l2_norm_sq_eq (f : Lp ℂ 2 photonMeasure) :
    ‖f‖ ^ 2 = ∫ p, ‖f p‖ ^ 2 ∂photonMeasure := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) f, L2.inner_def,
    ← integral_re (L2.integrable_inner (𝕜 := ℂ) f f)]
  exact integral_congr_ae (ae_of_all _ fun p => inner_self_eq_norm_sq (𝕜 := ℂ) (f p))

/-- The truncated frequency moment of a soft mode is at most `κ ‖f‖²`. -/
theorem oneMultiplier_inner_re_le (R : ℝ) (hR : 0 ≤ R) {f : Lp ℂ 2 photonMeasure}
    (hf : f ∈ softOnePhoton κ) :
    (⟪f, oneMultiplier R hR f⟫_ℂ).re ≤ κ * ‖f‖ ^ 2 := by
  have hf' := (MomentumSplit.mem_supported_iff photonMeasure (softMomentumSet κ)
    (softMomentumSet_measurable κ) f).mp hf
  have hsq : Integrable (fun p => ‖f p‖ ^ 2) photonMeasure :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hint : Integrable (fun p => truncatedFrequency R p * ‖f p‖ ^ 2) photonMeasure :=
    hsq.bdd_mul (truncatedFrequency_measurable R).aestronglyMeasurable
      (ae_of_all _ fun p => (Real.norm_eq_abs _).trans_le (truncatedFrequency_abs_le R hR p))
  have hi : ⟪f, oneMultiplier R hR f⟫_ℂ =
      ((∫ p, truncatedFrequency R p * ‖f p‖ ^ 2 ∂photonMeasure : ℝ) : ℂ) := by
    rw [L2.inner_def, ← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [oneMultiplier_ae R hR f] with p hp
    rw [hp]
    exact inner_real_smul_self' _ _
  rw [hi, Complex.ofReal_re, l2_norm_sq_eq f, ← integral_const_mul]
  apply integral_mono_ae hint (hsq.const_mul κ)
  filter_upwards [hf'] with p hp
  by_cases hs : p ∈ softMomentumSet κ
  · exact mul_le_mul_of_nonneg_right ((min_le_left _ _).trans (le_of_lt hs)) (sq_nonneg _)
  · rw [hp hs, norm_zero, zero_pow two_ne_zero, mul_zero, mul_zero]

/-- Admissible tag modes: unit, orthogonal, with diagonal truncated frequency
matrix. -/
structure TagModes {ι : Type*} (s : Finset ι) (f : ι → Lp ℂ 2 photonMeasure) : Prop where
  soft : ∀ j, f j ∈ softOnePhoton κ
  unit : ∀ j ∈ s, ‖f j‖ = 1
  orthogonal : ∀ j ∈ s, ∀ l ∈ s, j ≠ l → ⟪f j, f l⟫_ℂ = 0
  weighted : ∀ r : ℕ, ∀ j ∈ s, ∀ l ∈ s, j ≠ l →
    ⟪f j, oneMultiplier (r : ℝ) (Nat.cast_nonneg r) (f l)⟫_ℂ = 0

private theorem ofReal_sum_le {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    ENNReal.ofReal (∑ j ∈ s, a j) ≤ ∑ j ∈ s, ENNReal.ofReal (a j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact (ENNReal.ofReal_add_le).trans (add_le_add le_rfl ih)

variable {ι : Type*} (s : Finset ι) (c : ι → ℂ) (f : ι → Lp ℂ 2 photonMeasure)
  (hm : TagModes κ s f) (u : ι → PhotonFock)
  (hu : ∀ j, u j ∈ generatedFockSubspace (hardOnePhoton κ))

include C hm hu in
/-- **Radiation of a tag superposition in one sector.** -/
theorem sectorRadiation_tag_sum_le (hκ : 0 ≤ κ) (m : ℕ) :
    sectorRadiationForm (m + 1)
        (∑ j ∈ s, c j • creationSector photonMeasure m (f j) (u j m)) ≤
      ∑ j ∈ s, ENNReal.ofReal (‖c j‖ ^ 2) *
        (ENNReal.ofReal κ * ENNReal.ofReal (‖u j m‖ ^ 2) + sectorRadiationForm m (u j m)) := by
  rw [sectorRadiationForm_eq_iSup]
  refine iSup_le fun r => ?_
  set M := sectorMultiplier (r : ℝ) (Nat.cast_nonneg r) (m + 1)
  set X : ι → FullSector photonMeasure (m + 1) := fun j =>
    (creationSector photonMeasure m (f j) (u j m)).val
  have hval : (∑ j ∈ s, c j • creationSector photonMeasure m (f j) (u j m)).val =
      ∑ j ∈ s, c j • X j := by
    simp only [X, Submodule.coe_sum, Submodule.coe_smul]
  have hMX : M (∑ j ∈ s, c j • X j) = ∑ j ∈ s, c j • M (X j) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => map_smul M (c j) (X j)
  have hcross : ∀ j ∈ s, ∀ l ∈ s, j ≠ l → ⟪X j, M (X l)⟫_ℂ = 0 := by
    intro j hj l hl hjl
    rw [inner_multiplier_creation C κ (r : ℝ) (Nat.cast_nonneg r) (hm.soft j) m (u j m) (u l m)
      (softFree_of_generated C κ (u l) (hu l) m), hm.weighted r j hj l hl hjl,
      hm.orthogonal j hj l hl hjl, zero_mul, zero_mul, add_zero]
  have hdiag : ∀ j ∈ s, (⟪X j, M (X j)⟫_ℂ).re ≤ κ * ‖u j m‖ ^ 2 +
      (⟪(u j m).val, sectorMultiplier (r : ℝ) (Nat.cast_nonneg r) m (u j m).val⟫_ℂ).re := by
    intro j hj
    have key := inner_multiplier_creation C κ (r : ℝ) (Nat.cast_nonneg r) (g := f j) (hm.soft j) m (u j m)
      (u j m) (softFree_of_generated C κ (u j) (hu j) m)
    have hxx : ⟪u j m, u j m⟫_ℂ = ((‖u j m‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    have hff : ⟪f j, f j⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hm.unit j hj]
      simp
    have hW : ⟪u j m, sectorWeightOp (r : ℝ) (Nat.cast_nonneg r) m (u j m)⟫_ℂ =
        ⟪(u j m).val, sectorMultiplier (r : ℝ) (Nat.cast_nonneg r) m (u j m).val⟫_ℂ := rfl
    have h1 := oneMultiplier_inner_re_le κ (r : ℝ) (Nat.cast_nonneg r) (hm.soft j)
    rw [hm.unit j hj, one_pow, mul_one] at h1
    have hX : (⟪X j, M (X j)⟫_ℂ).re =
        (⟪f j, oneMultiplier (r : ℝ) (Nat.cast_nonneg r) (f j)⟫_ℂ).re * ‖u j m‖ ^ 2 +
          (⟪(u j m).val, sectorMultiplier (r : ℝ) (Nat.cast_nonneg r) m (u j m).val⟫_ℂ).re := by
      change (⟪(creationSector photonMeasure m (f j) (u j m)).val,
        sectorMultiplier (r : ℝ) (Nat.cast_nonneg r) (m + 1)
          (creationSector photonMeasure m (f j) (u j m)).val⟫_ℂ).re = _
      rw [key, hxx, hff, hW, one_mul, Complex.add_re, Complex.re_mul_ofReal]
    rw [hX]
    nlinarith [sq_nonneg ‖u j m‖]
  have hsum : (⟪∑ j ∈ s, c j • X j, M (∑ j ∈ s, c j • X j)⟫_ℂ).re =
      ∑ j ∈ s, ‖c j‖ ^ 2 * (⟪X j, M (X j)⟫_ℂ).re := by
    rw [hMX, inner_sum_diagonal s c X (fun j => M (X j)) hcross, Complex.re_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hval, hsum]
  refine (ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun j hj =>
    mul_le_mul_of_nonneg_left (hdiag j hj) (sq_nonneg ‖c j‖))).trans ?_
  refine (ofReal_sum_le s _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [ENNReal.ofReal_mul (sq_nonneg _)]
  refine mul_le_mul_right ?_ _
  refine ENNReal.ofReal_add_le.trans (add_le_add ?_ ?_)
  · rw [ENNReal.ofReal_mul hκ]
  · rw [sectorRadiationForm_eq_iSup]
    exact le_iSup (fun r : ℕ => ENNReal.ofReal
      (⟪(u j m).val, sectorMultiplier (r : ℝ) (Nat.cast_nonneg r) m (u j m).val⟫_ℂ).re) r

theorem sectorRadiationForm_zero (n : ℕ) : sectorRadiationForm n 0 = 0 := by
  unfold sectorRadiationForm
  have h : (fun k => ENNReal.ofReal (sectorDispersion n k) *
      ENNReal.ofReal (‖(0 : Sector photonMeasure n).val k‖ ^ 2)) =ᵐ[SectorMeasure photonMeasure n]
      fun _ => 0 := by
    filter_upwards [Lp.coeFn_zero ℂ 2 (SectorMeasure photonMeasure n)] with k hk
    change ENNReal.ofReal (sectorDispersion n k) *
      ENNReal.ofReal (‖(0 : FullSector photonMeasure n) k‖ ^ 2) = 0
    rw [hk]
    simp
  rw [lintegral_congr_ae h, lintegral_zero]

theorem sum_smul_coord (g : ι → PhotonFock) (n : ℕ) :
    (∑ j ∈ s, c j • g j) n = ∑ j ∈ s, c j • g j n := by
  rw [lp.coeFn_sum, Finset.sum_apply]
  rfl

include C hm hu in
/-- **Radiation of a tag superposition**,
`rad(∑ⱼ cⱼ a†(fⱼ) uⱼ) ≤ ∑ⱼ |cⱼ|² (κ ‖uⱼ‖² + rad(uⱼ))`. -/
theorem radiationForm_tag_sum_le (hκ : 0 ≤ κ) :
    radiationForm (∑ j ∈ s, c j • tagOp κ C BF (hm.soft j) (u j)) ≤
      ∑ j ∈ s, ENNReal.ofReal (‖c j‖ ^ 2) *
        (ENNReal.ofReal κ * ENNReal.ofReal (‖u j‖ ^ 2) + radiationForm (u j)) := by
  have hcoord : ∀ m, (∑ j ∈ s, c j • tagOp κ C BF (hm.soft j) (u j)) (m + 1) =
      ∑ j ∈ s, c j • creationSector photonMeasure m (f j) (u j m) := fun m => by
    rw [sum_smul_coord]
    exact Finset.sum_congr rfl fun j _ => by rw [tagOp_succ_coord_hard κ C BF (hm.soft j) (u j) (hu j)]
  have hzero : (∑ j ∈ s, c j • tagOp κ C BF (hm.soft j) (u j)) 0 = 0 := by
    rw [sum_smul_coord]
    exact Finset.sum_eq_zero fun j _ => by rw [tagOp_zero_coord, smul_zero]
  have hmass : ∀ j, (∑' m, ENNReal.ofReal (‖u j m‖ ^ 2)) = ENNReal.ofReal (‖u j‖ ^ 2) := fun j => by
    have h := massForm_eq (Sector photonMeasure) (u j)
    simp only [weightedForm, one_mul] at h
    exact h
  unfold radiationForm
  rw [tsum_eq_zero_add' ENNReal.summable, hzero, sectorRadiationForm_zero, zero_add]
  simp_rw [hcoord]
  refine (ENNReal.tsum_le_tsum fun m => sectorRadiation_tag_sum_le κ C s c f hm u hu hκ m).trans ?_
  rw [Summable.tsum_finsetSum (fun j _ => ENNReal.summable)]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, ENNReal.tsum_mul_left, hmass j]

end Radiation

section Graph

variable (C : CanonicalSectorCCR photonMeasure) (BF : StandardSymmetricFockExponential)
  {f : Lp ℂ 2 photonMeasure} (hf : f ∈ softOnePhoton κ) (hf1 : ‖f‖ = 1) (hκ : 0 ≤ κ)

include hf hf1 in
private theorem single_modes : TagModes κ ({()} : Finset Unit) (fun _ => f) where
  soft _ := hf
  unit _ _ := hf1
  orthogonal j _ l _ hjl := absurd (Subsingleton.elim j l) hjl
  weighted _ j _ l _ hjl := absurd (Subsingleton.elim j l) hjl

include hf1 hκ in
/-- The radiation of one tag. -/
theorem radiationForm_tagOp_le (x : PhotonFock) :
    radiationForm (tagOp κ C BF hf x) ≤
      ENNReal.ofReal κ * ENNReal.ofReal (‖x‖ ^ 2) + radiationForm x := by
  have hP := hardProjection_mem κ BF x
  have hfix : tagOp κ C BF hf x = tagOp κ C BF hf (hardProjection κ x) := by
    apply lp.ext
    funext n
    cases n with
    | zero => rfl
    | succ n => rw [tagOp_succ_coord, tagOp_succ_coord, hardProjection_fixed κ _ hP]
  have h := radiationForm_tag_sum_le κ C BF ({()} : Finset Unit) (fun _ => 1) (fun _ => f)
    (single_modes κ hf hf1) (fun _ => hardProjection κ x) (fun _ => hP) hκ
  simp only [Finset.sum_singleton, one_smul, norm_one, one_pow, ENNReal.ofReal_one, one_mul] at h
  rw [hfix]
  refine h.trans (add_le_add (mul_le_mul_right (ENNReal.ofReal_le_ofReal
    (pow_le_pow_left₀ (norm_nonneg _) (hardProjection_norm_le κ x) 2)) _)
    (radiationForm_hardProjection_le κ x))

include hf1 hκ in
theorem tagOp_mem_domain (q : RadiationGraphSpace) :
    tagOp κ C BF hf (radiationGraphInclusion q) ∈ radiationRoot.domain :=
  (radiationRoot_domain_iff_finite _).mpr ((radiationForm_tagOp_le κ C BF hf hf1 hκ _).trans_lt
    (ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top,
      radiationGraph_finite q⟩))

/-- The graph element of a tag. -/
def tagGraphFun (q : RadiationGraphSpace) : RadiationGraphSpace :=
  ⟨(tagOp κ C BF hf (radiationGraphInclusion q),
      radiationRoot ⟨_, tagOp_mem_domain κ C BF hf hf1 hκ q⟩),
    radiationRoot.mem_graph ⟨_, tagOp_mem_domain κ C BF hf hf1 hκ q⟩⟩

theorem tagGraphFun_inclusion (q : RadiationGraphSpace) :
    radiationGraphInclusion (tagGraphFun κ C BF hf hf1 hκ q) =
      tagOp κ C BF hf (radiationGraphInclusion q) := rfl

theorem tagGraphFun_derivative (q : RadiationGraphSpace) :
    radiationGraphDerivative (tagGraphFun κ C BF hf hf1 hκ q) =
      radiationRoot ⟨_, tagOp_mem_domain κ C BF hf hf1 hκ q⟩ := rfl

theorem tagGraphFun_derivative_norm_sq (q : RadiationGraphSpace) :
    ‖radiationGraphDerivative (tagGraphFun κ C BF hf hf1 hκ q)‖ ^ 2 ≤
      κ * ‖radiationGraphInclusion q‖ ^ 2 + ‖radiationGraphDerivative q‖ ^ 2 := by
  have h := (radiationRoot_energy ⟨_, tagOp_mem_domain κ C BF hf hf1 hκ q⟩).symm.trans_le
    (radiationForm_tagOp_le κ C BF hf hf1 hκ (radiationGraphInclusion q))
  rw [radiationGraph_energy, ← ENNReal.ofReal_mul hκ, ← ENNReal.ofReal_add
    (mul_nonneg hκ (sq_nonneg _)) (sq_nonneg _)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg (mul_nonneg hκ (sq_nonneg _)) (sq_nonneg _))).mp h

end Graph

end GptLean.PhysicalFock.SoftTag
