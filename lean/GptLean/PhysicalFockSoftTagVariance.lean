import GptLean.PhysicalFockSoftTagField

/-!
The soft field on superpositions of soft tags.

A tag family is a family of soft modes `f_j` that are orthonormal and whose
truncated frequency matrix is diagonal, as for modes with disjoint supports.
Write `T_j` for the tag of `f_j` and let `q_j` be radiation-graph vectors with
hard inclusions. For `Q = ∑ⱼ T_j q_j`:

* tags of hard vectors are orthonormal, `⟪∑ⱼ T_j u_j, ∑ⱼ T_j v_j⟫ = ∑ⱼ ⟪u_j, v_j⟫`;
* a hard kernel `h` commutes with the tags, `A_h Q = ∑ⱼ T_j A_h q_j`;
* for a soft kernel `s`, `‖A_s Q‖² ≤ 3 ‖s‖² ∑ⱼ ‖q_j‖²` (`many-electron-soft-tag-variance`),
  and `A_s Q` is orthogonal to every superposition of tags of hard vectors;
* `‖dΓ(ω)^{1/2} Q‖² ≤ ∑ⱼ (κ ‖q_j‖² + ‖dΓ(ω)^{1/2} q_j‖²)`.

The soft bound uses the canonical commutation relation
`‖a†(s) Q‖² = ‖a(s) Q‖² + ‖s‖² ‖Q‖²`, the orthogonality of the hard vector
`a(s) Q = ∑ⱼ ⟪s, f_j⟫ q_j` to `a†(s) Q`, and Bessel's inequality
`∑ⱼ |⟪s, f_j⟫|² ≤ ‖s‖²`.
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

/-- Inner product of two sums whose cross terms vanish. -/
theorem inner_sum_of_cross (s : Finset ι) (X Y : ι → E)
    (h : ∀ j ∈ s, ∀ l ∈ s, j ≠ l → ⟪X j, Y l⟫_ℂ = 0) :
    ⟪∑ j ∈ s, X j, ∑ l ∈ s, Y l⟫_ℂ = ∑ j ∈ s, ⟪X j, Y j⟫_ℂ := by
  rw [sum_inner]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [inner_sum]
  exact Finset.sum_eq_single j (fun l hl hlj => h j hj l hl (Ne.symm hlj))
    (fun hj' => absurd hj hj')

theorem re_inner_self (x : E) : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := by
  simpa using inner_self_eq_norm_sq (𝕜 := ℂ) x

/-- Pythagoras for orthogonal vectors. -/
theorem norm_sq_add_of_inner_zero (x y : E) (h : ⟪x, y⟫_ℂ = 0) :
    ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  rw [norm_add_sq (𝕜 := ℂ), h, map_zero, mul_zero, add_zero]

/-- Triangle and Cauchy--Schwarz inequalities for a finite combination. -/
theorem norm_sq_sum_smul_le (s : Finset ι) (a : ι → ℂ) (X : ι → E) :
    ‖∑ j ∈ s, a j • X j‖ ^ 2 ≤ (∑ j ∈ s, ‖a j‖ ^ 2) * ∑ j ∈ s, ‖X j‖ ^ 2 := by
  have h1 : ‖∑ j ∈ s, a j • X j‖ ≤ ∑ j ∈ s, ‖a j‖ * ‖X j‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (norm_smul (a j) (X j)).le)
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq s (fun j => ‖a j‖) (fun j => ‖X j‖))

private theorem three_bound (a b : ℝ) (h : a ≤ b) : a + (a + b) ≤ 3 * b := by linarith

end Algebra

variable (κ : ℝ) (C : CanonicalSectorCCR photonMeasure) (BF : StandardSymmetricFockExponential)

/-- Tag modes indexed by an arbitrary type: unit soft modes, mutually
orthogonal, with diagonal truncated frequency matrix. -/
structure TagFamily {ι : Type*} (f : ι → Lp ℂ 2 photonMeasure) : Prop where
  soft : ∀ j, f j ∈ softOnePhoton κ
  unit : ∀ j, ‖f j‖ = 1
  orthogonal : ∀ j l, j ≠ l → ⟪f j, f l⟫_ℂ = 0
  weighted : ∀ r : ℕ, ∀ j l, j ≠ l →
    ⟪f j, oneMultiplier (r : ℝ) (Nat.cast_nonneg r) (f l)⟫_ℂ = 0

variable {κ} {ι : Type*} {f : ι → Lp ℂ 2 photonMeasure}

theorem TagFamily.modes (hF : TagFamily κ f) (s : Finset ι) : TagModes κ s f where
  soft := hF.soft
  unit j _ := hF.unit j
  orthogonal j _ l _ := hF.orthogonal j l
  weighted r j _ l _ := hF.weighted r j l

theorem TagFamily.orthonormal (hF : TagFamily κ f) : Orthonormal ℂ f := by
  refine ⟨hF.unit, ?_⟩
  intro j l h
  exact hF.orthogonal j l h

theorem TagFamily.inner_self (hF : TagFamily κ f) (j : ι) : ⟪f j, f j⟫_ℂ = 1 := by
  rw [inner_self_eq_norm_sq_to_K, hF.unit j]
  simp

section Superposition

variable (hF : TagFamily κ f) (hκ : 0 ≤ κ) (s : Finset ι)

/-- **Tags of hard vectors are orthonormal.** -/
theorem tag_sum_inner (u v : ι → PhotonFock)
    (hu : ∀ j, u j ∈ generatedFockSubspace (hardOnePhoton κ))
    (hv : ∀ j, v j ∈ generatedFockSubspace (hardOnePhoton κ)) :
    ⟪∑ j ∈ s, tagOp κ C BF (hF.soft j) (u j), ∑ j ∈ s, tagOp κ C BF (hF.soft j) (v j)⟫_ℂ =
      ∑ j ∈ s, ⟪u j, v j⟫_ℂ := by
  refine (inner_sum_of_cross s _ _ fun j _ l _ hjl => ?_).trans
    (Finset.sum_congr rfl fun j _ => ?_)
  · exact (tagOp_inner κ C BF (hF.soft j) (hF.soft l) (u j) (v l) (hu j) (hv l)).trans
      ((congrArg (· * ⟪u j, v l⟫_ℂ) (hF.orthogonal j l hjl)).trans (zero_mul _))
  · exact (tagOp_inner κ C BF (hF.soft j) (hF.soft j) (u j) (v j) (hu j) (hv j)).trans
      ((congrArg (· * ⟪u j, v j⟫_ℂ) (hF.inner_self j)).trans (one_mul _))

theorem tag_sum_norm_sq (u : ι → PhotonFock)
    (hu : ∀ j, u j ∈ generatedFockSubspace (hardOnePhoton κ)) :
    ‖∑ j ∈ s, tagOp κ C BF (hF.soft j) (u j)‖ ^ 2 = ∑ j ∈ s, ‖u j‖ ^ 2 := by
  have h := congrArg Complex.re (tag_sum_inner C BF hF s u u hu hu)
  rw [re_inner_self, Complex.re_sum] at h
  exact h.trans (Finset.sum_congr rfl fun j _ => re_inner_self (u j))

/-- Tags are orthogonal to hard vectors. -/
theorem tag_sum_inner_hard (u : ι → PhotonFock) (w : PhotonFock)
    (hw : w ∈ generatedFockSubspace (hardOnePhoton κ)) :
    ⟪∑ j ∈ s, tagOp κ C BF (hF.soft j) (u j), w⟫_ℂ = 0 :=
  (sum_inner s _ w).trans (Finset.sum_eq_zero fun j _ =>
    tagOp_inner_hard κ C BF (hF.soft j) (u j) w hw)

theorem tagGraph_sum_inclusion (q : ι → RadiationGraphSpace) :
    radiationGraphInclusion (∑ j ∈ s, tagGraph κ C BF (hF.soft j) (hF.unit j) hκ (q j)) =
      ∑ j ∈ s, tagOp κ C BF (hF.soft j) (radiationGraphInclusion (q j)) :=
  (map_sum radiationGraphInclusion _ s).trans (Finset.sum_congr rfl fun j _ =>
    tagGraph_inclusion κ C BF (hF.soft j) (hF.unit j) hκ (q j))

/-- **A hard field commutes with the tags.** -/
theorem kernelField_tagGraph_sum_hard (k : WeightedPhotonKernel)
    (hk : k.val.1 ∈ hardOnePhoton κ) (q : ι → RadiationGraphSpace)
    (hq : ∀ j, radiationGraphInclusion (q j) ∈ generatedFockSubspace (hardOnePhoton κ)) :
    kernelField C k (∑ j ∈ s, tagGraph κ C BF (hF.soft j) (hF.unit j) hκ (q j)) =
      ∑ j ∈ s, tagOp κ C BF (hF.soft j) (kernelField C k (q j)) :=
  (map_sum (kernelField C k) _ s).trans (Finset.sum_congr rfl fun j _ =>
    kernelField_tagGraph_hard κ C BF (hF.soft j) (hF.unit j) hκ k hk (q j) (hq j))

theorem kernelAnnihilation_tagGraph_sum_soft (k : WeightedPhotonKernel)
    (hk : k.val.1 ∈ softOnePhoton κ) (q : ι → RadiationGraphSpace)
    (hq : ∀ j, radiationGraphInclusion (q j) ∈ generatedFockSubspace (hardOnePhoton κ)) :
    kernelAnnihilation k (∑ j ∈ s, tagGraph κ C BF (hF.soft j) (hF.unit j) hκ (q j)) =
      ∑ j ∈ s, ⟪k.val.1, f j⟫_ℂ • radiationGraphInclusion (q j) :=
  (map_sum (kernelAnnihilation k) _ s).trans (Finset.sum_congr rfl fun j _ =>
    kernelAnnihilation_tagGraph_soft κ C BF (hF.soft j) (hF.unit j) hκ k hk (q j) (hq j))

theorem kernelAnnihilation_tagGraph_sum_mem (k : WeightedPhotonKernel)
    (hk : k.val.1 ∈ softOnePhoton κ) (q : ι → RadiationGraphSpace)
    (hq : ∀ j, radiationGraphInclusion (q j) ∈ generatedFockSubspace (hardOnePhoton κ)) :
    kernelAnnihilation k (∑ j ∈ s, tagGraph κ C BF (hF.soft j) (hF.unit j) hκ (q j)) ∈
      generatedFockSubspace (hardOnePhoton κ) := by
  rw [kernelAnnihilation_tagGraph_sum_soft C BF hF hκ s k hk q hq]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hq j)

theorem kernelAnnihilation_tagGraph_sum_norm_sq_le (k : WeightedPhotonKernel)
    (hk : k.val.1 ∈ softOnePhoton κ) (q : ι → RadiationGraphSpace)
    (hq : ∀ j, radiationGraphInclusion (q j) ∈ generatedFockSubspace (hardOnePhoton κ)) :
    ‖kernelAnnihilation k (∑ j ∈ s, tagGraph κ C BF (hF.soft j) (hF.unit j) hκ (q j))‖ ^ 2 ≤
      ‖k.val.1‖ ^ 2 * ∑ j ∈ s, ‖radiationGraphInclusion (q j)‖ ^ 2 := by
  rw [kernelAnnihilation_tagGraph_sum_soft C BF hF hκ s k hk q hq]
  refine (norm_sq_sum_smul_le s _ _).trans
    (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun j _ => sq_nonneg _))
  have hb := Orthonormal.sum_inner_products_le (𝕜 := ℂ) k.val.1 (s := s) hF.orthonormal
  refine Eq.trans_le (Finset.sum_congr rfl fun j _ => ?_) hb
  rw [norm_inner_symm]

/-- **The soft-field estimate on a tag superposition**,
`‖A_s Q‖² ≤ 3 ‖s‖² ∑ⱼ ‖q_j‖²`. -/
theorem kernelField_tagGraph_sum_soft_norm_sq_le (k : WeightedPhotonKernel)
    (hk : k.val.1 ∈ softOnePhoton κ) (q : ι → RadiationGraphSpace)
    (hq : ∀ j, radiationGraphInclusion (q j) ∈ generatedFockSubspace (hardOnePhoton κ)) :
    ‖kernelField C k (∑ j ∈ s, tagGraph κ C BF (hF.soft j) (hF.unit j) hκ (q j))‖ ^ 2 ≤
      3 * (‖k.val.1‖ ^ 2 * ∑ j ∈ s, ‖radiationGraphInclusion (q j)‖ ^ 2) := by
  set Q := ∑ j ∈ s, tagGraph κ C BF (hF.soft j) (hF.unit j) hκ (q j) with hQdef
  have hA := kernelAnnihilation_tagGraph_sum_norm_sq_le C BF hF hκ s k hk q hq
  have hmem := kernelAnnihilation_tagGraph_sum_mem C BF hF hκ s k hk q hq
  have horth : ⟪kernelAnnihilation k Q, kernelCreation C k Q⟫_ℂ = 0 :=
    kernelCreation_inner_eq_zero_of_orthogonal C (hardOnePhoton κ) k
      (soft_mem_hard_orthogonal κ hk) Q _ hmem
  have hcr : ‖kernelCreation C k Q‖ ^ 2 =
      ‖kernelAnnihilation k Q‖ ^ 2 + ‖k.val.1‖ ^ 2 * ‖radiationGraphInclusion Q‖ ^ 2 :=
    creationRadiation_norm_sq C k.val.1 k.val.2 k.property Q
  have hQ : ‖radiationGraphInclusion Q‖ ^ 2 =
      ∑ j ∈ s, ‖radiationGraphInclusion (q j)‖ ^ 2 :=
    (congrArg (fun x : PhotonFock => ‖x‖ ^ 2) (tagGraph_sum_inclusion C BF hF hκ s q)).trans
      (tag_sum_norm_sq C BF hF s _ hq)
  have hsum : ‖kernelField C k Q‖ ^ 2 =
      ‖kernelAnnihilation k Q‖ ^ 2 + ‖kernelCreation C k Q‖ ^ 2 :=
    norm_sq_add_of_inner_zero (kernelAnnihilation k Q) (kernelCreation C k Q) horth
  rw [hsum, hcr, hQ]
  exact three_bound _ _ hA

/-- **The soft field of a tag superposition is orthogonal to all tags of hard
vectors.** -/
theorem tag_sum_inner_kernelField_soft (k : WeightedPhotonKernel)
    (hk : k.val.1 ∈ softOnePhoton κ) (q : ι → RadiationGraphSpace)
    (hq : ∀ j, radiationGraphInclusion (q j) ∈ generatedFockSubspace (hardOnePhoton κ))
    (w : ι → PhotonFock) (hw : ∀ j, w j ∈ generatedFockSubspace (hardOnePhoton κ)) :
    ⟪∑ j ∈ s, tagOp κ C BF (hF.soft j) (w j),
      kernelField C k (∑ j ∈ s, tagGraph κ C BF (hF.soft j) (hF.unit j) hκ (q j))⟫_ℂ = 0 := by
  set Q := ∑ j ∈ s, tagGraph κ C BF (hF.soft j) (hF.unit j) hκ (q j) with hQdef
  have hmem := kernelAnnihilation_tagGraph_sum_mem C BF hF hκ s k hk q hq
  have hincl : ∀ j, ⟪w j, radiationGraphInclusion Q⟫_ℂ = 0 := fun j => by
    rw [← inner_conj_symm, tagGraph_sum_inclusion C BF hF hκ s q,
      tag_sum_inner_hard C BF hF s _ (w j) (hw j), map_zero]
  have h1 : ⟪∑ j ∈ s, tagOp κ C BF (hF.soft j) (w j), kernelAnnihilation k Q⟫_ℂ = 0 :=
    tag_sum_inner_hard C BF hF s w _ hmem
  have h2 : ⟪∑ j ∈ s, tagOp κ C BF (hF.soft j) (w j), kernelCreation C k Q⟫_ℂ = 0 :=
    (sum_inner s _ _).trans (Finset.sum_eq_zero fun j _ =>
      (tagOp_inner_creation_soft κ C BF (hF.soft j) k hk (w j) (hw j) Q).trans
        ((congrArg (fun z => (starRingEnd ℂ) ⟪k.val.1, f j⟫_ℂ * z) (hincl j)).trans
          (mul_zero _)))
  change ⟪∑ j ∈ s, tagOp κ C BF (hF.soft j) (w j),
    kernelAnnihilation k Q + kernelCreation C k Q⟫_ℂ = 0
  rw [inner_add_right, h1, h2, add_zero]

/-- **Radiation of a tag superposition on the graph.** -/
theorem tagGraph_sum_derivative_norm_sq_le (q : ι → RadiationGraphSpace)
    (hq : ∀ j, radiationGraphInclusion (q j) ∈ generatedFockSubspace (hardOnePhoton κ)) :
    ‖radiationGraphDerivative (∑ j ∈ s, tagGraph κ C BF (hF.soft j) (hF.unit j) hκ (q j))‖ ^ 2 ≤
      ∑ j ∈ s, (κ * ‖radiationGraphInclusion (q j)‖ ^ 2 +
        ‖radiationGraphDerivative (q j)‖ ^ 2) := by
  have h := radiationForm_tag_sum_le κ C BF s (fun _ => (1 : ℂ)) f (hF.modes s)
    (fun j => radiationGraphInclusion (q j)) hq hκ
  have hl : ENNReal.ofReal (‖radiationGraphDerivative
      (∑ j ∈ s, tagGraph κ C BF (hF.soft j) (hF.unit j) hκ (q j))‖ ^ 2) =
      radiationForm (∑ j ∈ s, (1 : ℂ) • tagOp κ C BF (hF.soft j) (radiationGraphInclusion (q j))) :=
    (radiationGraph_energy _).symm.trans (congrArg radiationForm
      ((tagGraph_sum_inclusion C BF hF hκ s q).trans
        (Finset.sum_congr rfl fun j _ => (one_smul ℂ _).symm)))
  have hr : (∑ j ∈ s, ENNReal.ofReal (‖(1 : ℂ)‖ ^ 2) *
      (ENNReal.ofReal κ * ENNReal.ofReal (‖radiationGraphInclusion (q j)‖ ^ 2) +
        radiationForm (radiationGraphInclusion (q j)))) =
      ENNReal.ofReal (∑ j ∈ s, (κ * ‖radiationGraphInclusion (q j)‖ ^ 2 +
        ‖radiationGraphDerivative (q j)‖ ^ 2)) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [norm_one, one_pow, ENNReal.ofReal_one, one_mul, radiationGraph_energy,
      ← ENNReal.ofReal_mul hκ, ← ENNReal.ofReal_add (by positivity) (sq_nonneg _)]
  exact (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun j _ => by positivity)).mp
    (hl.trans_le (h.trans_eq hr))

end Superposition

end GptLean.PhysicalFock.SoftTag
