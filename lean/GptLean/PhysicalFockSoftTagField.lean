import GptLean.PhysicalFockSoftTagSum

/-!
The field on soft tags.

Let `T_f` be the soft tag of `PhysicalFockSoftTagSum` and `q` a radiation-graph
vector with hard inclusion. Then, with `tagGraph f q` the graph vector of
`T_f q`,

* a hard kernel `h` commutes with the tag: `A_h (T_f q) = T_f (A_h q)`;
* a soft kernel `s` annihilates the tag: `a(s) (T_f q) = ⟪s, f⟫ q`.

For a superposition `Q = ∑ⱼ cⱼ T_{fⱼ} qⱼ` with orthonormal soft modes, the soft
field splits into `a(s) Q`, which is hard, and `a†(s) Q`. Both are orthogonal
to every tag, and

`‖A_s Q‖² ≤ 3 ‖s‖² ‖Q‖²`,

which is the soft-field estimate `many-electron-soft-tag-variance` of the
article.
-/

noncomputable section

namespace GptLean.PhysicalFock.SoftTag

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 800000

variable (κ : ℝ) (C : CanonicalSectorCCR photonMeasure) (BF : StandardSymmetricFockExponential)

section Norm

variable {f : Lp ℂ 2 photonMeasure} (hf : f ∈ softOnePhoton κ)

theorem tagOp_norm_le (u : PhotonFock) : ‖tagOp κ C BF hf u‖ ≤ ‖f‖ * ‖u‖ := by
  change ‖tag C (hardOnePhoton κ) (soft_mem_hard_orthogonal κ hf)
    ⟨hardProjection κ u, hardProjection_mem κ BF u⟩‖ ≤ ‖f‖ * ‖u‖
  have h := tag_norm_sq C (hardOnePhoton κ) (soft_mem_hard_orthogonal κ hf)
    ⟨hardProjection κ u, hardProjection_mem κ BF u⟩
  rw [← mul_pow] at h
  rw [(pow_left_inj₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    two_ne_zero).mp h]
  exact mul_le_mul_of_nonneg_left (hardProjection_norm_le κ u) (norm_nonneg _)

theorem tagOp_norm_hard (hf1 : ‖f‖ = 1) (u : PhotonFock)
    (hu : u ∈ generatedFockSubspace (hardOnePhoton κ)) : ‖tagOp κ C BF hf u‖ = ‖u‖ := by
  have h := tagOp_inner κ C BF hf hf u u hu hu
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
    hf1] at h
  simp only [RCLike.ofReal_one, one_pow, one_mul] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp (by exact_mod_cast h)

end Norm

section Graph

variable {f : Lp ℂ 2 photonMeasure} (hf : f ∈ softOnePhoton κ) (hf1 : ‖f‖ = 1) (hκ : 0 ≤ κ)

theorem tagGraphFun_add (q r : RadiationGraphSpace) :
    tagGraphFun κ C BF hf hf1 hκ (q + r) =
      tagGraphFun κ C BF hf hf1 hκ q + tagGraphFun κ C BF hf hf1 hκ r := by
  have hx : tagOp κ C BF hf (radiationGraphInclusion (q + r)) =
      tagOp κ C BF hf (radiationGraphInclusion q) + tagOp κ C BF hf (radiationGraphInclusion r) :=
    (congrArg (tagOp κ C BF hf) (map_add radiationGraphInclusion q r)).trans (map_add _ _ _)
  apply Subtype.ext
  apply Prod.ext
  · exact hx
  · change radiationRoot ⟨_, tagOp_mem_domain κ C BF hf hf1 hκ (q + r)⟩ =
      radiationRoot ⟨_, tagOp_mem_domain κ C BF hf hf1 hκ q⟩ +
        radiationRoot ⟨_, tagOp_mem_domain κ C BF hf hf1 hκ r⟩
    rw [← LinearPMap.map_add]
    exact congrArg radiationRoot (Subtype.ext hx)

theorem tagGraphFun_smul (a : ℂ) (q : RadiationGraphSpace) :
    tagGraphFun κ C BF hf hf1 hκ (a • q) = a • tagGraphFun κ C BF hf hf1 hκ q := by
  have hx : tagOp κ C BF hf (radiationGraphInclusion (a • q)) =
      a • tagOp κ C BF hf (radiationGraphInclusion q) :=
    (congrArg (tagOp κ C BF hf) (map_smul radiationGraphInclusion a q)).trans (map_smul _ _ _)
  apply Subtype.ext
  apply Prod.ext
  · exact hx
  · change radiationRoot ⟨_, tagOp_mem_domain κ C BF hf hf1 hκ (a • q)⟩ =
      a • radiationRoot ⟨_, tagOp_mem_domain κ C BF hf hf1 hκ q⟩
    rw [← LinearPMap.map_smul]
    exact congrArg radiationRoot (Subtype.ext hx)

theorem tagGraphFun_norm_le (q : RadiationGraphSpace) :
    ‖tagGraphFun κ C BF hf hf1 hκ q‖ ≤ (κ + 2) * ‖q‖ := by
  have hq1 : ‖radiationGraphInclusion q‖ ≤ ‖q‖ := norm_fst_le q.val
  have hq2 : ‖radiationGraphDerivative q‖ ≤ ‖q‖ := norm_snd_le q.val
  have h1 : ‖radiationGraphInclusion (tagGraphFun κ C BF hf hf1 hκ q)‖ ≤ (κ + 2) * ‖q‖ := by
    refine (tagOp_norm_le κ C BF hf _).trans ?_
    rw [hf1, one_mul]
    nlinarith [norm_nonneg q]
  have h2 : ‖radiationGraphDerivative (tagGraphFun κ C BF hf hf1 hκ q)‖ ≤ (κ + 2) * ‖q‖ := by
    have hs := tagGraphFun_derivative_norm_sq κ C BF hf hf1 hκ q
    have hb : ‖radiationGraphDerivative (tagGraphFun κ C BF hf hf1 hκ q)‖ ^ 2 ≤
        ((κ + 2) * ‖q‖) ^ 2 := by
      have hq1' := pow_le_pow_left₀ (norm_nonneg _) hq1 2
      have hq2' := pow_le_pow_left₀ (norm_nonneg _) hq2 2
      have hk1 : κ * ‖radiationGraphInclusion q‖ ^ 2 ≤ κ * ‖q‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hq1' hκ
      have hk2 : (κ + 1) * ‖q‖ ^ 2 ≤ (κ + 2) ^ 2 * ‖q‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
      calc ‖radiationGraphDerivative (tagGraphFun κ C BF hf hf1 hκ q)‖ ^ 2
          ≤ κ * ‖radiationGraphInclusion q‖ ^ 2 + ‖radiationGraphDerivative q‖ ^ 2 := hs
        _ ≤ (κ + 1) * ‖q‖ ^ 2 := by linarith
        _ ≤ (κ + 2) ^ 2 * ‖q‖ ^ 2 := hk2
        _ = ((κ + 2) * ‖q‖) ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hb
  change max ‖radiationGraphInclusion (tagGraphFun κ C BF hf hf1 hκ q)‖
    ‖radiationGraphDerivative (tagGraphFun κ C BF hf hf1 hκ q)‖ ≤ _
  exact max_le h1 h2

/-- The soft tag as a bounded operator on the radiation graph. -/
def tagGraph : RadiationGraphSpace →L[ℂ] RadiationGraphSpace :=
  LinearMap.mkContinuous
    { toFun := tagGraphFun κ C BF hf hf1 hκ
      map_add' := tagGraphFun_add κ C BF hf hf1 hκ
      map_smul' := tagGraphFun_smul κ C BF hf hf1 hκ }
    (κ + 2) (tagGraphFun_norm_le κ C BF hf hf1 hκ)

theorem tagGraph_inclusion (q : RadiationGraphSpace) :
    radiationGraphInclusion (tagGraph κ C BF hf hf1 hκ q) =
      tagOp κ C BF hf (radiationGraphInclusion q) := rfl

theorem tagGraph_derivative_norm_sq (q : RadiationGraphSpace) :
    ‖radiationGraphDerivative (tagGraph κ C BF hf hf1 hκ q)‖ ^ 2 ≤
      κ * ‖radiationGraphInclusion q‖ ^ 2 + ‖radiationGraphDerivative q‖ ^ 2 :=
  tagGraphFun_derivative_norm_sq κ C BF hf hf1 hκ q

end Graph

section Field

variable {f : Lp ℂ 2 photonMeasure} (hf : f ∈ softOnePhoton κ) (hf1 : ‖f‖ = 1) (hκ : 0 ≤ κ)
  (k : WeightedPhotonKernel)

theorem kernelAnnihilation_coord (q : RadiationGraphSpace) (n : ℕ) :
    kernelAnnihilation k q n =
      annihilationSector photonMeasure n k.val.1 (radiationGraphInclusion q (n + 1)) := rfl

theorem kernelCreation_coord_zero (q : RadiationGraphSpace) : kernelCreation C k q 0 = 0 := rfl

theorem kernelCreation_coord_succ (q : RadiationGraphSpace) (n : ℕ) :
    kernelCreation C k q (n + 1) =
      creationSector photonMeasure n k.val.1 (radiationGraphInclusion q n) := rfl

/-- **Hard annihilation commutes with the tag.** -/
theorem kernelAnnihilation_tagGraph_hard (hk : k.val.1 ∈ hardOnePhoton κ) (q : RadiationGraphSpace)
    (hq : radiationGraphInclusion q ∈ generatedFockSubspace (hardOnePhoton κ)) :
    kernelAnnihilation k (tagGraph κ C BF hf hf1 hκ q) =
      tagOp κ C BF hf (kernelAnnihilation k q) := by
  have hfo := soft_mem_hard_orthogonal κ hf
  have ha := kernelAnnihilation_mem_generated C (hardOnePhoton κ) k q hq
  apply lp.ext
  funext n
  rw [kernelAnnihilation_coord, tagGraph_inclusion, tagOp_succ_coord_hard κ C BF hf _ hq]
  cases n with
  | zero => exact annihilation_creation_hard_zero C (hardOnePhoton κ) hk hfo _
  | succ m =>
    rw [annihilation_creation_hard C (hardOnePhoton κ) hk hfo m,
      tagOp_succ_coord_hard κ C BF hf _ ha m, kernelAnnihilation_coord]

/-- **Hard creation commutes with the tag.** -/
theorem kernelCreation_tagGraph_hard (hk : k.val.1 ∈ hardOnePhoton κ) (q : RadiationGraphSpace)
    (hq : radiationGraphInclusion q ∈ generatedFockSubspace (hardOnePhoton κ)) :
    kernelCreation C k (tagGraph κ C BF hf hf1 hκ q) =
      tagOp κ C BF hf (kernelCreation C k q) := by
  have hc := kernelCreation_mem_generated C (hardOnePhoton κ) k hk q hq
  apply lp.ext
  funext n
  cases n with
  | zero => rfl
  | succ m =>
    rw [kernelCreation_coord_succ, tagGraph_inclusion, tagOp_succ_coord_hard κ C BF hf _ hc m]
    cases m with
    | zero =>
      rw [tagOp_zero_coord, kernelCreation_coord_zero, map_zero, map_zero]
    | succ j =>
      rw [tagOp_succ_coord_hard κ C BF hf _ hq j, kernelCreation_coord_succ,
        creationSector_comm photonMeasure j k.val.1 f]

/-- **The hard field commutes with the tag.** -/
theorem kernelField_tagGraph_hard (hk : k.val.1 ∈ hardOnePhoton κ) (q : RadiationGraphSpace)
    (hq : radiationGraphInclusion q ∈ generatedFockSubspace (hardOnePhoton κ)) :
    kernelField C k (tagGraph κ C BF hf hf1 hκ q) = tagOp κ C BF hf (kernelField C k q) := by
  change kernelAnnihilation k (tagGraph κ C BF hf hf1 hκ q) +
      kernelCreation C k (tagGraph κ C BF hf hf1 hκ q) =
    tagOp κ C BF hf (kernelAnnihilation k q + kernelCreation C k q)
  rw [kernelAnnihilation_tagGraph_hard κ C BF hf hf1 hκ k hk q hq,
    kernelCreation_tagGraph_hard κ C BF hf hf1 hκ k hk q hq, map_add]

/-- **Soft annihilation removes the tag**, `a(s) T_f q = ⟪s, f⟫ q`. -/
theorem kernelAnnihilation_tagGraph_soft (hk : k.val.1 ∈ softOnePhoton κ) (q : RadiationGraphSpace)
    (hq : radiationGraphInclusion q ∈ generatedFockSubspace (hardOnePhoton κ)) :
    kernelAnnihilation k (tagGraph κ C BF hf hf1 hκ q) =
      ⟪k.val.1, f⟫_ℂ • radiationGraphInclusion q := by
  apply lp.ext
  funext n
  rw [kernelAnnihilation_coord, tagGraph_inclusion, tagOp_succ_coord_hard κ C BF hf _ hq,
    annihilation_creation_soft C (hardOnePhoton κ) (soft_mem_hard_orthogonal κ hk) hq n]
  rfl

/-- A tag is orthogonal to the soft creation of any graph vector, up to the
overlap `⟪s, f⟫`. -/
theorem tagOp_inner_creation_soft (hk : k.val.1 ∈ softOnePhoton κ) (w : PhotonFock)
    (hw : w ∈ generatedFockSubspace (hardOnePhoton κ)) (Q : RadiationGraphSpace) :
    ⟪tagOp κ C BF hf w, kernelCreation C k Q⟫_ℂ =
      (starRingEnd ℂ) ⟪k.val.1, f⟫_ℂ * ⟪w, radiationGraphInclusion Q⟫_ℂ := by
  apply shifted_inner w (radiationGraphInclusion Q) (tagOp κ C BF hf w) (kernelCreation C k Q) rfl
  intro n
  rw [tagOp_succ_coord_hard κ C BF hf w hw n, kernelCreation_coord_succ]
  have h := annihilationSector_duality photonMeasure n k.val.1 (radiationGraphInclusion Q n)
    (creationSector photonMeasure n f (w n))
  have h' : ⟪creationSector photonMeasure n k.val.1 (radiationGraphInclusion Q n),
      creationSector photonMeasure n f (w n)⟫_ℂ =
      ⟪k.val.1, f⟫_ℂ * ⟪radiationGraphInclusion Q n, w n⟫_ℂ :=
    h.trans ((congrArg (fun z => ⟪radiationGraphInclusion Q n, z⟫_ℂ)
      (annihilation_creation_soft C (hardOnePhoton κ) (soft_mem_hard_orthogonal κ hk) hw n)).trans
      (inner_smul_right (𝕜 := ℂ) (radiationGraphInclusion Q n) (w n) ⟪k.val.1, f⟫_ℂ))
  calc ⟪creationSector photonMeasure n f (w n),
        creationSector photonMeasure n k.val.1 (radiationGraphInclusion Q n)⟫_ℂ
      = (starRingEnd ℂ) ⟪creationSector photonMeasure n k.val.1 (radiationGraphInclusion Q n),
          creationSector photonMeasure n f (w n)⟫_ℂ := (inner_conj_symm _ _).symm
    _ = (starRingEnd ℂ) (⟪k.val.1, f⟫_ℂ * ⟪radiationGraphInclusion Q n, w n⟫_ℂ) :=
        congrArg _ h'
    _ = (starRingEnd ℂ) ⟪k.val.1, f⟫_ℂ * ⟪w n, radiationGraphInclusion Q n⟫_ℂ :=
        (map_mul _ _ _).trans (congrArg _ (inner_conj_symm _ _))

end Field

end GptLean.PhysicalFock.SoftTag
