import GptLean.PhysicalFockSoftTagVariance
import GptLean.PhysicalPFFiberMap
import GptLean.PhysicalPFVacuumEnergy

/-!
Soft tags on the common Pauli--Fierz reference domain.

Let `f_j` be a tag family below `κ` and `T_j` the soft tag of `f_j`, applied at
every configuration point. Let `u_j` be reference vectors whose photon parts
are hard, `u_j(x) ∈ ℱ(h_κ)` for almost every `x`. Split the field kernel
`k = h + s` into its hard and soft parts, with `∑ᵢ ‖sᵢ(x)‖² ≤ σ`. Then the
superposition `Ψ = ∑ⱼ T_j u_j` lies in the reference domain and

* `‖Ψ‖² = ∑ⱼ ‖u_j‖²`;
* `E(Ψ) ≤ ∑ⱼ E(u_j) + (κ + 3 e² σ / 2) ∑ⱼ ‖u_j‖²`;
* `‖Ψ(x)‖² = ∑ⱼ ‖u_j(x)‖²` and `⟪Ψ(x), (D_k Ψ)(x)⟫ = ∑ⱼ ⟪u_j(x), (D_k u_j)(x)⟫`
  for almost every `x`, so every tested density and current of `Ψ` is the sum
  of those of the `u_j`.

The hard covariant derivative commutes with the tags. The soft field of `Ψ`
is orthogonal to `Ψ` and to the hard covariant derivative of `Ψ`, and its
square is at most `3 ‖s(x)‖² ‖Ψ(x)‖²`. Each tag adds at most `κ ‖u_j‖²` of
radiation energy, and the hard energy of `u_j` is at most its full energy.
-/

noncomputable section

namespace GptLean.PhysicalPFSoftTag

open MeasureTheory Filter PhysicalFock PhysicalFock.SoftTag PhysicalPFReference
  PhysicalPFVacuumEnergy
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

section L2

variable {X H ι : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem norm_sq_eq_integral (F : Lp H 2 μ) : ‖F‖ ^ 2 = ∫ x, ‖F x‖ ^ 2 ∂μ := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) F, L2.inner_def,
    ← integral_re (L2.integrable_inner (𝕜 := ℂ) F F)]
  exact integral_congr_ae (ae_of_all _ fun x => inner_self_eq_norm_sq (𝕜 := ℂ) (F x))

omit [InnerProductSpace ℂ H] in
theorem integrable_norm_sq (F : Lp H 2 μ) : Integrable (fun x => ‖F x‖ ^ 2) μ :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable F)).mp (Lp.memLp F)

theorem inner_eq_zero_of_ae (F G : Lp H 2 μ) (h : ∀ᵐ x ∂μ, ⟪F x, G x⟫_ℂ = 0) :
    ⟪F, G⟫_ℂ = 0 := by
  rw [L2.inner_def]
  exact integral_eq_zero_of_ae h

theorem norm_sq_eq_sum_of_ae (F : Lp H 2 μ) (t : Finset ι) (A : ι → Lp H 2 μ)
    (h : ∀ᵐ x ∂μ, ‖F x‖ ^ 2 = ∑ j ∈ t, ‖A j x‖ ^ 2) :
    ‖F‖ ^ 2 = ∑ j ∈ t, ‖A j‖ ^ 2 := by
  rw [norm_sq_eq_integral, integral_congr_ae h,
    integral_finsetSum _ fun j _ => integrable_norm_sq (A j)]
  exact Finset.sum_congr rfl fun j _ => (norm_sq_eq_integral (A j)).symm

theorem sum_norm_sq_le_of_ae {κ' : Type*} (s : Finset κ') (F : κ' → Lp H 2 μ)
    (t : Finset ι) (a b : ι → ℝ) (A B : ι → Lp H 2 μ)
    (h : ∀ᵐ x ∂μ, ∑ i ∈ s, ‖F i x‖ ^ 2 ≤ ∑ j ∈ t, (a j * ‖A j x‖ ^ 2 + b j * ‖B j x‖ ^ 2)) :
    ∑ i ∈ s, ‖F i‖ ^ 2 ≤ ∑ j ∈ t, (a j * ‖A j‖ ^ 2 + b j * ‖B j‖ ^ 2) := by
  have hA (j : ι) : Integrable (fun x => a j * ‖A j x‖ ^ 2 + b j * ‖B j x‖ ^ 2) μ :=
    ((integrable_norm_sq (A j)).const_mul (a j)).add ((integrable_norm_sq (B j)).const_mul (b j))
  calc ∑ i ∈ s, ‖F i‖ ^ 2 = ∫ x, ∑ i ∈ s, ‖F i x‖ ^ 2 ∂μ := by
        rw [integral_finsetSum _ fun i _ => integrable_norm_sq (F i)]
        exact Finset.sum_congr rfl fun i _ => norm_sq_eq_integral (F i)
    _ ≤ ∫ x, ∑ j ∈ t, (a j * ‖A j x‖ ^ 2 + b j * ‖B j x‖ ^ 2) ∂μ :=
        integral_mono_ae (integrable_finsetSum _ fun i _ => integrable_norm_sq (F i))
          (integrable_finsetSum _ fun j _ => hA j) h
    _ = ∑ j ∈ t, (a j * ‖A j‖ ^ 2 + b j * ‖B j‖ ^ 2) := by
        rw [integral_finsetSum _ fun j _ => hA j]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_add ((integrable_norm_sq (A j)).const_mul (a j))
          ((integrable_norm_sq (B j)).const_mul (b j)), integral_const_mul, integral_const_mul,
          ← norm_sq_eq_integral, ← norm_sq_eq_integral]

/-- Pythagoras with a real coupling constant. -/
theorem norm_sq_sub_of_inner_zero (F G : Lp H 2 μ) (h : ⟪F, G⟫_ℂ = 0) (e : ℝ) :
    ‖F - (e : ℂ) • G‖ ^ 2 = ‖F‖ ^ 2 + e ^ 2 * ‖G‖ ^ 2 := by
  rw [norm_sub_sq (𝕜 := ℂ), inner_smul_right, h, mul_zero, map_zero,
    mul_zero, sub_zero, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

/-- A pointwise identity of inner products gives the identity of every
bounded tested real part. -/
theorem tested_sum_of_ae (w : X → ℝ) (hw : AEStronglyMeasurable w μ) (c : ℝ)
    (hc : ∀ᵐ x ∂μ, |w x| ≤ c) (F G : Lp H 2 μ) (t : Finset ι) (A B : ι → Lp H 2 μ)
    (h : ∀ᵐ x ∂μ, ⟪F x, G x⟫_ℂ = ∑ j ∈ t, ⟪A j x, B j x⟫_ℂ) :
    ∫ x, w x * (⟪F x, G x⟫_ℂ).re ∂μ = ∑ j ∈ t, ∫ x, w x * (⟪A j x, B j x⟫_ℂ).re ∂μ := by
  have hc' : ∀ᵐ x ∂μ, ‖w x‖ ≤ c := by
    filter_upwards [hc] with x hx
    exact (Real.norm_eq_abs _).trans_le hx
  have hi (j : ι) : Integrable (fun x => w x * (⟪A j x, B j x⟫_ℂ).re) μ :=
    (L2.integrable_inner (𝕜 := ℂ) (A j) (B j)).re.bdd_mul hw hc'
  rw [← integral_finsetSum _ fun j _ => hi j]
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [hx, Complex.re_sum, Finset.mul_sum]

theorem coeFn_finset_sum {E : Type*} [NormedAddCommGroup E] (t : Finset ι)
    (F : ι → Lp E 2 μ) : ⇑(∑ j ∈ t, F j) =ᵐ[μ] fun x => ∑ j ∈ t, F j x := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero E 2 μ] with x hx
    rw [Finset.sum_empty, hx, Finset.sum_empty]
    rfl
  | insert j t hj ih =>
    rw [Finset.sum_insert hj]
    filter_upwards [Lp.coeFn_add (F j) (∑ l ∈ t, F l), ih] with x hx hx'
    rw [hx, Pi.add_apply, hx', Finset.sum_insert hj]

theorem sum_compLpL_ae {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (t : Finset ι) (L : ι → E →L[ℂ] F)
    (v : ι → Lp E 2 μ) :
    ⇑(∑ j ∈ t, (L j).compLpL 2 μ (v j)) =ᵐ[μ] fun x => ∑ j ∈ t, L j (v j x) := by
  filter_upwards [coeFn_finset_sum t (fun j => (L j).compLpL 2 μ (v j)),
    (eventually_all_finset t).mpr fun j _ => (L j).coeFn_compLpL (v j)] with x h₁ h₂
  exact h₁.trans (Finset.sum_congr rfl h₂)

theorem affine_ae (A B : Lp H 2 μ) (a b : ℂ) :
    ∀ᵐ x ∂μ, (a • A - b • B) x = a • A x - b • B x := by
  filter_upwards [Lp.coeFn_sub (a • A) (b • B), Lp.coeFn_smul a A, Lp.coeFn_smul b B]
    with x h₁ h₂ h₃
  exact h₁.trans (congrArg₂ (fun y z : H => y - z) h₂ h₃)

theorem sub_smul_ae (A B : Lp H 2 μ) (b : ℂ) :
    ∀ᵐ x ∂μ, (A - b • B) x = A x - b • B x := by
  filter_upwards [Lp.coeFn_sub A (b • B), Lp.coeFn_smul b B] with x h₁ h₂
  exact h₁.trans (congrArg (fun z : H => A x - z) h₂)

theorem inner_sub_smul_of_zero (a c w : H) (d : ℂ) (h : ⟪a, w⟫_ℂ = 0) :
    ⟪a, c - d • w⟫_ℂ = ⟪a, c⟫_ℂ := by
  rw [inner_sub_right, inner_smul_right, h, mul_zero, sub_zero]

end L2

section Algebra

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem sum_map_affine (t : Finset ι) (T : ι → E →L[ℂ] E) (a b : ι → E) (c d : ℂ) :
    c • ∑ j ∈ t, T j (a j) - d • ∑ j ∈ t, T j (b j) = ∑ j ∈ t, T j (c • a j - d • b j) := by
  simp only [map_sub, map_smul, Finset.smul_sum, Finset.sum_sub_distrib]

theorem add_one_mul' (a b : ℝ) : a + b = a + 1 * b := by ring

theorem scalar_soft_bound {I : Type*} [Fintype I] (t : Finset ι) (a : I → ℝ) (m : ι → ℝ)
    (σ : ℝ) (hm : 0 ≤ ∑ j ∈ t, m j) (ha : ∑ i, a i ≤ σ) :
    ∑ i ∈ Finset.univ, 3 * (a i * ∑ j ∈ t, m j) ≤ ∑ j ∈ t, (3 * σ * m j + 0 * m j) := by
  have h1 : ∑ i ∈ Finset.univ, 3 * (a i * ∑ j ∈ t, m j) = 3 * ((∑ i, a i) * ∑ j ∈ t, m j) := by
    rw [← Finset.mul_sum, ← Finset.sum_mul]
  have h2 : ∑ j ∈ t, (3 * σ * m j + 0 * m j) = 3 * (σ * ∑ j ∈ t, m j) := by
    simp only [zero_mul, add_zero]
    rw [← Finset.mul_sum]
    ring
  rw [h1, h2]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ha hm) (by norm_num)

variable {I : Type*} [Fintype I]

/-- The final energy bookkeeping. -/
theorem energy_assemble (t : Finset ι) (ck ch fs : I → ℝ) (chj : I → ι → ℝ)
    (rQ pQ : ℝ) (rj pj mj Ej : ι → ℝ) (e σ κ : ℝ)
    (hcov : ∀ i, ck i = ch i + e ^ 2 * fs i)
    (hch : ∀ i, ch i = ∑ j ∈ t, chj i j)
    (hfs : ∑ i, fs i ≤ ∑ j ∈ t, (3 * σ * mj j + 0 * mj j))
    (hr : rQ ≤ ∑ j ∈ t, (κ * mj j + 1 * rj j))
    (hp : pQ = ∑ j ∈ t, pj j)
    (hE : ∀ j ∈ t, (1 / 2 : ℝ) * ∑ i, chj i j + rj j + pj j ≤ Ej j) :
    (1 / 2 : ℝ) * ∑ i, ck i + rQ + pQ ≤
      ∑ j ∈ t, Ej j + (κ + 3 * e ^ 2 * σ / 2) * ∑ j ∈ t, mj j := by
  have h1 : ∑ i, ck i = ∑ j ∈ t, ∑ i, chj i j + e ^ 2 * ∑ i, fs i := by
    simp_rw [hcov, hch]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
  have h2 := Finset.sum_le_sum hE
  have h4 : ∑ j ∈ t, ((1 / 2 : ℝ) * ∑ i, chj i j + rj j + pj j) =
      (1 / 2 : ℝ) * ∑ j ∈ t, ∑ i, chj i j + ∑ j ∈ t, rj j + ∑ j ∈ t, pj j := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  have h5 : ∑ j ∈ t, (κ * mj j + 1 * rj j) = κ * ∑ j ∈ t, mj j + ∑ j ∈ t, rj j := by
    simp only [one_mul]
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  have h6 : ∑ j ∈ t, (3 * σ * mj j + 0 * mj j) = 3 * σ * ∑ j ∈ t, mj j := by
    simp only [zero_mul, add_zero]
    rw [Finset.mul_sum]
  have h3 : e ^ 2 * ∑ i, fs i ≤ e ^ 2 * (3 * σ * ∑ j ∈ t, mj j) :=
    mul_le_mul_of_nonneg_left (hfs.trans_eq h6) (sq_nonneg e)
  rw [h1, hp]
  rw [h4] at h2
  rw [h5] at hr
  nlinarith [h2, h3, hr]

end Algebra

variable {I : Type} [Fintype I] [DecidableEq I] (V : Position I → ℝ)
  (C : CanonicalSectorCCR photonMeasure) (BF : StandardSymmetricFockExponential)
  {κ : ℝ} {ι : Type*} [Countable ι] {f : ι → Lp ℂ 2 photonMeasure}
  (hF : TagFamily κ f) (hκ : 0 ≤ κ)

/-- The spatial soft tag of mode `f_j`. -/
def tagRef (j : ι) : Reference I V →L[ℂ] Reference I V :=
  PhysicalPFFiberMap.map V (tagOp κ C BF (hF.soft j))
    (tagGraph κ C BF (hF.soft j) (hF.unit j) hκ)
    (tagGraph_inclusion κ C BF (hF.soft j) (hF.unit j) hκ)

/-- The superposition `∑ⱼ T_j u_j`. -/
def tagSum (t : Finset ι) (u : ι → Reference I V) : Reference I V :=
  ∑ j ∈ t, tagRef V C BF hF hκ j (u j)

section Coordinates

variable (t : Finset ι) (u : ι → Reference I V)

omit [Countable ι] in
theorem inclusion_tagSum :
    inclusion I V (tagSum V C BF hF hκ t u) =
      ∑ j ∈ t, (tagOp κ C BF (hF.soft j)).compLpL 2 volume (inclusion I V (u j)) :=
  (map_sum (inclusion I V) _ t).trans (Finset.sum_congr rfl fun j _ =>
    PhysicalPFFiberMap.inclusion_map V _ _ _ (u j))

omit [Countable ι] in
theorem inclusion_tagSum_ae :
    ∀ᵐ x ∂volume, inclusion I V (tagSum V C BF hF hκ t u) x =
      ∑ j ∈ t, tagOp κ C BF (hF.soft j) (inclusion I V (u j) x) := by
  filter_upwards [sum_compLpL_ae t (fun j => tagOp κ C BF (hF.soft j))
    (fun j => inclusion I V (u j))] with x hx
  exact (congrArg (fun v : WaveSpace I => v x) (inclusion_tagSum V C BF hF hκ t u)).trans hx

omit [Countable ι] in
theorem ordinary_tagSum_ae (i : I) :
    ∀ᵐ x ∂volume, ordinary I V i (tagSum V C BF hF hκ t u) x =
      ∑ j ∈ t, tagOp κ C BF (hF.soft j) (ordinary I V i (u j) x) := by
  have he : ordinary I V i (tagSum V C BF hF hκ t u) =
      ∑ j ∈ t, (tagOp κ C BF (hF.soft j)).compLpL 2 volume (ordinary I V i (u j)) :=
    (map_sum (ordinary I V i) _ t).trans (Finset.sum_congr rfl fun j _ =>
      PhysicalPFFiberMap.ordinary_map V _ _ _ i (u j))
  filter_upwards [sum_compLpL_ae t (fun j => tagOp κ C BF (hF.soft j))
    (fun j => ordinary I V i (u j))] with x hx
  exact (congrArg (fun v : WaveSpace I => v x) he).trans hx

omit [Countable ι] in
theorem potential_tagSum_ae :
    ∀ᵐ x ∂volume, potential I V (tagSum V C BF hF hκ t u) x =
      ∑ j ∈ t, tagOp κ C BF (hF.soft j) (potential I V (u j) x) := by
  have he : potential I V (tagSum V C BF hF hκ t u) =
      ∑ j ∈ t, (tagOp κ C BF (hF.soft j)).compLpL 2 volume (potential I V (u j)) :=
    (map_sum (potential I V) _ t).trans (Finset.sum_congr rfl fun j _ =>
      PhysicalPFFiberMap.potential_map V _ _ _ (u j))
  filter_upwards [sum_compLpL_ae t (fun j => tagOp κ C BF (hF.soft j))
    (fun j => potential I V (u j))] with x hx
  exact (congrArg (fun v : WaveSpace I => v x) he).trans hx

omit [Countable ι] in
theorem radiationSource_tagSum_ae :
    ∀ᵐ x ∂volume, radiationSource I V (tagSum V C BF hF hκ t u) x =
      ∑ j ∈ t, tagGraph κ C BF (hF.soft j) (hF.unit j) hκ (radiationSource I V (u j) x) := by
  have he : radiationSource I V (tagSum V C BF hF hκ t u) =
      ∑ j ∈ t, (tagGraph κ C BF (hF.soft j) (hF.unit j) hκ).compLpL 2 volume
        (radiationSource I V (u j)) :=
    (map_sum (radiationSource I V) _ t).trans (Finset.sum_congr rfl fun j _ =>
      PhysicalPFFiberMap.radiationSource_map V _ _ _ (u j))
  filter_upwards [sum_compLpL_ae t (fun j => tagGraph κ C BF (hF.soft j) (hF.unit j) hκ)
    (fun j => radiationSource I V (u j))] with x hx
  exact (congrArg (fun v : RadiationGraph I => v x) he).trans hx

end Coordinates

attribute [local irreducible] tagSum

section Reference

variable (w : Reference I V)

theorem radiation_ae :
    ∀ᵐ x ∂volume, radiation I V w x = radiationGraphDerivative (radiationSource I V w x) :=
  radiationGraphDerivative.coeFn_compLpL (radiationSource I V w)

theorem potential_ae :
    ∀ᵐ x ∂volume, potential I V w x = (Real.sqrt (V x) : ℂ) • inclusion I V w x := by
  have hp : ∀ᵐ x ∂volume, (potentialSource I V w).val.2 x =
      (Real.sqrt (V x) : ℂ) • (potentialSource I V w).val.1 x := (potentialSource I V w).property
  filter_upwards [hp] with x hx
  exact hx.trans (congrArg (fun v : WaveSpace I => (Real.sqrt (V x) : ℂ) • v x)
    (potential_matches I V w))

variable (k : I → Position I → WeightedPhotonKernel)
  (hk : ∀ i, AEStronglyMeasurable (k i) volume)
  (M : ℝ) (hM : ∀ i, ∀ᵐ x ∂volume, ‖k i x‖ ≤ M)

theorem field_ae (i : I) :
    ∀ᵐ x ∂volume, field I V C k hk M hM i w x = kernelField C (k i x) (radiationSource I V w x) :=
  spatialField_ae volume C (k i) (hk i) M (hM i) (radiationSource I V w)

theorem covariant_ae (e : ℝ) (i : I) :
    ∀ᵐ x ∂volume, covariant I V C k hk M hM e i w x =
      (-Complex.I) • ordinary I V i w x - (e : ℂ) • field I V C k hk M hM i w x := by
  filter_upwards [affine_ae (ordinary I V i w) (field I V C k hk M hM i w) (-Complex.I) (e : ℂ)]
    with x hx
  exact (congrArg (fun v : WaveSpace I => v x) (covariant_apply I V C k hk M hM e i w)).trans hx

end Reference

section Fields

variable (t : Finset ι) (u : ι → Reference I V)
  (hu : ∀ j, ∀ᵐ x ∂volume, inclusion I V (u j) x ∈ generatedFockSubspace (hardOnePhoton κ))

include hu in
theorem radiation_hard_ae :
    ∀ᵐ x ∂volume, ∀ j, radiationGraphInclusion (radiationSource I V (u j) x) ∈
      generatedFockSubspace (hardOnePhoton κ) :=
  ae_all_iff.mpr fun j => reference_radiation_mem I V (hardOnePhoton κ) (u j) (hu j)

include hu in
theorem potential_hard_ae :
    ∀ᵐ x ∂volume, ∀ j, potential I V (u j) x ∈ generatedFockSubspace (hardOnePhoton κ) := by
  filter_upwards [ae_all_iff.mpr hu, ae_all_iff.mpr fun j => potential_ae V (u j)] with x h₁ h₂ j
  exact (h₂ j).symm ▸ Submodule.smul_mem _ _ (h₁ j)

variable (h : I → Position I → WeightedPhotonKernel)
  (hh : ∀ i, AEStronglyMeasurable (h i) volume)
  (Mh : ℝ) (hMh : ∀ i, ∀ᵐ x ∂volume, ‖h i x‖ ≤ Mh)
  (hhard : ∀ i, ∀ᵐ x ∂volume, (h i x).val.1 ∈ hardOnePhoton κ)

include hu hhard in
/-- **The hard field commutes with the tags.** -/
theorem field_tagSum_hard_ae (i : I) :
    ∀ᵐ x ∂volume, field I V C h hh Mh hMh i (tagSum V C BF hF hκ t u) x =
      ∑ j ∈ t, tagOp κ C BF (hF.soft j) (field I V C h hh Mh hMh i (u j) x) := by
  filter_upwards [field_ae V C (tagSum V C BF hF hκ t u) h hh Mh hMh i,
    radiationSource_tagSum_ae V C BF hF hκ t u, hhard i,
    ae_all_iff.mpr fun j => field_ae V C (u j) h hh Mh hMh i,
    radiation_hard_ae V u hu] with x h₁ h₂ h₃ h₄ h₅
  exact h₁.trans ((congrArg (kernelField C (h i x)) h₂).trans
    ((kernelField_tagGraph_sum_hard C BF hF hκ t (h i x) h₃
      (fun j => radiationSource I V (u j) x) h₅).trans
      (Finset.sum_congr rfl fun j _ => congrArg (tagOp κ C BF (hF.soft j)) (h₄ j).symm)))

include hu hhard in
/-- **The hard covariant derivative commutes with the tags.** -/
theorem covariant_tagSum_hard_ae (e : ℝ) (i : I) :
    ∀ᵐ x ∂volume, covariant I V C h hh Mh hMh e i (tagSum V C BF hF hκ t u) x =
      ∑ j ∈ t, tagOp κ C BF (hF.soft j) (covariant I V C h hh Mh hMh e i (u j) x) := by
  filter_upwards [covariant_ae V C (tagSum V C BF hF hκ t u) h hh Mh hMh e i,
    ordinary_tagSum_ae V C BF hF hκ t u i,
    field_tagSum_hard_ae V C BF hF hκ t u hu h hh Mh hMh hhard i,
    ae_all_iff.mpr fun j => covariant_ae V C (u j) h hh Mh hMh e i] with x h₁ h₂ h₃ h₄
  refine h₁.trans ((congrArg₂ (fun a b : PhotonFock => (-Complex.I) • a - (e : ℂ) • b)
    h₂ h₃).trans ((sum_map_affine t (fun j => tagOp κ C BF (hF.soft j))
      (fun j => ordinary I V i (u j) x) (fun j => field I V C h hh Mh hMh i (u j) x)
      (-Complex.I) (e : ℂ)).trans (Finset.sum_congr rfl fun j _ => ?_)))
  exact congrArg (tagOp κ C BF (hF.soft j)) (h₄ j).symm

include hu hhard in
theorem covariant_hard_ae (e : ℝ) (i : I) :
    ∀ᵐ x ∂volume, ∀ j, covariant I V C h hh Mh hMh e i (u j) x ∈
      generatedFockSubspace (hardOnePhoton κ) :=
  ae_all_iff.mpr fun j => reference_covariant_mem I V C (hardOnePhoton κ) h hh Mh hMh hhard
    (u j) (hu j) e i

variable (s : I → Position I → WeightedPhotonKernel)
  (hs : ∀ i, AEStronglyMeasurable (s i) volume)
  (Ms : ℝ) (hMs : ∀ i, ∀ᵐ x ∂volume, ‖s i x‖ ≤ Ms)
  (hsoft : ∀ i, ∀ᵐ x ∂volume, (s i x).val.1 ∈ softOnePhoton κ)

include hu hsoft in
/-- **The soft field estimate on the reference domain.** -/
theorem field_tagSum_soft_norm_sq_ae (i : I) :
    ∀ᵐ x ∂volume, ‖field I V C s hs Ms hMs i (tagSum V C BF hF hκ t u) x‖ ^ 2 ≤
      3 * (‖(s i x).val.1‖ ^ 2 * ∑ j ∈ t, ‖inclusion I V (u j) x‖ ^ 2) := by
  filter_upwards [field_ae V C (tagSum V C BF hF hκ t u) s hs Ms hMs i,
    radiationSource_tagSum_ae V C BF hF hκ t u, hsoft i, radiation_hard_ae V u hu,
    ae_all_iff.mpr fun j => reference_radiation_ae I V (u j)] with x h₁ h₂ h₃ h₄ h₅
  have hb := kernelField_tagGraph_sum_soft_norm_sq_le C BF hF hκ t (s i x) h₃
    (fun j => radiationSource I V (u j) x) h₄
  have hn : ∑ j ∈ t, ‖radiationGraphInclusion (radiationSource I V (u j) x)‖ ^ 2 =
      ∑ j ∈ t, ‖inclusion I V (u j) x‖ ^ 2 :=
    Finset.sum_congr rfl fun j _ => congrArg (fun v : PhotonFock => ‖v‖ ^ 2) (h₅ j).symm
  exact (congrArg (fun v : PhotonFock => ‖v‖ ^ 2)
    (h₁.trans (congrArg (kernelField C (s i x)) h₂))).trans_le
      (hb.trans_eq (congrArg (fun r : ℝ => 3 * (‖(s i x).val.1‖ ^ 2 * r)) hn))

include hu hsoft in
/-- The soft field of the superposition is orthogonal to every superposition
of tags of hard vectors. -/
theorem inner_tagSum_field_soft_ae (i : I) (v : ι → WaveSpace I)
    (hv : ∀ᵐ x ∂volume, ∀ j, v j x ∈ generatedFockSubspace (hardOnePhoton κ)) :
    ∀ᵐ x ∂volume, ⟪∑ j ∈ t, tagOp κ C BF (hF.soft j) (v j x),
      field I V C s hs Ms hMs i (tagSum V C BF hF hκ t u) x⟫_ℂ = 0 := by
  filter_upwards [field_ae V C (tagSum V C BF hF hκ t u) s hs Ms hMs i,
    radiationSource_tagSum_ae V C BF hF hκ t u, hsoft i, radiation_hard_ae V u hu, hv]
    with x h₁ h₂ h₃ h₄ h₅
  have h := tag_sum_inner_kernelField_soft C BF hF hκ t (s i x) h₃
    (fun j => radiationSource I V (u j) x) h₄ (fun j => v j x) h₅
  exact (congrArg (fun z : PhotonFock => ⟪∑ j ∈ t, tagOp κ C BF (hF.soft j) (v j x), z⟫_ℂ)
    (h₁.trans (congrArg (kernelField C (s i x)) h₂))).trans h

end Fields

section Energy

variable (k h s : I → Position I → WeightedPhotonKernel)
  (hk : ∀ i, AEStronglyMeasurable (k i) volume)
  (hh : ∀ i, AEStronglyMeasurable (h i) volume)
  (hs : ∀ i, AEStronglyMeasurable (s i) volume)
  (Mk Mh Ms : ℝ)
  (hMk : ∀ i, ∀ᵐ x ∂volume, ‖k i x‖ ≤ Mk)
  (hMh : ∀ i, ∀ᵐ x ∂volume, ‖h i x‖ ≤ Mh)
  (hMs : ∀ i, ∀ᵐ x ∂volume, ‖s i x‖ ≤ Ms)
  (hsplit : ∀ i, ∀ᵐ x ∂volume, k i x = h i x + s i x)
  (hhard : ∀ i, ∀ᵐ x ∂volume, (h i x).val.1 ∈ hardOnePhoton κ)
  (hsoft : ∀ i, ∀ᵐ x ∂volume, (s i x).val.1 ∈ softOnePhoton κ)
  (t : Finset ι) (u : ι → Reference I V)
  (hu : ∀ j, ∀ᵐ x ∂volume, inclusion I V (u j) x ∈ generatedFockSubspace (hardOnePhoton κ))

omit [DecidableEq I] in
include hsoft in
theorem soft_orthogonal : ∀ i, ∀ᵐ x ∂volume, (s i x).val.1 ∈ (hardOnePhoton κ)ᗮ := fun i =>
  (hsoft i).mono fun _ hx => soft_mem_hard_orthogonal κ hx

include hu in
theorem inclusion_tagSum_norm_sq :
    ‖inclusion I V (tagSum V C BF hF hκ t u)‖ ^ 2 = ∑ j ∈ t, ‖inclusion I V (u j)‖ ^ 2 := by
  apply norm_sq_eq_sum_of_ae
  filter_upwards [inclusion_tagSum_ae V C BF hF hκ t u, ae_all_iff.mpr hu] with x h₁ h₂
  exact (congrArg (fun v : PhotonFock => ‖v‖ ^ 2) h₁).trans
    (tag_sum_norm_sq C BF hF t (fun j => inclusion I V (u j) x) h₂)

include hh Mh hMh hs Ms hMs hsplit hhard hsoft hu in
/-- The covariant derivative of the superposition splits orthogonally into
its hard part and the soft field. -/
theorem covariant_tagSum_norm_sq (e : ℝ) (i : I) :
    ‖covariant I V C k hk Mk hMk e i (tagSum V C BF hF hκ t u)‖ ^ 2 =
      ‖covariant I V C h hh Mh hMh e i (tagSum V C BF hF hκ t u)‖ ^ 2 +
        e ^ 2 * ‖field I V C s hs Ms hMs i (tagSum V C BF hF hκ t u)‖ ^ 2 := by
  have horth : ⟪covariant I V C h hh Mh hMh e i (tagSum V C BF hF hκ t u),
      field I V C s hs Ms hMs i (tagSum V C BF hF hκ t u)⟫_ℂ = 0 := by
    apply inner_eq_zero_of_ae
    filter_upwards [covariant_tagSum_hard_ae V C BF hF hκ t u hu h hh Mh hMh hhard e i,
      inner_tagSum_field_soft_ae V C BF hF hκ t u hu s hs Ms hMs hsoft i
        (fun j => covariant I V C h hh Mh hMh e i (u j))
        (covariant_hard_ae V C u hu h hh Mh hMh hhard e i)] with x h₁ h₂
    exact (congrArg (fun z : PhotonFock =>
      ⟪z, field I V C s hs Ms hMs i (tagSum V C BF hF hκ t u) x⟫_ℂ) h₁).trans h₂
  exact (congrArg (fun z : WaveSpace I => ‖z‖ ^ 2)
    (reference_covariant_split I V C k h s hk hh hs Mk Mh Ms hMk hMh hMs hsplit
      (tagSum V C BF hF hκ t u) e i)).trans (norm_sq_sub_of_inner_zero _ _ horth e)

include hu hhard in
theorem covariant_hard_tagSum_norm_sq (e : ℝ) (i : I) :
    ‖covariant I V C h hh Mh hMh e i (tagSum V C BF hF hκ t u)‖ ^ 2 =
      ∑ j ∈ t, ‖covariant I V C h hh Mh hMh e i (u j)‖ ^ 2 := by
  apply norm_sq_eq_sum_of_ae
  filter_upwards [covariant_tagSum_hard_ae V C BF hF hκ t u hu h hh Mh hMh hhard e i,
    covariant_hard_ae V C u hu h hh Mh hMh hhard e i] with x h₁ h₂
  exact (congrArg (fun v : PhotonFock => ‖v‖ ^ 2) h₁).trans
    (tag_sum_norm_sq C BF hF t (fun j => covariant I V C h hh Mh hMh e i (u j) x) h₂)

include hu hsoft in
theorem field_soft_tagSum_le (σ : ℝ) (hσ : ∀ᵐ x ∂volume, ∑ i, ‖(s i x).val.1‖ ^ 2 ≤ σ) :
    ∑ i ∈ Finset.univ, ‖field I V C s hs Ms hMs i (tagSum V C BF hF hκ t u)‖ ^ 2 ≤
      ∑ j ∈ t, (3 * σ * ‖inclusion I V (u j)‖ ^ 2 + 0 * ‖inclusion I V (u j)‖ ^ 2) := by
  apply sum_norm_sq_le_of_ae
  filter_upwards [ae_all_iff.mpr fun i =>
    field_tagSum_soft_norm_sq_ae V C BF hF hκ t u hu s hs Ms hMs hsoft i, hσ] with x h₁ h₂
  have hm : 0 ≤ ∑ j ∈ t, ‖inclusion I V (u j) x‖ ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  refine (Finset.sum_le_sum fun i _ => h₁ i).trans ?_
  exact scalar_soft_bound _ _ _ _ hm h₂

include hu in
theorem radiation_tagSum_le :
    ‖radiation I V (tagSum V C BF hF hκ t u)‖ ^ 2 ≤
      ∑ j ∈ t, (κ * ‖inclusion I V (u j)‖ ^ 2 + 1 * ‖radiation I V (u j)‖ ^ 2) := by
  have h := sum_norm_sq_le_of_ae ({()} : Finset Unit)
    (fun _ => radiation I V (tagSum V C BF hF hκ t u)) t (fun _ => κ) (fun _ => 1)
    (fun j => inclusion I V (u j)) (fun j => radiation I V (u j)) (by
      filter_upwards [radiation_ae V (tagSum V C BF hF hκ t u),
        radiationSource_tagSum_ae V C BF hF hκ t u, radiation_hard_ae V u hu,
        ae_all_iff.mpr fun j => radiation_ae V (u j),
        ae_all_iff.mpr fun j => reference_radiation_ae I V (u j)] with x h₁ h₂ h₃ h₄ h₅
      have hb := tagGraph_sum_derivative_norm_sq_le C BF hF hκ t
        (fun j => radiationSource I V (u j) x) h₃
      refine (Finset.sum_singleton _ _).trans_le ((congrArg (fun v : PhotonFock => ‖v‖ ^ 2)
        (h₁.trans (congrArg radiationGraphDerivative h₂))).trans_le (hb.trans_eq ?_))
      exact Finset.sum_congr rfl fun j _ => (add_one_mul' _ _).trans
        (congrArg₂ (fun a b : PhotonFock => κ * ‖a‖ ^ 2 + 1 * ‖b‖ ^ 2) (h₅ j).symm (h₄ j).symm))
  exact (Finset.sum_singleton (fun _ : Unit =>
    ‖radiation I V (tagSum V C BF hF hκ t u)‖ ^ 2) ()).symm.trans_le h

include hu in
theorem potential_tagSum_norm_sq :
    ‖potential I V (tagSum V C BF hF hκ t u)‖ ^ 2 = ∑ j ∈ t, ‖potential I V (u j)‖ ^ 2 := by
  apply norm_sq_eq_sum_of_ae
  filter_upwards [potential_tagSum_ae V C BF hF hκ t u, potential_hard_ae V u hu] with x h₁ h₂
  exact (congrArg (fun v : PhotonFock => ‖v‖ ^ 2) h₁).trans
    (tag_sum_norm_sq C BF hF t (fun j => potential I V (u j) x) h₂)

omit [Countable ι] in
include hs Ms hMs hsplit hhard hsoft hu in
theorem hard_energy_le (e : ℝ) (j : ι) :
    (1 / 2 : ℝ) * ∑ i, ‖covariant I V C h hh Mh hMh e i (u j)‖ ^ 2 +
      ‖radiation I V (u j)‖ ^ 2 + ‖potential I V (u j)‖ ^ 2 ≤
        energy I V C k hk Mk hMk e (u j) := by
  have heq := reference_energy_eq I V C (hardOnePhoton κ) k h s hk hh hs Mk Mh Ms hMk hMh hMs
    hsplit hhard (soft_orthogonal s hsoft) (u j) (hu j) e
  have hnn : 0 ≤ e ^ 2 / 2 * ∑ i, ‖field I V C s hs Ms hMs i (u j)‖ ^ 2 := by positivity
  exact (le_add_of_nonneg_right hnn).trans_eq heq.symm

include hh Mh hMh hs Ms hMs hsplit hhard hsoft hu in
/-- **The tagging energy estimate**,
`E(∑ⱼ T_j u_j) ≤ ∑ⱼ E(u_j) + (κ + 3 e² σ / 2) ∑ⱼ ‖u_j‖²`. -/
theorem energy_tagSum_le (e σ : ℝ) (hσ : ∀ᵐ x ∂volume, ∑ i, ‖(s i x).val.1‖ ^ 2 ≤ σ) :
    energy I V C k hk Mk hMk e (tagSum V C BF hF hκ t u) ≤
      ∑ j ∈ t, energy I V C k hk Mk hMk e (u j) +
        (κ + 3 * e ^ 2 * σ / 2) * ∑ j ∈ t, ‖inclusion I V (u j)‖ ^ 2 :=
  energy_assemble t
    (fun i => ‖covariant I V C k hk Mk hMk e i (tagSum V C BF hF hκ t u)‖ ^ 2)
    (fun i => ‖covariant I V C h hh Mh hMh e i (tagSum V C BF hF hκ t u)‖ ^ 2)
    (fun i => ‖field I V C s hs Ms hMs i (tagSum V C BF hF hκ t u)‖ ^ 2)
    (fun i j => ‖covariant I V C h hh Mh hMh e i (u j)‖ ^ 2)
    (‖radiation I V (tagSum V C BF hF hκ t u)‖ ^ 2)
    (‖potential I V (tagSum V C BF hF hκ t u)‖ ^ 2)
    (fun j => ‖radiation I V (u j)‖ ^ 2) (fun j => ‖potential I V (u j)‖ ^ 2)
    (fun j => ‖inclusion I V (u j)‖ ^ 2)
    (fun j => energy I V C k hk Mk hMk e (u j)) e σ κ
    (covariant_tagSum_norm_sq V C BF hF hκ k h s hk hh hs Mk Mh Ms hMk hMh hMs hsplit hhard
      hsoft t u hu e)
    (covariant_hard_tagSum_norm_sq V C BF hF hκ h hh Mh hMh hhard t u hu e)
    (field_soft_tagSum_le V C BF hF hκ s hs Ms hMs hsoft t u hu σ hσ)
    (radiation_tagSum_le V C BF hF hκ t u hu)
    (potential_tagSum_norm_sq V C BF hF hκ t u hu)
    (fun j _ => hard_energy_le V C k h s hk hh hs Mk Mh Ms hMk hMh hMs hsplit hhard hsoft u hu
      e j)

include hh Mh hMh hs Ms hMs hsplit hhard hsoft hu in
/-- **The current of a tag superposition** is the sum of the currents. -/
theorem current_tagSum_ae (e : ℝ) (i : I) :
    ∀ᵐ x ∂volume, ⟪inclusion I V (tagSum V C BF hF hκ t u) x,
      covariant I V C k hk Mk hMk e i (tagSum V C BF hF hκ t u) x⟫_ℂ =
      ∑ j ∈ t, ⟪inclusion I V (u j) x, covariant I V C k hk Mk hMk e i (u j) x⟫_ℂ := by
  have hsplitQ := reference_covariant_split I V C k h s hk hh hs Mk Mh Ms hMk hMh hMs hsplit
    (tagSum V C BF hF hκ t u) e i
  filter_upwards [sub_smul_ae (covariant I V C h hh Mh hMh e i (tagSum V C BF hF hκ t u))
      (field I V C s hs Ms hMs i (tagSum V C BF hF hκ t u)) (e : ℂ),
    inclusion_tagSum_ae V C BF hF hκ t u,
    covariant_tagSum_hard_ae V C BF hF hκ t u hu h hh Mh hMh hhard e i,
    inner_tagSum_field_soft_ae V C BF hF hκ t u hu s hs Ms hMs hsoft i
      (fun j => inclusion I V (u j)) (ae_all_iff.mpr hu),
    ae_all_iff.mpr hu, covariant_hard_ae V C u hu h hh Mh hMh hhard e i,
    ae_all_iff.mpr fun j => reference_current_eq I V C (hardOnePhoton κ) k h s hk hh hs
      Mk Mh Ms hMk hMh hMs hsplit (soft_orthogonal s hsoft) (u j) (hu j) e i]
    with x h₁ h₂ h₃ h₄ h₅ h₆ h₇
  have hc : covariant I V C k hk Mk hMk e i (tagSum V C BF hF hκ t u) x =
      covariant I V C h hh Mh hMh e i (tagSum V C BF hF hκ t u) x -
        (e : ℂ) • field I V C s hs Ms hMs i (tagSum V C BF hF hκ t u) x :=
    (congrArg (fun z : WaveSpace I => z x) hsplitQ).trans h₁
  have hfield : ⟪inclusion I V (tagSum V C BF hF hκ t u) x,
      field I V C s hs Ms hMs i (tagSum V C BF hF hκ t u) x⟫_ℂ = 0 :=
    (congrArg (fun z : PhotonFock =>
      ⟪z, field I V C s hs Ms hMs i (tagSum V C BF hF hκ t u) x⟫_ℂ) h₂).trans h₄
  refine (congrArg (fun z : PhotonFock => ⟪inclusion I V (tagSum V C BF hF hκ t u) x, z⟫_ℂ)
    hc).trans ((inner_sub_smul_of_zero _ _ _ _ hfield).trans ?_)
  refine (congrArg₂ (fun a b : PhotonFock => ⟪a, b⟫_ℂ) h₂ h₃).trans
    ((tag_sum_inner C BF hF t _ _ h₅ h₆).trans ?_)
  exact Finset.sum_congr rfl fun j _ => (h₇ j).symm

include hu in
theorem density_tagSum_ae :
    ∀ᵐ x ∂volume, ⟪inclusion I V (tagSum V C BF hF hκ t u) x,
      inclusion I V (tagSum V C BF hF hκ t u) x⟫_ℂ =
      ∑ j ∈ t, ⟪inclusion I V (u j) x, inclusion I V (u j) x⟫_ℂ := by
  filter_upwards [inclusion_tagSum_ae V C BF hF hκ t u, ae_all_iff.mpr hu] with x h₁ h₂
  exact (congrArg (fun a : PhotonFock => ⟪a, a⟫_ℂ) h₁).trans (tag_sum_inner C BF hF t _ _ h₂ h₂)

end Energy

end GptLean.PhysicalPFSoftTag
