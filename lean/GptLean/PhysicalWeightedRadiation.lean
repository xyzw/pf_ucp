import GptLean.PhysicalRadiationCross
import GptLean.PhysicalWeylIntegralGraph

/-! Radiation displacement at form regularity. Only the square-root-frequency
weighted displacement belongs to L². No full-frequency L² premise is used. -/

noncomputable section
namespace GptLean.PhysicalWeyl

open MeasureTheory Filter Topology PhysicalFock Representability
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

section Sequence

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Tensoring the shell coefficients with a photon vector. -/
def coefficientSequence (y : Lp ℂ 2 photonMeasure) (u : H) : lp (fun _ : ℕ => H) 2 :=
  ⟨fun i => ⟪sFamily i, y⟫_ℂ • u, memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, norm_smul, mul_pow] using
      (sFamily_parseval y).summable.mul_right (‖u‖ ^ 2))⟩

theorem coefficientSequence_norm_sq (y : Lp ℂ 2 photonMeasure) (u : H) :
    ‖coefficientSequence y u‖ ^ 2 = ‖y‖ ^ 2 * ‖u‖ ^ 2 := by
  have h := coordinate_mass_hasSum (fun _ : ℕ => H) (coefficientSequence y u)
  have h' : HasSum (fun i => ‖⟪sFamily i, y⟫_ℂ‖ ^ 2 * ‖u‖ ^ 2)
      (‖y‖ ^ 2 * ‖u‖ ^ 2) := (sFamily_parseval y).mul_right (‖u‖ ^ 2)
  apply h.unique
  apply h'.congr_fun
  intro i
  change ‖⟪sFamily i, y⟫_ℂ • u‖ ^ 2 = ‖⟪sFamily i, y⟫_ℂ‖ ^ 2 * ‖u‖ ^ 2
  rw [norm_smul, mul_pow]

theorem coefficientSequence_norm (y : Lp ℂ 2 photonMeasure) (u : H) :
    ‖coefficientSequence y u‖ = ‖y‖ * ‖u‖ := by
  apply (pow_left_inj₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) two_ne_zero).mp
  exact (coefficientSequence_norm_sq y u).trans (mul_pow _ _ _).symm

/-- The shell tensor map is jointly continuous and complex bilinear. -/
def coefficientTensor : Lp ℂ 2 photonMeasure →L[ℂ] H →L[ℂ] lp (fun _ : ℕ => H) 2 :=
  (LinearMap.mk₂ ℂ (fun (y : Lp ℂ 2 photonMeasure) (u : H) => coefficientSequence y u)
    (fun y z u => by
      apply lp.ext
      funext i
      change ⟪sFamily i, y + z⟫_ℂ • u = ⟪sFamily i, y⟫_ℂ • u + ⟪sFamily i, z⟫_ℂ • u
      rw [inner_add_right, add_smul])
    (fun c y u => by
      apply lp.ext
      funext i
      change ⟪sFamily i, c • y⟫_ℂ • u = c • (⟪sFamily i, y⟫_ℂ • u)
      rw [inner_smul_right, mul_smul])
    (fun y u v => by
      apply lp.ext
      funext i
      exact smul_add _ _ _)
    (fun c y u => by
      apply lp.ext
      funext i
      exact smul_comm _ _ _)).mkContinuous₂ 1
      (fun y u => by
        change ‖coefficientSequence y u‖ ≤ 1 * ‖y‖ * ‖u‖
        rw [coefficientSequence_norm, one_mul])

theorem coefficientTensor_apply (y : Lp ℂ 2 photonMeasure) (u : H) (i : ℕ) :
    coefficientTensor y u i = ⟪sFamily i, y⟫_ℂ • u := rfl

theorem coefficientTensor_norm_sq (y : Lp ℂ 2 photonMeasure) (u : H) :
    ‖coefficientTensor y u‖ ^ 2 = ‖y‖ ^ 2 * ‖u‖ ^ 2 :=
  coefficientSequence_norm_sq y u

theorem coefficientTensor_norm (y : Lp ℂ 2 photonMeasure) (u : H) :
    ‖coefficientTensor y u‖ = ‖y‖ * ‖u‖ := coefficientSequence_norm y u

theorem coefficientTensor_inner_abs_le (v : lp (fun _ : ℕ => H) 2)
    (y : Lp ℂ 2 photonMeasure) (u : H) :
    |2 * (⟪v, coefficientTensor y u⟫_ℂ).re| ≤ 2 * ‖v‖ * ‖y‖ * ‖u‖ := by
  have h := (Complex.abs_re_le_norm ⟪v, coefficientTensor y u⟫_ℂ).trans
    (norm_inner_le_norm v (coefficientTensor y u))
  rw [coefficientTensor_norm] at h
  rw [abs_mul, abs_two]
  nlinarith

theorem coefficientTensor_add_norm_sq (v : lp (fun _ : ℕ => H) 2)
    (y : Lp ℂ 2 photonMeasure) (u : H) :
    ‖v + coefficientTensor y u‖ ^ 2 = ‖v‖ ^ 2 +
      2 * (⟪v, coefficientTensor y u⟫_ℂ).re + ‖y‖ ^ 2 * ‖u‖ ^ 2 := by
  rw [norm_add_sq (𝕜 := ℂ), coefficientTensor_norm_sq]
  rfl

end Sequence

theorem radiationAnalysis_apply (q : RadiationGraphSpace) (i : ℕ) :
    radiationAnalysis q i = kernelAnnihilation (shellKernel i) q := rfl

attribute [local irreducible] coefficientTensor radiationAnalysis

/-- The extended field form with inverse-frequency argument `y`. -/
def weightedField (y : Lp ℂ 2 photonMeasure) (q : RadiationGraphSpace) : ℝ :=
  2 * (⟪radiationAnalysis q, coefficientTensor y (radiationGraphInclusion q)⟫_ℂ).re

theorem weightedField_abs_le (y : Lp ℂ 2 photonMeasure) (q : RadiationGraphSpace) :
    |weightedField y q| ≤ 2 * ‖y‖ * ‖radiationGraphDerivative q‖ * ‖radiationGraphInclusion q‖ := by
  have h := coefficientTensor_inner_abs_le (radiationAnalysis q) y (radiationGraphInclusion q)
  rw [radiationAnalysis_norm] at h
  exact h.trans_eq (by ring)

theorem weightedField_continuous : Continuous (fun z : Lp ℂ 2 photonMeasure × RadiationGraphSpace =>
    weightedField z.1 z.2) := by
  exact continuous_const.mul (Complex.continuous_re.comp
    ((radiationAnalysis.continuous.comp continuous_snd).inner
      (coefficientTensor.continuous₂.comp
        (continuous_fst.prodMk (radiationGraphInclusion.continuous.comp continuous_snd)))))

theorem weightedField_add (y z : Lp ℂ 2 photonMeasure) (q : RadiationGraphSpace) :
    weightedField (y + z) q = weightedField y q + weightedField z q := by
  simp only [weightedField, map_add, ContinuousLinearMap.add_apply, inner_add_right, Complex.add_re]
  ring

private theorem real_cross_scalar (c : ℝ) (z : ℂ) :
    2 * ((c : ℂ) * z).re = c * (2 * z.re) := by
  rw [Complex.re_ofReal_mul]
  ring

theorem weightedField_real_smul (c : ℝ) (y : Lp ℂ 2 photonMeasure) (q : RadiationGraphSpace) :
    weightedField (c • y) q = c * weightedField y q := by
  rw [weightedField, RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul,
    ContinuousLinearMap.smul_apply, inner_smul_right]
  change 2 * ((c : ℂ) * ⟪radiationAnalysis q, coefficientTensor y (radiationGraphInclusion q)⟫_ℂ).re =
    c * (2 * (⟪radiationAnalysis q, coefficientTensor y (radiationGraphInclusion q)⟫_ℂ).re)
  exact real_cross_scalar c _

def weightedFieldLinear (q : RadiationGraphSpace) : Lp ℂ 2 photonMeasure →ₗ[ℝ] ℝ where
  toFun y := weightedField y q
  map_add' y z := weightedField_add y z q
  map_smul' c y := weightedField_real_smul c y q

theorem weightedField_sum {ι : Type*} (s : Finset ι) (y : ι → Lp ℂ 2 photonMeasure)
    (q : RadiationGraphSpace) : weightedField (∑ i ∈ s, y i) q = ∑ i ∈ s, weightedField (y i) q :=
  map_sum (weightedFieldLinear q) y s

/-- On ordinary weighted kernels, the extended field has the existing
annihilation-field value. -/
theorem weightedField_eq_annihilation {f : Lp ℂ 2 photonMeasure} (K : WeightedPhotonKernel)
    (hK : ∀ᵐ p ∂photonMeasure, K.val.2 p = (Real.sqrt ‖p.1‖ : ℂ) * f p)
    (q : RadiationGraphSpace) :
    weightedField K.val.2 q = 2 * (⟪kernelAnnihilation K q, radiationGraphInclusion q⟫_ℂ).re := by
  have hs := lp.hasSum_inner (𝕜 := ℂ) (radiationAnalysis q)
    (coefficientTensor K.val.2 (radiationGraphInclusion q))
  have ht : HasSum (fun i => ⟪radiationAnalysis q i,
      coefficientTensor K.val.2 (radiationGraphInclusion q) i⟫_ℂ)
      ⟪kernelAnnihilation K q, radiationGraphInclusion q⟫_ℂ := by
    apply (cross_hasSum K hK q).congr_fun
    intro i
    rw [radiationAnalysis_apply, coefficientTensor_apply, inner_smul_right, radiationFamily_inner K hK]
  exact congrArg (fun z : ℂ => 2 * z.re) (hs.unique ht)

section Displacement

variable (W : ConcreteWeylLaw photonMeasure) (f y : Lp ℂ 2 photonMeasure)
  (hy : ∀ᵐ p ∂photonMeasure, y p = (Real.sqrt ‖p.1‖ : ℂ) * f p)

include hy in
theorem radiationFamily_inner_weighted (i : ℕ) :
    ⟪radiationFamily i, f⟫_ℂ = ⟪sFamily i, y⟫_ℂ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [radiationFamily_weighted i, hy] with p h₁ h₂
  rw [h₁, h₂]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

include hy in
/-- The actual radiation form after displacement, under the sharp UV hypothesis. -/
theorem radiationForm_weyl_weighted (q : RadiationGraphSpace) :
    radiationForm (W.weyl f (radiationGraphInclusion q)) = ENNReal.ofReal
      (‖radiationGraphDerivative q‖ ^ 2 + weightedField y q +
        ‖y‖ ^ 2 * ‖radiationGraphInclusion q‖ ^ 2) := by
  let v := radiationAnalysis q + coefficientTensor y (radiationGraphInclusion q)
  have hshift (i : ℕ) : annihilationForm photonMeasure (radiationFamily i)
      (W.weyl f (radiationGraphInclusion q)) = ENNReal.ofReal (‖v i‖ ^ 2) := by
    have hgraph : AnnihilationGraph photonMeasure (radiationFamily i)
        (radiationGraphInclusion q) (kernelAnnihilation (shellKernel i) q) := fun n => rfl
    have h := (AnnihilationGraph.form_eq photonMeasure
      (W.annihilation_shift f _ _ _ hgraph)).trans
        (congrArg (fun z : ℝ => ENNReal.ofReal (z ^ 2)) (LinearIsometryEquiv.norm_map _ _))
    rw [radiationFamily_inner_weighted f y hy i] at h
    simpa only [v, lp.coeFn_add, Pi.add_apply, radiationAnalysis_apply, coefficientTensor_apply] using h
  have hmass := coordinate_mass_hasSum (fun _ : ℕ => PhotonFock) v
  calc radiationForm (W.weyl f (radiationGraphInclusion q))
      = ∑' i, ENNReal.ofReal (‖v i‖ ^ 2) :=
        (sum_annihilationForm_eq_radiationForm _).symm.trans (tsum_congr hshift)
    _ = ENNReal.ofReal (‖v‖ ^ 2) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hmass.summable).symm.trans
        (congrArg ENNReal.ofReal hmass.tsum_eq)
    _ = _ := by
      congr 1
      change ‖radiationAnalysis q + coefficientTensor y (radiationGraphInclusion q)‖ ^ 2 = _
      rw [coefficientTensor_add_norm_sq, radiationAnalysis_norm]
      rfl

include hy in
theorem weyl_weighted_mem_domain (q : RadiationGraphSpace) :
    W.weyl f (radiationGraphInclusion q) ∈ radiationRoot.domain := by
  apply (radiationRoot_domain_iff_finite _).mpr
  rw [radiationForm_weyl_weighted W f y hy q]
  exact ENNReal.ofReal_lt_top

/-- The closed radiation graph lift at square-root-frequency regularity. -/
def weylWeightedGraphFun (q : RadiationGraphSpace) : RadiationGraphSpace :=
  ⟨(W.weyl f (radiationGraphInclusion q),
    radiationRoot ⟨_, weyl_weighted_mem_domain W f y hy q⟩),
      radiationRoot.mem_graph ⟨_, weyl_weighted_mem_domain W f y hy q⟩⟩

theorem weighted_shift_nonneg (q : RadiationGraphSpace) :
    0 ≤ ‖radiationGraphDerivative q‖ ^ 2 + weightedField y q +
      ‖y‖ ^ 2 * ‖radiationGraphInclusion q‖ ^ 2 := by
  have h := sq_nonneg (‖radiationAnalysis q + coefficientTensor y (radiationGraphInclusion q)‖)
  rw [coefficientTensor_add_norm_sq, radiationAnalysis_norm] at h
  exact h

theorem weylWeightedGraphFun_derivative_norm_sq (q : RadiationGraphSpace) :
    ‖radiationGraphDerivative (weylWeightedGraphFun W f y hy q)‖ ^ 2 =
      ‖radiationGraphDerivative q‖ ^ 2 + weightedField y q +
        ‖y‖ ^ 2 * ‖radiationGraphInclusion q‖ ^ 2 := by
  have h := (radiationRoot_energy ⟨_, weyl_weighted_mem_domain W f y hy q⟩).symm.trans
    (radiationForm_weyl_weighted W f y hy q)
  exact (ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _) (weighted_shift_nonneg y q)).mp h

theorem weylWeightedGraphFun_derivative_sq_le (q : RadiationGraphSpace) :
    ‖radiationGraphDerivative (weylWeightedGraphFun W f y hy q)‖ ^ 2 ≤
      2 * ‖radiationGraphDerivative q‖ ^ 2 +
        2 * ‖y‖ ^ 2 * ‖radiationGraphInclusion q‖ ^ 2 := by
  rw [weylWeightedGraphFun_derivative_norm_sq]
  have h := (le_abs_self (weightedField y q)).trans (weightedField_abs_le y q)
  nlinarith [sq_nonneg (‖radiationGraphDerivative q‖ - ‖y‖ * ‖radiationGraphInclusion q‖)]

theorem weylWeightedGraphFun_derivative_le (q : RadiationGraphSpace) :
    ‖radiationGraphDerivative (weylWeightedGraphFun W f y hy q)‖ ≤
      ‖radiationGraphDerivative q‖ + ‖y‖ * ‖radiationGraphInclusion q‖ := by
  have hre := (le_abs_self (weightedField y q)).trans (weightedField_abs_le y q)
  have hsq : ‖radiationGraphDerivative (weylWeightedGraphFun W f y hy q)‖ ^ 2 ≤
      (‖radiationGraphDerivative q‖ + ‖y‖ * ‖radiationGraphInclusion q‖) ^ 2 := by
    rw [weylWeightedGraphFun_derivative_norm_sq]
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

theorem weylWeightedGraphFun_add (q r : RadiationGraphSpace) :
    weylWeightedGraphFun W f y hy (q + r) = weylWeightedGraphFun W f y hy q + weylWeightedGraphFun W f y hy r := by
  have hx : W.weyl f (radiationGraphInclusion (q + r)) =
      W.weyl f (radiationGraphInclusion q) + W.weyl f (radiationGraphInclusion r) :=
    (congrArg (W.weyl f) (map_add radiationGraphInclusion q r)).trans (map_add _ _ _)
  apply Subtype.ext
  apply Prod.ext
  · exact hx
  · change radiationRoot ⟨_, weyl_weighted_mem_domain W f y hy (q + r)⟩ =
      radiationRoot ⟨_, weyl_weighted_mem_domain W f y hy q⟩ + radiationRoot ⟨_, weyl_weighted_mem_domain W f y hy r⟩
    rw [← LinearPMap.map_add]
    exact congrArg radiationRoot (Subtype.ext hx)

theorem weylWeightedGraphFun_smul (a : ℂ) (q : RadiationGraphSpace) :
    weylWeightedGraphFun W f y hy (a • q) = a • weylWeightedGraphFun W f y hy q := by
  have hx : W.weyl f (radiationGraphInclusion (a • q)) =
      a • W.weyl f (radiationGraphInclusion q) :=
    (congrArg (W.weyl f) (map_smul radiationGraphInclusion a q)).trans (map_smul _ _ _)
  apply Subtype.ext
  apply Prod.ext
  · exact hx
  · change radiationRoot ⟨_, weyl_weighted_mem_domain W f y hy (a • q)⟩ =
      a • radiationRoot ⟨_, weyl_weighted_mem_domain W f y hy q⟩
    rw [← LinearPMap.map_smul]
    exact congrArg radiationRoot (Subtype.ext hx)

theorem weylWeightedGraphFun_norm_le (q : RadiationGraphSpace) :
    ‖weylWeightedGraphFun W f y hy q‖ ≤ (1 + ‖y‖) * ‖q‖ := by
  have hq1 : ‖radiationGraphInclusion q‖ ≤ ‖q‖ := norm_fst_le q.val
  have hq2 : ‖radiationGraphDerivative q‖ ≤ ‖q‖ := norm_snd_le q.val
  have hk := norm_nonneg y
  have h1 : ‖radiationGraphInclusion (weylWeightedGraphFun W f y hy q)‖ ≤ (1 + ‖y‖) * ‖q‖ := by
    change ‖W.weyl f (radiationGraphInclusion q)‖ ≤ _
    rw [LinearIsometryEquiv.norm_map]
    nlinarith [norm_nonneg q]
  have h2 : ‖radiationGraphDerivative (weylWeightedGraphFun W f y hy q)‖ ≤ (1 + ‖y‖) * ‖q‖ := by
    refine (weylWeightedGraphFun_derivative_le W f y hy q).trans ?_
    nlinarith [mul_le_mul_of_nonneg_left hq1 hk]
  change max ‖radiationGraphInclusion (weylWeightedGraphFun W f y hy q)‖
    ‖radiationGraphDerivative (weylWeightedGraphFun W f y hy q)‖ ≤ _
  exact max_le h1 h2

/-- **`W(f)` on the radiation graph.** -/
def weylWeightedGraph : RadiationGraphSpace →L[ℂ] RadiationGraphSpace :=
  LinearMap.mkContinuous
    { toFun := weylWeightedGraphFun W f y hy
      map_add' := weylWeightedGraphFun_add W f y hy
      map_smul' := weylWeightedGraphFun_smul W f y hy }
    (1 + ‖y‖) (weylWeightedGraphFun_norm_le W f y hy)

theorem weylWeightedGraph_inclusion (q : RadiationGraphSpace) :
    radiationGraphInclusion (weylWeightedGraph W f y hy q) = W.weyl f (radiationGraphInclusion q) := rfl

theorem weylWeightedGraph_derivative_norm_sq (q : RadiationGraphSpace) :
    ‖radiationGraphDerivative (weylWeightedGraph W f y hy q)‖ ^ 2 =
      ‖radiationGraphDerivative q‖ ^ 2 +
        weightedField y q +
        ‖y‖ ^ 2 * ‖radiationGraphInclusion q‖ ^ 2 :=
  weylWeightedGraphFun_derivative_norm_sq W f y hy q


end Displacement

attribute [local irreducible] weightedField

section Spatial

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}
  (W : ConcreteWeylLaw photonMeasure)
  (f y : X → Lp ℂ 2 photonMeasure)
  (hy : ∀ x, ∀ᵐ p ∂photonMeasure, y x p = (Real.sqrt ‖p.1‖ : ℂ) * f x p)
  (q : X → RadiationGraphSpace)

/-- The cross term is bounded by the two nonnegative energy terms. -/
theorem weightedField_abs_le_energy (y : Lp ℂ 2 photonMeasure) (q : RadiationGraphSpace) :
    |weightedField y q| ≤ ‖radiationGraphDerivative q‖ ^ 2 +
      ‖y‖ ^ 2 * ‖radiationGraphInclusion q‖ ^ 2 := by
  have h := weightedField_abs_le y q
  nlinarith [sq_nonneg (‖radiationGraphDerivative q‖ - ‖y‖ * ‖radiationGraphInclusion q‖)]

include hy in
theorem weylWeightedGraph_aestronglyMeasurable
    (hf : AEStronglyMeasurable f ν) (hq : AEStronglyMeasurable q ν) :
    AEStronglyMeasurable (fun x => weylWeightedGraph W (f x) (y x) (hy x) (q x)) ν := by
  apply radiationGraph_aestronglyMeasurable
  exact W.continuous.comp_aestronglyMeasurable
    (hf.prodMk (radiationGraphInclusion.continuous.comp_aestronglyMeasurable hq))

include hy in
theorem weylWeightedGraph_memLp
    (hf : AEStronglyMeasurable f ν) (hq : MemLp q 2 ν)
    (hpol : Integrable (fun x => ‖y x‖ ^ 2 * ‖radiationGraphInclusion (q x)‖ ^ 2) ν) :
    MemLp (fun x => weylWeightedGraph W (f x) (y x) (hy x) (q x)) 2 ν := by
  apply (memLp_two_iff_integrable_sq_norm
    (weylWeightedGraph_aestronglyMeasurable W f y hy q hf hq.aestronglyMeasurable)).mpr
  have hmass := (memLp_two_iff_integrable_sq_norm hq.aestronglyMeasurable).mp hq
  apply ((hmass.const_mul 3).add (hpol.const_mul 2)).mono'
    ((weylWeightedGraph_aestronglyMeasurable W f y hy q hf hq.aestronglyMeasurable).norm.pow 2)
  refine ae_of_all _ fun x => ?_
  change ‖‖weylWeightedGraph W (f x) (y x) (hy x) (q x)‖ ^ 2‖ ≤
    3 * ‖q x‖ ^ 2 + 2 * (‖y x‖ ^ 2 * ‖radiationGraphInclusion (q x)‖ ^ 2)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have h := weylWeightedGraphFun_derivative_sq_le W (f x) (y x) (hy x) (q x)
  change ‖radiationGraphDerivative (weylWeightedGraph W (f x) (y x) (hy x) (q x))‖ ^ 2 ≤
    2 * ‖radiationGraphDerivative (q x)‖ ^ 2 +
      2 * ‖y x‖ ^ 2 * ‖radiationGraphInclusion (q x)‖ ^ 2 at h
  have hu : ‖radiationGraphInclusion (q x)‖ ≤ ‖q x‖ := norm_fst_le (q x).val
  have hr : ‖radiationGraphDerivative (q x)‖ ≤ ‖q x‖ := norm_snd_le (q x).val
  have hin : ‖radiationGraphInclusion (weylWeightedGraph W (f x) (y x) (hy x) (q x))‖ =
      ‖radiationGraphInclusion (q x)‖ := LinearIsometryEquiv.norm_map _ _
  change (max ‖radiationGraphInclusion (weylWeightedGraph W (f x) (y x) (hy x) (q x))‖
    ‖radiationGraphDerivative (weylWeightedGraph W (f x) (y x) (hy x) (q x))‖) ^ 2 ≤ _
  rw [hin]
  rcases le_total ‖radiationGraphInclusion (q x)‖
    ‖radiationGraphDerivative (weylWeightedGraph W (f x) (y x) (hy x) (q x))‖ with hle | hle
  · rw [max_eq_right hle]
    nlinarith [norm_nonneg (q x), norm_nonneg (radiationGraphDerivative (q x))]
  · rw [max_eq_left hle]
    nlinarith [norm_nonneg (q x), norm_nonneg (radiationGraphInclusion (q x)),
      mul_nonneg (sq_nonneg ‖y x‖) (sq_nonneg ‖radiationGraphInclusion (q x)‖)]

theorem weightedField_integrable
    (hy : AEStronglyMeasurable y ν) (hq : MemLp q 2 ν)
    (hpol : Integrable (fun x => ‖y x‖ ^ 2 * ‖radiationGraphInclusion (q x)‖ ^ 2) ν) :
    Integrable (fun x => weightedField (y x) (q x)) ν := by
  have hr : MemLp (fun x => radiationGraphDerivative (q x)) 2 ν :=
    radiationGraphDerivative.comp_memLp' hq
  have hrad : Integrable (fun x => ‖radiationGraphDerivative (q x)‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm hr.aestronglyMeasurable).mp hr
  have hm : AEStronglyMeasurable (fun x => weightedField (y x) (q x)) ν :=
    weightedField_continuous.comp_aestronglyMeasurable (hy.prodMk hq.aestronglyMeasurable)
  apply (hrad.add hpol).mono' hm
  refine ae_of_all _ fun x => ?_
  change |weightedField (y x) (q x)| ≤ ‖radiationGraphDerivative (q x)‖ ^ 2 +
    ‖y x‖ ^ 2 * ‖radiationGraphInclusion (q x)‖ ^ 2
  exact weightedField_abs_le_energy (y x) (q x)

theorem weightedField_integral_abs_le
    (hy : AEStronglyMeasurable y ν) (hq : MemLp q 2 ν)
    (hpol : Integrable (fun x => ‖y x‖ ^ 2 * ‖radiationGraphInclusion (q x)‖ ^ 2) ν) :
    |∫ x, weightedField (y x) (q x) ∂ν| ≤
      (∫ x, ‖radiationGraphDerivative (q x)‖ ^ 2 ∂ν) +
      (∫ x, ‖y x‖ ^ 2 * ‖radiationGraphInclusion (q x)‖ ^ 2 ∂ν) := by
  have hr : MemLp (fun x => radiationGraphDerivative (q x)) 2 ν :=
    radiationGraphDerivative.comp_memLp' hq
  have hrad : Integrable (fun x => ‖radiationGraphDerivative (q x)‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm hr.aestronglyMeasurable).mp hr
  have hc := weightedField_integrable y q hy hq hpol
  calc |∫ x, weightedField (y x) (q x) ∂ν|
      ≤ ∫ x, |weightedField (y x) (q x)| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ x, ‖radiationGraphDerivative (q x)‖ ^ 2 +
        ‖y x‖ ^ 2 * ‖radiationGraphInclusion (q x)‖ ^ 2 ∂ν :=
      integral_mono hc.abs (hrad.add hpol) (fun x => weightedField_abs_le_energy (y x) (q x))
    _ = _ := integral_add hrad hpol

include hy in
theorem weylWeightedGraph_integral_energy
    (hymeas : AEStronglyMeasurable y ν) (hq : MemLp q 2 ν)
    (hpol : Integrable (fun x => ‖y x‖ ^ 2 * ‖radiationGraphInclusion (q x)‖ ^ 2) ν) :
    (∫ x, ‖radiationGraphDerivative (weylWeightedGraph W (f x) (y x) (hy x) (q x))‖ ^ 2 ∂ν) =
      (∫ x, ‖radiationGraphDerivative (q x)‖ ^ 2 ∂ν) +
      (∫ x, weightedField (y x) (q x) ∂ν) +
      (∫ x, ‖y x‖ ^ 2 * ‖radiationGraphInclusion (q x)‖ ^ 2 ∂ν) := by
  have hr : MemLp (fun x => radiationGraphDerivative (q x)) 2 ν :=
    radiationGraphDerivative.comp_memLp' hq
  have hrad : Integrable (fun x => ‖radiationGraphDerivative (q x)‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm hr.aestronglyMeasurable).mp hr
  have hc := weightedField_integrable y q hymeas hq hpol
  simp_rw [weylWeightedGraph_derivative_norm_sq]
  have hsum : Integrable (fun x => ‖radiationGraphDerivative (q x)‖ ^ 2 + weightedField (y x) (q x)) ν :=
    hrad.add hc
  exact (integral_add hsum hpol).trans
    (congrArg (fun z : ℝ => z + ∫ x, ‖y x‖ ^ 2 * ‖radiationGraphInclusion (q x)‖ ^ 2 ∂ν)
      (integral_add hrad hc))

end Spatial

end GptLean.PhysicalWeyl
