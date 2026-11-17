import GptLean.PhysicalWeightedRadiation

/-! Appendix A radiation displacement on the full form domain.
The weighted annihilation map is constructed by the adjoint of the shell
tensor map. Only the square-root-frequency weight is required. The ordinary
Weyl law remains the existing universal operator background.
-/

noncomputable section
namespace GptLean.PhysicalWeyl

open MeasureTheory PhysicalFock Representability
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000

attribute [local irreducible] coefficientTensor radiationAnalysis weylWeightedGraph
  kernelAnnihilation

/-- Annihilation for a kernel specified only by its inverse-frequency part. -/
def weightedAnnihilation (y : Lp ℂ 2 photonMeasure) :
    RadiationGraphSpace →L[ℂ] PhotonFock :=
  (coefficientTensor (H := PhotonFock) y).adjoint.comp radiationAnalysis

theorem weightedAnnihilation_apply (y : Lp ℂ 2 photonMeasure) (q : RadiationGraphSpace) :
    weightedAnnihilation y q = (coefficientTensor (H := PhotonFock) y).adjoint (radiationAnalysis q) := rfl



theorem weightedAnnihilation_inner (y : Lp ℂ 2 photonMeasure)
    (q : RadiationGraphSpace) (u : PhotonFock) :
    ⟪weightedAnnihilation y q, u⟫_ℂ =
      ⟪radiationAnalysis q, coefficientTensor (H := PhotonFock) y u⟫_ℂ := by
  exact (coefficientTensor (H := PhotonFock) y).adjoint_inner_left u (radiationAnalysis q)

theorem weightedAnnihilation_norm_le (y : Lp ℂ 2 photonMeasure)
    (q : RadiationGraphSpace) :
    ‖weightedAnnihilation y q‖ ≤ ‖y‖ * ‖radiationGraphDerivative q‖ := by
  let a := weightedAnnihilation y q
  have h : ‖a‖ ^ 2 ≤ ‖radiationGraphDerivative q‖ * (‖y‖ * ‖a‖) := calc
    ‖a‖ ^ 2 = ‖⟪a, a⟫_ℂ‖ :=
      (inner_self_eq_norm_sq (𝕜 := ℂ) a).symm.trans (inner_self_re_eq_norm a)
    _ = ‖⟪radiationAnalysis q, coefficientTensor (H := PhotonFock) y a⟫_ℂ‖ :=
      congrArg norm (weightedAnnihilation_inner y q a)
    _ ≤ ‖radiationAnalysis q‖ * ‖coefficientTensor (H := PhotonFock) y a‖ :=
      norm_inner_le_norm _ _
    _ = _ := congrArg₂ (fun x z : ℝ => x * z)
      (radiationAnalysis_norm q) (coefficientTensor_norm y a)
  change ‖a‖ ≤ ‖y‖ * ‖radiationGraphDerivative q‖
  nlinarith only [h, norm_nonneg a,
    mul_nonneg (norm_nonneg y) (norm_nonneg (radiationGraphDerivative q))]

/-- Agreement with the ordinary annihilation operator whenever its kernel
also belongs to the one-photon Hilbert space. -/
theorem weightedAnnihilation_eq_kernel {f : Lp ℂ 2 photonMeasure}
    (K : WeightedPhotonKernel)
    (hK : ∀ᵐ p ∂photonMeasure, K.val.2 p = (Real.sqrt ‖p.1‖ : ℂ) * f p)
    (q : RadiationGraphSpace) :
    weightedAnnihilation K.val.2 q = kernelAnnihilation K q := by
  apply ext_inner_right ℂ
  intro u
  have hs := lp.hasSum_inner (𝕜 := ℂ) (radiationAnalysis q)
    (coefficientTensor (H := PhotonFock) K.val.2 u)
  have ht := cross_hasSum_vector (f := f) K hK q u
  apply (weightedAnnihilation_inner K.val.2 q u).trans
  apply hs.unique
  apply ht.congr_fun
  intro i
  exact (congrArg₂ (fun a b : PhotonFock => ⟪a, b⟫_ℂ)
    (radiationAnalysis_apply q i) (coefficientTensor_apply K.val.2 u i)).trans
    ((inner_smul_right _ _ _).trans
      (congrArg (fun c : ℂ => c * ⟪kernelAnnihilation (shellKernel i) q, u⟫_ℂ)
        (radiationFamily_inner (f := f) K hK i).symm))

/-- The polarized weighted field form. -/
def weightedFieldForm (y : Lp ℂ 2 photonMeasure) (q r : RadiationGraphSpace) : ℂ :=
  ⟪weightedAnnihilation y q, radiationGraphInclusion r⟫_ℂ +
    ⟪radiationGraphInclusion q, weightedAnnihilation y r⟫_ℂ



theorem weightedFieldForm_self (y : Lp ℂ 2 photonMeasure) (q : RadiationGraphSpace) :
    weightedFieldForm y q q = (weightedField y q : ℂ) := by
  unfold weightedFieldForm weightedField
  have halg {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (a b : H) :
      ⟪a, b⟫_ℂ + ⟪b, a⟫_ℂ = ((2 * (⟪a, b⟫_ℂ).re : ℝ) : ℂ) := by
    rw [← inner_conj_symm b a]
    apply Complex.ext <;> simp only [Complex.add_re, Complex.add_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im] <;> ring
  exact (halg (weightedAnnihilation y q) (radiationGraphInclusion q)).trans
    (congrArg (fun z : ℂ => ((2 * z.re : ℝ) : ℂ))
      (weightedAnnihilation_inner y q (radiationGraphInclusion q)))

theorem weightedFieldForm_conj (y : Lp ℂ 2 photonMeasure) (q r : RadiationGraphSpace) :
    star (weightedFieldForm y q r) = weightedFieldForm y r q := by
  unfold weightedFieldForm
  have halg {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (a b c d : H) :
      (starRingEnd ℂ) (⟪a, b⟫_ℂ + ⟪c, d⟫_ℂ) = ⟪d, c⟫_ℂ + ⟪b, a⟫_ℂ := by
    rw [map_add, inner_conj_symm, inner_conj_symm, add_comm]
  exact halg (weightedAnnihilation y q) (radiationGraphInclusion r)
    (radiationGraphInclusion q) (weightedAnnihilation y r)

private theorem coefficientTensor_inner (y : Lp ℂ 2 photonMeasure) (u v : PhotonFock) :
    ⟪coefficientTensor (H := PhotonFock) y u, coefficientTensor (H := PhotonFock) y v⟫_ℂ =
      (‖y‖ ^ 2 : ℂ) * ⟪u, v⟫_ℂ := by
  let L : PhotonFock →L[ℂ] PhotonFock := (‖y‖ : ℂ) • ContinuousLinearMap.id ℂ PhotonFock
  have h := inner_eq_of_map_norm_eq (coefficientTensor (H := PhotonFock) y) L
    (fun u => by simp only [L, smul_apply,
      ContinuousLinearMap.id_apply, coefficientTensor_norm, norm_smul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg y)]) u v
  simpa only [L, smul_apply, ContinuousLinearMap.id_apply,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal, pow_two, mul_assoc] using h

section Displacement

variable (W : ConcreteWeylLaw photonMeasure) (f y : Lp ℂ 2 photonMeasure)
  (hy : ∀ᵐ p ∂photonMeasure, y p = (Real.sqrt ‖p.1‖ : ℂ) * f p)

theorem kernelField_weylWeightedGraph (C : CanonicalSectorCCR photonMeasure)
    (k : WeightedPhotonKernel) (q : RadiationGraphSpace) :
    kernelField C k (weylWeightedGraph W f y hy q) = W.weyl f
      (kernelField C k q + ((2 * (⟪k.val.1, f⟫_ℂ).re : ℝ) : ℂ) • radiationGraphInclusion q) := by
  have h1 := kernelField_segalGraph C k (weylWeightedGraph W f y hy q)
  have h2 := W.field_shift f k.val.1 _ _ (kernelField_segalGraph C k q)
  apply lp.ext
  funext n
  exact (h1 n).trans ((congrArg (segalCoordinate photonMeasure k.val.1 n)
    (weylWeightedGraph_inclusion W f y hy q)).trans (h2 n).symm)

/-- The exact sesquilinear radiation shift at form regularity. -/
theorem weylWeightedGraph_form (q r : RadiationGraphSpace) :
    ⟪radiationGraphDerivative (weylWeightedGraph W f y hy q),
      radiationGraphDerivative (weylWeightedGraph W f y hy r)⟫_ℂ =
      ⟪radiationGraphDerivative q, radiationGraphDerivative r⟫_ℂ +
        weightedFieldForm y q r +
        (‖y‖ ^ 2 : ℂ) * ⟪radiationGraphInclusion q, radiationGraphInclusion r⟫_ℂ := by
  let L := radiationGraphDerivative.comp (weylWeightedGraph W f y hy)
  let K := radiationAnalysis + (coefficientTensor (H := PhotonFock) y).comp radiationGraphInclusion
  have hn (z : RadiationGraphSpace) : ‖L z‖ = ‖K z‖ := by
    apply (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
    change ‖radiationGraphDerivative (weylWeightedGraph W f y hy z)‖ ^ 2 =
      ‖radiationAnalysis z + coefficientTensor (H := PhotonFock) y (radiationGraphInclusion z)‖ ^ 2
    exact (weylWeightedGraph_derivative_norm_sq W f y hy z).trans
      ((coefficientTensor_add_norm_sq (radiationAnalysis z) y (radiationGraphInclusion z)).trans
        (congrArg (fun t : ℝ => t ^ 2 + weightedField y z +
          ‖y‖ ^ 2 * ‖radiationGraphInclusion z‖ ^ 2) (radiationAnalysis_norm z))).symm
  have h := inner_eq_of_map_norm_eq L K hn q r
  have hexpand {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (a b c d : H) :
      ⟪a + b, c + d⟫_ℂ = (⟪a, c⟫_ℂ + ⟪a, d⟫_ℂ) + (⟪b, c⟫_ℂ + ⟪b, d⟫_ℂ) := by
    rw [inner_add_left, inner_add_right, inner_add_right]
  have hc : ⟪coefficientTensor (H := PhotonFock) y (radiationGraphInclusion q), radiationAnalysis r⟫_ℂ =
      ⟪radiationGraphInclusion q, weightedAnnihilation y r⟫_ℂ :=
    (inner_conj_symm _ _).symm.trans
      ((congrArg (starRingEnd ℂ) (weightedAnnihilation_inner y r (radiationGraphInclusion q)).symm).trans
        (inner_conj_symm _ _))
  calc
    _ = ⟪K q, K r⟫_ℂ := h
    _ = (⟪radiationAnalysis q, radiationAnalysis r⟫_ℂ +
        ⟪radiationAnalysis q, coefficientTensor (H := PhotonFock) y (radiationGraphInclusion r)⟫_ℂ) +
        (⟪coefficientTensor (H := PhotonFock) y (radiationGraphInclusion q), radiationAnalysis r⟫_ℂ +
        ⟪coefficientTensor (H := PhotonFock) y (radiationGraphInclusion q),
          coefficientTensor (H := PhotonFock) y (radiationGraphInclusion r)⟫_ℂ) :=
      hexpand _ _ _ _
    _ = (⟪radiationGraphDerivative q, radiationGraphDerivative r⟫_ℂ +
        ⟪weightedAnnihilation y q, radiationGraphInclusion r⟫_ℂ) +
        (⟪radiationGraphInclusion q, weightedAnnihilation y r⟫_ℂ +
          (‖y‖ ^ 2 : ℂ) * ⟪radiationGraphInclusion q, radiationGraphInclusion r⟫_ℂ) :=
      congrArg₂ (fun a b : ℂ => a + b)
        (congrArg₂ (fun a b : ℂ => a + b) (radiationAnalysis_inner q r)
          (weightedAnnihilation_inner y q (radiationGraphInclusion r)).symm)
        (congrArg₂ (fun a b : ℂ => a + b) hc
          (coefficientTensor_inner y (radiationGraphInclusion q) (radiationGraphInclusion r)))
    _ = _ := by unfold weightedFieldForm; ring

include hy in
theorem weighted_relation_neg :
    ∀ᵐ p ∂photonMeasure, (-y) p = (Real.sqrt ‖p.1‖ : ℂ) * (-f) p := by
  filter_upwards [hy, Lp.coeFn_neg y, Lp.coeFn_neg f] with p hp hpy hpf
  simp only [hpy, hpf, Pi.neg_apply, hp, mul_neg]

theorem radiationGraphInclusion_injective_weyl : Function.Injective radiationGraphInclusion := by
  intro q r h
  have hz : (q - r).val.1 = 0 := sub_eq_zero.mpr h
  have ho := radiationRoot.graph_fst_eq_zero_snd (q - r).property hz
  exact Subtype.ext (Prod.ext h (sub_eq_zero.mp ho))

theorem weylWeightedGraph_surjective : Function.Surjective (weylWeightedGraph W f y hy) := by
  intro q
  refine ⟨weylWeightedGraph W (-f) (-y) (weighted_relation_neg f y hy) q, ?_⟩
  apply radiationGraphInclusion_injective_weyl
  rw [weylWeightedGraph_inclusion, weylWeightedGraph_inclusion]
  simpa only [neg_neg] using weyl_neg_apply W (-f) (radiationGraphInclusion q)

include hy in
/-- Equality of the complete radiation form domains under displacement. -/
theorem weyl_weighted_domain_iff (u : PhotonFock) :
    W.weyl f u ∈ radiationRoot.domain ↔ u ∈ radiationRoot.domain := by
  constructor
  · intro hu
    let q : RadiationGraphSpace :=
      ⟨(W.weyl f u, radiationRoot ⟨_, hu⟩), radiationRoot.mem_graph ⟨_, hu⟩⟩
    have h := weyl_weighted_mem_domain W (-f) (-y) (weighted_relation_neg f y hy) q
    change W.weyl (-f) (W.weyl f u) ∈ radiationRoot.domain at h
    rwa [weyl_neg_apply] at h
  · intro hu
    have h := weyl_weighted_mem_domain W f y hy
      ⟨(u, radiationRoot ⟨_, hu⟩), radiationRoot.mem_graph ⟨_, hu⟩⟩
    exact h

end Displacement

/-- Testing the vacuum proves the necessity of the one-photon energy condition. -/
theorem radiation_domain_preservation_necessary
    (W : ConcreteWeylLaw photonMeasure) (f : Lp ℂ 2 photonMeasure)
    (h : ∀ u, u ∈ radiationRoot.domain → W.weyl f u ∈ radiationRoot.domain) :
    onePhotonFamilyValue radiationFamily f < ⊤ := by
  have hv : creationWord photonMeasure [] ∈ radiationRoot.domain := by
    apply radiationRoot_domain_of_finite
    have h0 := W.coherent_radiation 0
    change radiationForm (W.weyl 0 (creationWord photonMeasure [])) = _ at h0
    rw [W.zero] at h0
    change radiationForm (creationWord photonMeasure []) = _ at h0
    rw [h0]
    simp [onePhotonFamilyValue]
  have hf := (radiationRoot_domain_iff_finite _).mp (h _ hv)
  change radiationForm (W.coherent photonMeasure f) < ⊤ at hf
  rwa [W.coherent_radiation] at hf

end GptLean.PhysicalWeyl
