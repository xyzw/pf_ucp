import GptLean.PhysicalWeylRadiation
import GptLean.PhysicalFockFieldSymmetry

/-!
Polarized radiation identities for the shell Parseval frame. These identities
allow a bounded field observable in the second vector of a radiation form.
-/

noncomputable section

namespace GptLean.PhysicalWeyl

open MeasureTheory Filter PhysicalFock Representability
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

def kernelAnnihilationHom (q : RadiationGraphSpace) : WeightedPhotonKernel →+ PhotonFock where
  toFun k := kernelAnnihilation k q
  map_zero' := by
    have h := congrArg (fun L => L q) (kernelAnnihilation_smul (0 : ℂ) (0 : WeightedPhotonKernel))
    simpa using h
  map_add' k l := by
    rw [kernelAnnihilation_add]
    rfl

/-- Vector-valued convergence requires only the inverse-frequency component. -/
theorem kernelAnnihilation_hasSum (q : RadiationGraphSpace) (K : WeightedPhotonKernel)
    (x : ℕ → WeightedPhotonKernel) (hx : HasSum (fun i => (x i).val.2) K.val.2) :
    HasSum (fun i => kernelAnnihilation (x i) q) (kernelAnnihilation K q) := by
  have hsum (s : Finset ℕ) : ∑ i ∈ s, kernelAnnihilation (x i) q =
      kernelAnnihilation (∑ i ∈ s, x i) q :=
    (map_sum (kernelAnnihilationHom q) x s).symm
  have hval (s : Finset ℕ) : (∑ i ∈ s, x i).val.2 = ∑ i ∈ s, (x i).val.2 := by
    rw [Submodule.coe_sum, Prod.snd_sum]
  unfold HasSum at hx ⊢
  rw [tendsto_iff_norm_sub_tendsto_zero] at hx ⊢
  have hB := hx.mul_const ‖radiationGraphDerivative q‖
  rw [zero_mul] at hB
  refine squeeze_zero (fun s => norm_nonneg _) (fun s => ?_) hB
  calc ‖∑ i ∈ s, kernelAnnihilation (x i) q - kernelAnnihilation K q‖
      = ‖kernelAnnihilation (∑ i ∈ s, x i - K) q‖ := by
        rw [hsum]
        exact congrArg norm (map_sub (kernelAnnihilationHom q) _ _).symm
    _ ≤ ‖(∑ i ∈ s, x i - K).val.2‖ * ‖radiationGraphDerivative q‖ :=
      kernelAnnihilation_norm_le _ q
    _ = _ := by rw [Submodule.coe_sub, Prod.snd_sub, hval]

/-- Shell reconstruction paired with an arbitrary photon vector. -/
theorem cross_hasSum_vector {f : Lp ℂ 2 photonMeasure} (K : WeightedPhotonKernel)
    (hK : ∀ᵐ p ∂photonMeasure, K.val.2 p = (Real.sqrt ‖p.1‖ : ℂ) * f p)
    (q : RadiationGraphSpace) (v : PhotonFock) :
    HasSum (fun i => ⟪radiationFamily i, f⟫_ℂ * ⟪kernelAnnihilation (shellKernel i) q, v⟫_ℂ)
      ⟪kernelAnnihilation K q, v⟫_ℂ := by
  have h : HasSum
      (fun i => star ⟪v, kernelAnnihilation
        (⟪sFamily i, K.val.2⟫_ℂ • shellKernel i) q⟫_ℂ)
      (star ⟪v, kernelAnnihilation K q⟫_ℂ) :=
    ((kernelAnnihilation_hasSum q K
      (fun i => ⟪sFamily i, K.val.2⟫_ℂ • shellKernel i)
      (sFamily_hasSum K.val.2)).mapL (innerSL ℂ v)).star
  have hl : star ⟪v, kernelAnnihilation K q⟫_ℂ = ⟪kernelAnnihilation K q, v⟫_ℂ :=
    inner_conj_symm _ _
  rw [hl] at h
  refine h.congr_fun fun i => ?_
  have ha := congrArg (fun L : RadiationGraphSpace →L[ℂ] PhotonFock => L q)
    (kernelAnnihilation_smul ⟪sFamily i, K.val.2⟫_ℂ (shellKernel i))
  change kernelAnnihilation (⟪sFamily i, K.val.2⟫_ℂ • shellKernel i) q =
    star ⟪sFamily i, K.val.2⟫_ℂ • kernelAnnihilation (shellKernel i) q at ha
  rw [ha, inner_smul_right, star_mul', radiationFamily_inner K hK]
  simp only [star_star]
  rw [show star ⟪v, kernelAnnihilation (shellKernel i) q⟫_ℂ =
    ⟪kernelAnnihilation (shellKernel i) q, v⟫_ℂ from inner_conj_symm _ _]

theorem shell_annihilation_hasSum (q : RadiationGraphSpace) :
    HasSum (fun i => ‖kernelAnnihilation (shellKernel i) q‖ ^ 2)
      (‖radiationGraphDerivative q‖ ^ 2) := by
  apply hasSum_of_ofReal (fun _ => sq_nonneg _) (sq_nonneg _)
  rw [← radiationGraph_energy, ← sum_annihilationForm_eq_radiationForm]
  exact tsum_congr fun i =>
    (AnnihilationGraph.form_eq photonMeasure (fun n => rfl)).symm

def radiationAnalysisVector (q : RadiationGraphSpace) : lp (fun _ : ℕ => PhotonFock) 2 :=
  ⟨fun i => kernelAnnihilation (shellKernel i) q, memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using (shell_annihilation_hasSum q).summable)⟩

theorem radiationAnalysisVector_norm (q : RadiationGraphSpace) :
    ‖radiationAnalysisVector q‖ = ‖radiationGraphDerivative q‖ := by
  have h := coordinate_mass_hasSum (fun _ : ℕ => PhotonFock) (radiationAnalysisVector q)
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
    (h.unique (shell_annihilation_hasSum q))

def radiationAnalysis : RadiationGraphSpace →L[ℂ] lp (fun _ : ℕ => PhotonFock) 2 :=
  LinearMap.mkContinuous
    { toFun := radiationAnalysisVector
      map_add' q r := by apply lp.ext; funext i; exact map_add _ q r
      map_smul' c q := by apply lp.ext; funext i; exact map_smul _ c q }
    ‖radiationGraphDerivative‖ (fun q =>
      (radiationAnalysisVector_norm q).trans_le (radiationGraphDerivative.le_opNorm q))

theorem radiationAnalysis_norm (q : RadiationGraphSpace) :
    ‖radiationAnalysis q‖ = ‖radiationGraphDerivative q‖ := radiationAnalysisVector_norm q

/-- Polarization for two linear maps having the same pointwise norms. -/
theorem inner_eq_of_map_norm_eq {E F H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (L : E →L[ℂ] F) (K : E →L[ℂ] H) (hn : ∀ z, ‖L z‖ = ‖K z‖) (q r : E) :
    ⟪L q, L r⟫_ℂ = ⟪K q, K r⟫_ℂ := by
  rw [inner_eq_sum_norm_sq_div_four (L q) (L r),
    inner_eq_sum_norm_sq_div_four (K q) (K r)]
  have h (z w : E) : ‖L z + L w‖ = ‖K z + K w‖ := by
    rw [← map_add, ← map_add, hn]
  have hs (z w : E) : ‖L z - L w‖ = ‖K z - K w‖ := by
    rw [← map_sub, ← map_sub, hn]
  rw [h, hs]
  have hi : L ((RCLike.I : ℂ) • r) = (RCLike.I : ℂ) • L r := map_smul _ _ _
  have hd : K ((RCLike.I : ℂ) • r) = (RCLike.I : ℂ) • K r := map_smul _ _ _
  rw [← hi, ← hd, hs, h]

theorem radiationAnalysis_inner (q r : RadiationGraphSpace) :
    ⟪radiationAnalysis q, radiationAnalysis r⟫_ℂ =
      ⟪radiationGraphDerivative q, radiationGraphDerivative r⟫_ℂ :=
  inner_eq_of_map_norm_eq radiationAnalysis radiationGraphDerivative radiationAnalysis_norm q r

/-- The radiation form as a convergent complex series of annihilation forms. -/
theorem radiation_inner_hasSum (q r : RadiationGraphSpace) :
    HasSum (fun i => ⟪kernelAnnihilation (shellKernel i) q,
      kernelAnnihilation (shellKernel i) r⟫_ℂ)
      ⟪radiationGraphDerivative q, radiationGraphDerivative r⟫_ℂ := by
  rw [← radiationAnalysis_inner]
  exact lp.hasSum_inner (𝕜 := ℂ) (radiationAnalysis q) (radiationAnalysis r)

theorem im_inner_selfadjoint_sum {E J : Type*} [Fintype J]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) (v : E) (c : J → ℂ) (w : J → E) :
    (⟪v, A v + ∑ j, c j • w j⟫_ℂ).im = (∑ j, c j * ⟪v, w j⟫_ℂ).im := by
  have hz : (⟪v, A v⟫_ℂ).im = 0 := hA.isSymmetric.im_inner_self_apply v
  rw [inner_add_right, Complex.add_im, hz, zero_add, inner_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => inner_smul_right _ _ _

/-- The imaginary radiation form is fixed by the annihilation commutators. -/
theorem radiation_im_of_commutator {J : Type*} [Fintype J]
    (A : PhotonFock →L[ℂ] PhotonFock) (hA : IsSelfAdjoint A)
    (D : J → PhotonFock →L[ℂ] PhotonFock)
    (g : J → Lp ℂ 2 photonMeasure) (K : J → WeightedPhotonKernel)
    (hK : ∀ j, ∀ᵐ p ∂photonMeasure, (K j).val.2 p = (Real.sqrt ‖p.1‖ : ℂ) * g j p)
    (q r : RadiationGraphSpace)
    (hcomm : ∀ k : WeightedPhotonKernel,
      kernelAnnihilation k r = A (kernelAnnihilation k q) +
        ∑ j, ⟪k.val.1, g j⟫_ℂ • D j (radiationGraphInclusion q)) :
    (⟪radiationGraphDerivative q, radiationGraphDerivative r⟫_ℂ).im =
      ∑ j, (⟪kernelAnnihilation (K j) q, D j (radiationGraphInclusion q)⟫_ℂ).im := by
  have h₁ := Complex.hasSum_im (radiation_inner_hasSum q r)
  have h₂ := Complex.hasSum_im (hasSum_sum (s := Finset.univ)
    (fun j _ => cross_hasSum_vector (K j) (hK j) q (D j (radiationGraphInclusion q))))
  have hpt (i : ℕ) :
      (⟪kernelAnnihilation (shellKernel i) q, kernelAnnihilation (shellKernel i) r⟫_ℂ).im =
        (∑ j, ⟪radiationFamily i, g j⟫_ℂ *
          ⟪kernelAnnihilation (shellKernel i) q, D j (radiationGraphInclusion q)⟫_ℂ).im :=
    (congrArg (fun w : PhotonFock => (⟪kernelAnnihilation (shellKernel i) q, w⟫_ℂ).im)
      (hcomm (shellKernel i))).trans
        (im_inner_selfadjoint_sum A hA (kernelAnnihilation (shellKernel i) q)
          (fun j => ⟪radiationFamily i, g j⟫_ℂ) (fun j => D j (radiationGraphInclusion q)))
  exact h₁.unique (h₂.congr_fun hpt) |>.trans (map_sum Complex.imAddGroupHom _ _)

theorem electric_scalar_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (u v w z : E) :
    (⟪u, Complex.I • v⟫_ℂ).re + (⟪Complex.I • w, z⟫_ℂ).re =
      -(⟪u, v⟫_ℂ).im + (⟪w, z⟫_ℂ).im := by
  simp [inner_smul_right, inner_smul_left, Complex.mul_re]

/-- Pairing the electric Segal field uses annihilation on both graph vectors. -/
theorem electric_pair (C : CanonicalSectorCCR photonMeasure) (K : WeightedPhotonKernel)
    (q r : RadiationGraphSpace) :
    (⟪radiationGraphInclusion r, kernelField C ((-Complex.I) • K) q⟫_ℂ).re =
      -(⟪radiationGraphInclusion r, kernelAnnihilation K q⟫_ℂ).im +
        (⟪kernelAnnihilation K r, radiationGraphInclusion q⟫_ℂ).im := by
  have ha (v : RadiationGraphSpace) : kernelAnnihilation ((-Complex.I) • K) v =
      Complex.I • kernelAnnihilation K v := by
    have h := congrArg (fun L : RadiationGraphSpace →L[ℂ] PhotonFock => L v)
      (kernelAnnihilation_smul (-Complex.I) K)
    simpa only [smul_apply, map_neg, Complex.conj_I, neg_neg] using h
  calc
    (⟪radiationGraphInclusion r, kernelField C ((-Complex.I) • K) q⟫_ℂ).re
      = (⟪radiationGraphInclusion r, kernelAnnihilation ((-Complex.I) • K) q⟫_ℂ).re +
          (⟪radiationGraphInclusion r, kernelCreation C ((-Complex.I) • K) q⟫_ℂ).re :=
        (congrArg Complex.re (inner_add_right (radiationGraphInclusion r)
          (kernelAnnihilation ((-Complex.I) • K) q)
          (kernelCreation C ((-Complex.I) • K) q))).trans (Complex.add_re _ _)
    _ = (⟪radiationGraphInclusion r, kernelAnnihilation ((-Complex.I) • K) q⟫_ℂ).re +
          (⟪kernelAnnihilation ((-Complex.I) • K) r, radiationGraphInclusion q⟫_ℂ).re :=
        congrArg (fun z : ℂ =>
          (⟪radiationGraphInclusion r, kernelAnnihilation ((-Complex.I) • K) q⟫_ℂ).re + z.re)
          (kernelAnnihilation_creation_duality C ((-Complex.I) • K) r q).symm
    _ = (⟪radiationGraphInclusion r, Complex.I • kernelAnnihilation K q⟫_ℂ).re +
          (⟪Complex.I • kernelAnnihilation K r, radiationGraphInclusion q⟫_ℂ).re :=
        congrArg₂ (fun v w : PhotonFock =>
          (⟪radiationGraphInclusion r, v⟫_ℂ).re + (⟪w, radiationGraphInclusion q⟫_ℂ).re)
          (ha q) (ha r)
    _ = _ := electric_scalar_pair _ _ _ _

theorem electric_commutator_algebra {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (D H : E →L[ℂ] E) (hD : IsSelfAdjoint D) (hH : IsSelfAdjoint H) (u v : E) :
    -(⟪D u, v⟫_ℂ).im + (⟪D v + H u, u⟫_ℂ).im = 2 * (⟪v, D u⟫_ℂ).im := by
  have hsym (x y : E) : ⟪D x, y⟫_ℂ = ⟪x, D y⟫_ℂ := hD.isSymmetric x y
  have him : (⟪H u, u⟫_ℂ).im = 0 := hH.isSymmetric.im_inner_apply_self u
  have hc : (⟪D u, v⟫_ℂ).im = -(⟪v, D u⟫_ℂ).im := by
    simpa only [Complex.conj_im] using
      (congrArg Complex.im (inner_conj_symm (D u) v)).symm
  rw [inner_add_left, Complex.add_im, him, add_zero, hsym v u, hc]
  ring

/-- A self-adjoint annihilation commutator contributes no electric trace. -/
theorem electric_pair_of_commutator
    (C : CanonicalSectorCCR photonMeasure) (K : WeightedPhotonKernel)
    (D H : PhotonFock →L[ℂ] PhotonFock) (hD : IsSelfAdjoint D) (hH : IsSelfAdjoint H)
    (q r : RadiationGraphSpace)
    (hr : radiationGraphInclusion r = D (radiationGraphInclusion q))
    (hcomm : kernelAnnihilation K r = D (kernelAnnihilation K q) + H (radiationGraphInclusion q)) :
    (⟪radiationGraphInclusion q, D (kernelField C ((-Complex.I) • K) q)⟫_ℂ).re =
      2 * (⟪kernelAnnihilation K q, D (radiationGraphInclusion q)⟫_ℂ).im := by
  have hsym : ⟪radiationGraphInclusion q, D (kernelField C ((-Complex.I) • K) q)⟫_ℂ =
      ⟪D (radiationGraphInclusion q), kernelField C ((-Complex.I) • K) q⟫_ℂ :=
    (hD.isSymmetric _ _).symm
  calc
    (⟪radiationGraphInclusion q, D (kernelField C ((-Complex.I) • K) q)⟫_ℂ).re
      = (⟪radiationGraphInclusion r, kernelField C ((-Complex.I) • K) q⟫_ℂ).re :=
        congrArg Complex.re (hsym.trans (congrArg
          (fun v : PhotonFock => ⟪v, kernelField C ((-Complex.I) • K) q⟫_ℂ) hr.symm))
    _ = -(⟪radiationGraphInclusion r, kernelAnnihilation K q⟫_ℂ).im +
          (⟪kernelAnnihilation K r, radiationGraphInclusion q⟫_ℂ).im := electric_pair C K q r
    _ = -(⟪D (radiationGraphInclusion q), kernelAnnihilation K q⟫_ℂ).im +
          (⟪D (kernelAnnihilation K q) + H (radiationGraphInclusion q), radiationGraphInclusion q⟫_ℂ).im :=
        congrArg₂ (fun v w : PhotonFock => -(⟪v, kernelAnnihilation K q⟫_ℂ).im +
          (⟪w, radiationGraphInclusion q⟫_ℂ).im) hr hcomm
    _ = _ := electric_commutator_algebra D H hD hH _ _

/-- The nonlinear electric statistic is twice the imaginary radiation form. -/
theorem electric_statistics_eq_radiation {J : Type*} [Fintype J]
    (C : CanonicalSectorCCR photonMeasure)
    (A : PhotonFock →L[ℂ] PhotonFock) (hA : IsSelfAdjoint A)
    (D H : J → PhotonFock →L[ℂ] PhotonFock)
    (hD : ∀ j, IsSelfAdjoint (D j)) (hH : ∀ j, IsSelfAdjoint (H j))
    (g : J → Lp ℂ 2 photonMeasure) (K : J → WeightedPhotonKernel)
    (hK : ∀ j, ∀ᵐ p ∂photonMeasure, (K j).val.2 p = (Real.sqrt ‖p.1‖ : ℂ) * g j p)
    (q r : RadiationGraphSpace) (s : J → RadiationGraphSpace)
    (hs : ∀ j, radiationGraphInclusion (s j) = D j (radiationGraphInclusion q))
    (hcomm : ∀ k : WeightedPhotonKernel,
      kernelAnnihilation k r = A (kernelAnnihilation k q) +
        ∑ j, ⟪k.val.1, g j⟫_ℂ • D j (radiationGraphInclusion q))
    (hcommD : ∀ j, kernelAnnihilation (K j) (s j) =
      D j (kernelAnnihilation (K j) q) + H j (radiationGraphInclusion q)) :
    (∑ j, (⟪radiationGraphInclusion q,
      D j (kernelField C ((-Complex.I) • K j) q)⟫_ℂ).re) =
      2 * (⟪radiationGraphDerivative q, radiationGraphDerivative r⟫_ℂ).im := by
  calc
    (∑ j, (⟪radiationGraphInclusion q,
        D j (kernelField C ((-Complex.I) • K j) q)⟫_ℂ).re)
      = ∑ j, 2 * (⟪kernelAnnihilation (K j) q, D j (radiationGraphInclusion q)⟫_ℂ).im :=
        Finset.sum_congr rfl fun j _ =>
          electric_pair_of_commutator C (K j) (D j) (H j) (hD j) (hH j) q (s j) (hs j) (hcommD j)
    _ = 2 * ∑ j, (⟪kernelAnnihilation (K j) q, D j (radiationGraphInclusion q)⟫_ℂ).im :=
      (Finset.mul_sum ..).symm
    _ = _ := congrArg (fun x : ℝ => 2 * x)
      (radiation_im_of_commutator A hA D g K hK q r hcomm).symm

end GptLean.PhysicalWeyl
