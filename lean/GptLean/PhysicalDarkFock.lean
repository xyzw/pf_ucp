import GptLean.PhysicalFockSoftRadiationBound
import GptLean.PhysicalFockHardRadiationBound
import GptLean.PhysicalFockChannelVacuum

/-!
Dark photon modes on the photon Fock space (`prop-optimizer-symmetry` (ii)).

Fix a measurable set `D` of photon modes. The split `MomentumSplit.split D`
keeps the modes in `D`, and the split of `Dᶜ` keeps the bright modes off `D`.
Their Kraus coordinates `K_a` (the bright ones) and `K'_a` (the dark ones)
partition the radiation energy:

* `∑_a R(K'_a u) + ∑_a R(K_a u) = R(u)`. The first sum is the radiation energy
  of the dark factor, `darkRadiation u`.
* Each `K_a` maps the radiation graph into itself with norm at most one.
* For a kernel `k` supported off `D`, `φ(k) K_a u = K_a φ(k) u`: the field of a
  bright kernel commutes with the bright Kraus coordinates.
* If `darkRadiation u = 0`, then `u` has no dark photons: in every sector
  `u_n(k₁, …, k_n) = 0` for almost every `k` with some `kᵢ ∈ D`.

The last item uses the bounded weight `w = 1_D min(ω, 1)`, which is positive on
`D` because the dispersion `ω(k) = |k|` is positive almost everywhere.
-/

noncomputable section

namespace GptLean.PhysicalFock.DarkModes

open MeasureTheory PhysicalL2HilbertSum PhotonLocalizationFormBounds PhotonLocalizationChannel
  PhysicalNormalTrace PhotonLocalizationFockChannel
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

variable {D : Set PhotonMode} (hD : MeasurableSet D)

/-! ### A bounded weight that detects dark photons -/

/-- `min(ω, 1)` on the dark modes and zero elsewhere. -/
def weight (D : Set PhotonMode) (p : PhotonMode) : ℝ :=
  D.indicator (fun p => min (NormalPhoton.frequency p) 1) p

include hD in
theorem weight_measurable : Measurable (weight D) :=
  (NormalPhoton.frequency_measurable.min measurable_const).indicator hD

theorem weight_nonneg (p : PhotonMode) : 0 ≤ weight D p := by
  classical
  unfold weight
  by_cases hp : p ∈ D
  · rw [Set.indicator_of_mem hp]
    exact le_min (norm_nonneg p.1) zero_le_one
  · rw [Set.indicator_of_notMem hp]

theorem weight_le_one (p : PhotonMode) : weight D p ≤ 1 := by
  classical
  unfold weight
  by_cases hp : p ∈ D
  · rw [Set.indicator_of_mem hp]
    exact min_le_right _ _
  · rw [Set.indicator_of_notMem hp]
    exact zero_le_one

/-- Multiplication by `√w` on the one-photon space. -/
def weightRoot : Lp ℂ 2 photonMeasure →L[ℂ] Lp ℂ 2 photonMeasure :=
  PhotonLocalization.realL2Multiplier (fun p => Real.sqrt (weight D p))
    (weight_measurable hD).sqrt.aestronglyMeasurable (Real.sqrt 1)
    (ae_of_all _ fun p => by
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_sqrt (weight_le_one p))

theorem weightRoot_ae (v : Lp ℂ 2 photonMeasure) :
    weightRoot hD v =ᵐ[photonMeasure] fun p => Real.sqrt (weight D p) • v p :=
  PhotonLocalization.realL2Multiplier_apply _ _ _ _ v

theorem weightRoot_norm_integral (v : Lp ℂ 2 photonMeasure) :
    ENNReal.ofReal (‖weightRoot hD v‖ ^ 2) =
      ∫⁻ p, ENNReal.ofReal (weight D p) * ENNReal.ofReal (‖v p‖ ^ 2) ∂photonMeasure := by
  rw [PhotonKernelLocalization.l2_norm_sq_eq_integral,
    ofReal_integral_eq_lintegral_ofReal
      ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _))
      (ae_of_all _ fun p => sq_nonneg _)]
  apply lintegral_congr_ae
  filter_upwards [weightRoot_ae hD v] with p hp
  rw [hp, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, Real.sq_sqrt (weight_nonneg p), ENNReal.ofReal_mul (weight_nonneg p)]

/-- The weighted dark energy is at most the radiation energy of the dark part. -/
theorem weightRoot_le_radiation (v : Lp ℂ 2 photonMeasure) :
    ENNReal.ofReal (‖weightRoot hD v‖ ^ 2) ≤
      onePhotonFamilyValue radiationFamily (MomentumSplit.projection photonMeasure D hD v) := by
  rw [radiationFamily_value, weightRoot_norm_integral]
  apply lintegral_mono_ae
  filter_upwards [MomentumSplit.projection_ae photonMeasure D hD v] with p hp
  rw [hp]
  classical
  by_cases hm : p ∈ D
  · simp only [weight, Set.indicator_of_mem hm]
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (min_le_left _ _)) _
  · simp only [weight, Set.indicator_of_notMem hm, ENNReal.ofReal_zero, zero_mul]
    exact zero_le

/-- Multiplication by `√w` of the head photon on a sector. -/
def headWeightRoot (n : ℕ) :
    FullSector photonMeasure (n + 1) →L[ℂ] FullSector photonMeasure (n + 1) :=
  PhotonLocalization.realL2Multiplier (fun k => Real.sqrt (weight D (k 0)))
    ((weight_measurable hD).comp (measurable_pi_apply 0)).sqrt.aestronglyMeasurable
    (Real.sqrt 1) (ae_of_all _ fun k => by
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_sqrt (weight_le_one (k 0)))

theorem headWeightRoot_ae (n : ℕ) (u : FullSector photonMeasure (n + 1)) :
    headWeightRoot hD n u =ᵐ[SectorMeasure photonMeasure (n + 1)]
      fun k => Real.sqrt (weight D (k 0)) • u k :=
  PhotonLocalization.realL2Multiplier_apply _ _ _ _ u

theorem headWeightRoot_sections (n : ℕ) (u : FullSector photonMeasure (n + 1)) :
    onePhotonSections n (headWeightRoot hD n u) =
      (weightRoot hD).compLpL 2 (SectorMeasure photonMeasure n) (onePhotonSections n u) := by
  let P : FullSector photonMeasure (n + 1) →ₗᵢ[ℂ]
      Lp ℂ 2 ((SectorMeasure photonMeasure n).prod photonMeasure) :=
    Lp.compMeasurePreservingₗᵢ ℂ (tailHeadCoordinates n) (tailHeadCoordinates_measurePreserving n)
  have hp : P (headWeightRoot hD n u) =ᵐ[(SectorMeasure photonMeasure n).prod photonMeasure]
      fun z => Real.sqrt (weight D z.2) • P u z := by
    filter_upwards [Lp.coeFn_compMeasurePreserving (headWeightRoot hD n u)
      (tailHeadCoordinates_measurePreserving n),
      Lp.coeFn_compMeasurePreserving u (tailHeadCoordinates_measurePreserving n),
      (tailHeadCoordinates_measurePreserving n).quasiMeasurePreserving.ae
        (headWeightRoot_ae hD n u)] with z hv hu ht
    have hhead : (tailHeadCoordinates n z) 0 = z.2 := by
      simp [tailHeadCoordinates, MeasurableEquiv.prodComm,
        MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    exact hv.trans (ht.trans ((congrArg (fun p : PhotonMode =>
      Real.sqrt (weight D p) • u (tailHeadCoordinates n z)) hhead).trans
      (congrArg (Real.sqrt (weight D z.2) • ·) hu.symm)))
  have hcV := PhysicalSourceFubini.curryEquiv_represents_ae (P (headWeightRoot hD n u))
  have hcU := PhysicalSourceFubini.curryEquiv_represents_ae (P u)
  have hcB := (weightRoot hD).coeFn_compLpL (onePhotonSections n u)
  apply Lp.ext
  filter_upwards [hcV, hcU, Measure.ae_ae_of_ae_prod hp, hcB] with x hv hu ht hb
  change PhysicalSourceFubini.curryEquiv (P (headWeightRoot hD n u)) x = _
  rw [hb]
  apply Lp.ext
  filter_upwards [hv, hu, ht, weightRoot_ae hD (onePhotonSections n u x)]
    with p hV hU hT hB
  exact hV.trans (hT.trans ((congrArg (Real.sqrt (weight D p) • ·) hU.symm).trans hB.symm))

theorem onePhotonSlices_weightRoot_norm_sum (n : ℕ) (u : Sector photonMeasure (n + 1)) :
    (∑' a, ENNReal.ofReal (‖weightRoot hD (onePhotonSlices n u a)‖ ^ 2)) =
      ENNReal.ofReal (‖headWeightRoot hD n u.val‖ ^ 2) := by
  let W := spatialCoefficients (SectorMeasure photonMeasure n) (Lp ℂ 2 photonMeasure)
  let v := (weightRoot hD).compLpL 2 (SectorMeasure photonMeasure n) (onePhotonSections n u.val)
  have hcoord (a : ℕ) : W v a = weightRoot hD (onePhotonSlices n u a) :=
    spatialCoefficients_compLpL (SectorMeasure photonMeasure n) (Lp ℂ 2 photonMeasure)
      (weightRoot hD) (onePhotonSections n u.val) a
  have hs := coordinate_mass_hasSum (fun _ : ℕ => Lp ℂ 2 photonMeasure) (W v)
  have hn : ‖W v‖ = ‖headWeightRoot hD n u.val‖ :=
    (W.norm_map v).trans ((congrArg norm (headWeightRoot_sections hD n u.val).symm).trans
      ((onePhotonSections n).norm_map (headWeightRoot hD n u.val)))
  calc
    _ = ∑' a, ENNReal.ofReal (‖W v a‖ ^ 2) :=
      tsum_congr fun a => congrArg (fun t : Lp ℂ 2 photonMeasure => ENNReal.ofReal (‖t‖ ^ 2))
        (hcoord a).symm
    _ = ENNReal.ofReal (‖W v‖ ^ 2) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun a => sq_nonneg _) hs.summable).symm.trans
        (congrArg ENNReal.ofReal hs.tsum_eq)
    _ = _ := congrArg (fun t : ℝ => ENNReal.ofReal (t ^ 2)) hn

theorem headWeightRoot_norm_moment (n : ℕ) (u : Sector photonMeasure (n + 1)) :
    ENNReal.ofReal (‖headWeightRoot hD n u.val‖ ^ 2) =
      coordinatePhotonMoment (fun p => ENNReal.ofReal (weight D p)) (0 : Fin (n + 1)) u := by
  rw [PhotonKernelLocalization.l2_norm_sq_eq_integral,
    ofReal_integral_eq_lintegral_ofReal
      ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _))
      (ae_of_all _ fun k => sq_nonneg _)]
  unfold coordinatePhotonMoment
  apply lintegral_congr_ae
  filter_upwards [headWeightRoot_ae hD n u.val] with k hk
  rw [hk, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, Real.sq_sqrt (weight_nonneg (k 0)), ENNReal.ofReal_mul (weight_nonneg (k 0))]

/-- The weighted photon moment is at most the slice form of the dark radiation. -/
theorem moment_le_fockForm (u : PhotonFock) :
    photonMoment (fun p => ENNReal.ofReal (weight D p)) u ≤
      fockForm (fun v => onePhotonFamilyValue radiationFamily
        (MomentumSplit.projection photonMeasure D hD v)) (fockSlices u) := by
  unfold fockForm photonMoment
  apply ENNReal.tsum_le_tsum
  intro n
  cases n with
  | zero => simp [sectorPhotonMoment]
  | succ n =>
    have hsec : sectorForm (fun v => onePhotonFamilyValue radiationFamily
        (MomentumSplit.projection photonMeasure D hD v)) (fockSlices u (n + 1)) =
        ((n + 1 : ℕ) : ℝ≥0∞) * ∑' a, onePhotonFamilyValue radiationFamily
          (MomentumSplit.projection photonMeasure D hD (onePhotonSlices n (u (n + 1)) a)) := by
      simp only [sectorForm, fockSlices, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    calc sectorPhotonMoment (fun p => ENNReal.ofReal (weight D p)) (n + 1) (u (n + 1))
        = ((n + 1 : ℕ) : ℝ≥0∞) *
            coordinatePhotonMoment (fun p => ENNReal.ofReal (weight D p)) (0 : Fin (n + 1))
              (u (n + 1)) :=
          sectorPhotonMoment_eq_coordinate _ (weight_measurable hD).ennreal_ofReal
            (0 : Fin (n + 1)) (u (n + 1))
      _ = ((n + 1 : ℕ) : ℝ≥0∞) *
            ∑' a, ENNReal.ofReal (‖weightRoot hD (onePhotonSlices n (u (n + 1)) a)‖ ^ 2) :=
          congrArg (fun t => ((n + 1 : ℕ) : ℝ≥0∞) * t)
            ((headWeightRoot_norm_moment hD n (u (n + 1))).symm.trans
              (onePhotonSlices_weightRoot_norm_sum hD n (u (n + 1))).symm)
      _ ≤ ((n + 1 : ℕ) : ℝ≥0∞) * ∑' a, onePhotonFamilyValue radiationFamily
            (MomentumSplit.projection photonMeasure D hD (onePhotonSlices n (u (n + 1)) a)) :=
          mul_le_mul_right (ENNReal.tsum_le_tsum fun a => weightRoot_le_radiation hD _) _
      _ = _ := hsec.symm

/-- A Fock vector without photons in `D`. -/
def DarkVacuum (D : Set PhotonMode) (u : PhotonFock) : Prop :=
  ∀ n, ∀ᵐ k ∂SectorMeasure photonMeasure n, (u n).val k ≠ 0 → ∀ i, k i ∉ D

include hD in
/-- **Zero weighted moment forces the dark vacuum.** -/
theorem darkVacuum_of_moment (u : PhotonFock)
    (h : photonMoment (fun p => ENNReal.ofReal (weight D p)) u = 0) : DarkVacuum D u := by
  intro n
  have hn : sectorPhotonMoment (fun p => ENNReal.ofReal (weight D p)) n (u n) = 0 :=
    ENNReal.tsum_eq_zero.mp h n
  unfold sectorPhotonMoment at hn
  have hmeas : AEMeasurable (fun k : Fin n → PhotonMode =>
      (∑ i, ENNReal.ofReal (weight D (k i))) * ENNReal.ofReal (‖(u n).val k‖ ^ 2))
      (SectorMeasure photonMeasure n) :=
    (Finset.measurable_sum _ fun i _ =>
      (weight_measurable hD).ennreal_ofReal.comp (measurable_pi_apply i)).aemeasurable.mul
      ((Lp.stronglyMeasurable (u n).val).measurable.norm.pow_const 2).ennreal_ofReal.aemeasurable
  have hz := (lintegral_eq_zero_iff' hmeas).mp hn
  have hpos : ∀ᵐ k ∂SectorMeasure photonMeasure n, ∀ i, 0 < NormalPhoton.frequency (k i) :=
    ae_all_iff.mpr fun i => (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => photonMeasure)
      (i := i)).eventually (p := fun p => 0 < NormalPhoton.frequency p)
      NormalPhoton.frequency_positive
  filter_upwards [hz, hpos] with k hk hk' hne i hi
  have hpos2 : ENNReal.ofReal (‖(u n).val k‖ ^ 2) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact pow_pos (norm_pos_iff.mpr hne) 2
  have hsum : ∑ i, ENNReal.ofReal (weight D (k i)) = 0 :=
    (mul_eq_zero.mp hk).resolve_right hpos2
  have h0 : ENNReal.ofReal (weight D (k i)) = 0 :=
    (Finset.sum_eq_zero_iff.mp hsum) i (Finset.mem_univ i)
  rw [ENNReal.ofReal_eq_zero, weight, Set.indicator_of_mem hi] at h0
  exact absurd h0 (not_le.mpr (lt_min (hk' i) zero_lt_one))

/-! ### The bright and dark Kraus coordinates -/

/-- The split keeping the bright modes off `D`. -/
abbrev brightSplit : Lp ℂ 2 photonMeasure →ₗᵢ[ℂ]
    WithLp 2 (Lp ℂ 2 photonMeasure × Lp ℂ 2 photonMeasure) :=
  MomentumSplit.split photonMeasure Dᶜ hD.compl

variable (BF : StandardSymmetricFockExponential)

/-- The radiation energy of the dark factor. -/
def darkRadiation (u : PhotonFock) : ℝ≥0∞ :=
  ∑' a, radiationForm ((photonFactorization BF).factor (MomentumSplit.split photonMeasure D hD) u a)

/-- The bright Kraus coordinate `K_a` on the photon Fock space. -/
def krausFock (a : ℕ) : PhotonFock →L[ℂ] PhotonFock :=
  (lp.evalCLM ℂ (fun _ : ℕ => PhotonFock) 2 a).comp
    ((photonFactorization BF).factor (brightSplit hD)).toContinuousLinearMap

theorem krausFock_apply (a : ℕ) (u : PhotonFock) :
    krausFock hD BF a u = (photonFactorization BF).factor (brightSplit hD) u a := rfl

/-- Parseval for the bright Kraus coordinates. -/
theorem krausFock_mass (u : PhotonFock) :
    HasSum (fun a => ‖krausFock hD BF a u‖ ^ 2) (‖u‖ ^ 2) :=
  kraus_mass ((photonFactorization BF).factor (brightSplit hD)) u

section Normal

variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : Gaussian.RankOneData PhotonFock T}
  (normal : NormalTraceData R) (F : NormalFunctionalData R) (C : CanonicalSectorCCR photonMeasure)

include normal F C in
/-- **The bright and dark factors partition the radiation energy.** -/
theorem radiation_partition (u : PhotonFock) :
    darkRadiation hD BF u + ∑' a, radiationForm (krausFock hD BF a u) = radiationForm u :=
  split_radiation_partition normal F BF C D hD u

include normal F C in
/-- Zero dark radiation energy forces the dark vacuum. -/
theorem darkVacuum_of_darkRadiation (u : PhotonFock) (h : darkRadiation hD BF u = 0) :
    DarkVacuum D u := by
  have hp := familyObservable_pullback normal F BF C
    (MomentumSplit.split photonMeasure D hD) radiationFamily u
  simp only [radiationObservable_rankOne, MomentumSplit.retained_split] at hp
  apply darkVacuum_of_moment hD u
  apply le_antisymm _ zero_le
  exact ((moment_le_fockForm hD u).trans_eq hp.symm).trans_eq h

include normal F C in
theorem radiationForm_kraus_le (a : ℕ) (u : PhotonFock) :
    radiationForm (krausFock hD BF a u) ≤ radiationForm u :=
  (ENNReal.le_tsum a).trans (le_add_self.trans_eq (radiation_partition hD BF normal F C u))

include normal F C in
theorem kraus_mem_domain (a : ℕ) (q : RadiationGraphSpace) :
    krausFock hD BF a (radiationGraphInclusion q) ∈ radiationRoot.domain :=
  (radiationRoot_domain_iff_finite _).mpr
    (((radiationForm_kraus_le hD BF normal F C a _).trans_eq
      (radiationGraph_energy q)).trans_lt ENNReal.ofReal_lt_top)

/-- The bright Kraus coordinate of a radiation graph element. -/
def krausGraphFun (a : ℕ) (q : RadiationGraphSpace) : RadiationGraphSpace :=
  ⟨(krausFock hD BF a (radiationGraphInclusion q),
      radiationRoot ⟨_, kraus_mem_domain hD BF normal F C a q⟩),
    radiationRoot.mem_graph ⟨_, kraus_mem_domain hD BF normal F C a q⟩⟩

theorem krausGraphFun_derivative_energy (a : ℕ) (q : RadiationGraphSpace) :
    ENNReal.ofReal (‖radiationGraphDerivative (krausGraphFun hD BF normal F C a q)‖ ^ 2) =
      radiationForm (krausFock hD BF a (radiationGraphInclusion q)) :=
  (radiationRoot_energy ⟨_, kraus_mem_domain hD BF normal F C a q⟩).symm

theorem krausGraphFun_derivative_le (a : ℕ) (q : RadiationGraphSpace) :
    ‖radiationGraphDerivative (krausGraphFun hD BF normal F C a q)‖ ≤
      ‖radiationGraphDerivative q‖ := by
  have h : ENNReal.ofReal (‖radiationGraphDerivative (krausGraphFun hD BF normal F C a q)‖ ^ 2) ≤
      ENNReal.ofReal (‖radiationGraphDerivative q‖ ^ 2) :=
    ((krausGraphFun_derivative_energy hD BF normal F C a q).trans_le
      (radiationForm_kraus_le hD BF normal F C a _)).trans_eq (radiationGraph_energy q)
  have hsq := (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).mp h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

theorem krausGraphFun_add (a : ℕ) (q r : RadiationGraphSpace) :
    krausGraphFun hD BF normal F C a (q + r) =
      krausGraphFun hD BF normal F C a q + krausGraphFun hD BF normal F C a r := by
  have hx : krausFock hD BF a (radiationGraphInclusion (q + r)) =
      krausFock hD BF a (radiationGraphInclusion q) +
        krausFock hD BF a (radiationGraphInclusion r) :=
    (congrArg (krausFock hD BF a) (map_add radiationGraphInclusion q r)).trans (map_add _ _ _)
  apply Subtype.ext
  apply Prod.ext
  · exact hx
  · change radiationRoot ⟨_, kraus_mem_domain hD BF normal F C a (q + r)⟩ =
      radiationRoot ⟨_, kraus_mem_domain hD BF normal F C a q⟩ +
        radiationRoot ⟨_, kraus_mem_domain hD BF normal F C a r⟩
    rw [← LinearPMap.map_add]
    exact congrArg radiationRoot (Subtype.ext hx)

theorem krausGraphFun_smul (a : ℕ) (c : ℂ) (q : RadiationGraphSpace) :
    krausGraphFun hD BF normal F C a (c • q) = c • krausGraphFun hD BF normal F C a q := by
  have hx : krausFock hD BF a (radiationGraphInclusion (c • q)) =
      c • krausFock hD BF a (radiationGraphInclusion q) :=
    (congrArg (krausFock hD BF a) (map_smul radiationGraphInclusion c q)).trans (map_smul _ _ _)
  apply Subtype.ext
  apply Prod.ext
  · exact hx
  · change radiationRoot ⟨_, kraus_mem_domain hD BF normal F C a (c • q)⟩ =
      c • radiationRoot ⟨_, kraus_mem_domain hD BF normal F C a q⟩
    rw [← LinearPMap.map_smul]
    exact congrArg radiationRoot (Subtype.ext hx)

theorem krausFock_norm_le (a : ℕ) (u : PhotonFock) : ‖krausFock hD BF a u‖ ≤ ‖u‖ :=
  (lp.norm_apply_le_norm two_ne_zero _ a).trans_eq (LinearIsometry.norm_map _ u)

theorem krausGraphFun_norm_le (a : ℕ) (q : RadiationGraphSpace) :
    ‖krausGraphFun hD BF normal F C a q‖ ≤ 1 * ‖q‖ := by
  have hq1 : ‖radiationGraphInclusion q‖ ≤ ‖q‖ := _root_.norm_fst_le q.val
  have hq2 : ‖radiationGraphDerivative q‖ ≤ ‖q‖ := _root_.norm_snd_le q.val
  rw [one_mul]
  change max ‖krausFock hD BF a (radiationGraphInclusion q)‖
    ‖radiationGraphDerivative (krausGraphFun hD BF normal F C a q)‖ ≤ _
  exact max_le ((krausFock_norm_le hD BF a _).trans hq1)
    ((krausGraphFun_derivative_le hD BF normal F C a q).trans hq2)

/-- **`K_a` on the radiation graph.** -/
def krausGraph (a : ℕ) : RadiationGraphSpace →L[ℂ] RadiationGraphSpace :=
  LinearMap.mkContinuous
    { toFun := krausGraphFun hD BF normal F C a
      map_add' := krausGraphFun_add hD BF normal F C a
      map_smul' := krausGraphFun_smul hD BF normal F C a }
    1 (krausGraphFun_norm_le hD BF normal F C a)

theorem krausGraph_inclusion (a : ℕ) (q : RadiationGraphSpace) :
    radiationGraphInclusion (krausGraph hD BF normal F C a q) =
      krausFock hD BF a (radiationGraphInclusion q) := rfl

theorem krausGraph_derivative_energy (a : ℕ) (q : RadiationGraphSpace) :
    ENNReal.ofReal (‖radiationGraphDerivative (krausGraph hD BF normal F C a q)‖ ^ 2) =
      radiationForm (krausFock hD BF a (radiationGraphInclusion q)) :=
  krausGraphFun_derivative_energy hD BF normal F C a q

/-- **The field of a bright kernel commutes with the bright Kraus coordinates.** -/
theorem kernelField_krausGraph (k : WeightedPhotonKernel)
    (hk : MomentumSplit.projection photonMeasure Dᶜ hD.compl k.val.1 = k.val.1)
    (a : ℕ) (q : RadiationGraphSpace) :
    kernelField C k (krausGraph hD BF normal F C a q) =
      krausFock hD BF a (kernelField C k q) := by
  have hk' : (retainedMap (brightSplit hD)).adjoint k.val.1 = k.val.1 :=
    (congrArg (fun A : Lp ℂ 2 photonMeasure →L[ℂ] Lp ℂ 2 photonMeasure => A k.val.1)
      (MomentumSplit.projection_adjoint photonMeasure Dᶜ hD.compl)).trans hk
  have h1 := channelField_output BF C (brightSplit hD) k.val.1 k hk' k rfl q
    (krausGraph hD BF normal F C a q) a rfl
  have h2 := channelField_eq_factor_add_vacuum BF C (brightSplit hD) k.val.1 k hk' q
  have h3 : channelVacuum BF C (brightSplit hD) k.val.1 k hk' q = 0 := by
    have hn : ‖channelVacuum BF C (brightSplit hD) k.val.1 k hk' q‖ ^ 2 = 0 :=
      (channelVacuum_norm_sq BF C (brightSplit hD) k.val.1 k hk' q).trans
        (by rw [sub_self, zero_mul])
    exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hn)
  calc kernelField C k (krausGraph hD BF normal F C a q)
      = channelField BF C (brightSplit hD) k.val.1 k hk' q a := h1
    _ = ((photonFactorization BF).factor (brightSplit hD) (kernelField C k q) +
          channelVacuum BF C (brightSplit hD) k.val.1 k hk' q) a :=
        congrArg (fun w : Space (fun _ : ℕ => PhotonFock) => w a) h2
    _ = ((photonFactorization BF).factor (brightSplit hD) (kernelField C k q) + 0) a :=
        congrArg (fun w : Space (fun _ : ℕ => PhotonFock) =>
          ((photonFactorization BF).factor (brightSplit hD) (kernelField C k q) + w) a) h3
    _ = krausFock hD BF a (kernelField C k q) :=
        congrArg (fun w : Space (fun _ : ℕ => PhotonFock) => w a) (add_zero _)

end Normal

end GptLean.PhysicalFock.DarkModes
