import GptLean.PhysicalFockRadiationLocalization

/-!
The ordinary bounded multiplier theorem on negative half-Sobolev space
gives a uniform radiation bound for the actual localization channel.
The finite shell frame then recovers the full radiation form by monotone
summation. This also proves the radiation domain of every Kraus output.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory Gaussian SymmetricLift PhotonLocalization PhotonLocalizationKernelCutoffs
  PhotonLocalizationPhysicalKernels PhotonLocalizationFockChannel
  PhotonLocalizationFormBounds PhysicalNormalTrace
  PhysicalNormalTrace.StandardNormalTraceBackground
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types false

private theorem realLinear_bessel_bound {V ι : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] [Fintype ι]
    (b : ι → V) (hb : ∀ z, ∑ i, ‖⟪b i, z⟫_ℂ‖ ^ 2 ≤ ‖z‖ ^ 2)
    (A : V →L[ℝ] V) (M : ℝ) (hA : ‖A‖ ≤ M) (z : V) :
    ∑ i, ‖⟪A (b i), z⟫_ℂ‖ ^ 2 ≤ 2 * M ^ 2 * ‖z‖ ^ 2 := by
  let : InnerProductSpace ℝ V := InnerProductSpace.rclikeToReal ℂ V
  have hre (w : V) : ∑ i, ⟪b i, w⟫_ℝ ^ 2 ≤ ‖w‖ ^ 2 := by
    apply le_trans (Finset.sum_le_sum (fun i _ => ?_)) (hb w)
    rw [real_inner_eq_re_inner ℂ]
    change (⟪b i, w⟫_ℂ).re ^ 2 ≤ ‖⟪b i, w⟫_ℂ‖ ^ 2
    nlinarith [Complex.sq_norm_sub_sq_re ⟪b i, w⟫_ℂ,
      sq_nonneg (⟪b i, w⟫_ℂ).im]
  have hadj (w : V) : ‖A.adjoint w‖ ^ 2 ≤ M ^ 2 * ‖w‖ ^ 2 := by
    have hn : ‖A.adjoint w‖ ≤ M * ‖w‖ := by
      apply (A.adjoint.le_opNorm w).trans
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg w)
      simpa only [ContinuousLinearMap.adjoint.norm_map] using hA
    calc
      _ ≤ (M * ‖w‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ = _ := mul_pow _ _ _
  have he (v : V) : ‖⟪v, z⟫_ℂ‖ ^ 2 =
      ⟪v, z⟫_ℝ ^ 2 + ⟪v, Complex.I • z⟫_ℝ ^ 2 := by
    rw [real_inner_eq_re_inner ℂ, real_inner_eq_re_inner ℂ, inner_smul_right]
    change ‖⟪v, z⟫_ℂ‖ ^ 2 = (⟪v, z⟫_ℂ).re ^ 2 + (Complex.I * ⟪v, z⟫_ℂ).re ^ 2
    simp only [Complex.mul_re, Complex.I_re, zero_mul, Complex.I_im, one_mul,
      zero_sub, neg_sq]
    nlinarith [Complex.sq_norm_sub_sq_re ⟪v, z⟫_ℂ]
  simp_rw [he, Finset.sum_add_distrib, ← ContinuousLinearMap.adjoint_inner_right]
  have h1 := (hre (A.adjoint z)).trans (hadj z)
  have h2 := (hre (A.adjoint (Complex.I • z))).trans (hadj (Complex.I • z))
  have hz : ‖Complex.I • z‖ = ‖z‖ := by simp only [norm_smul, Complex.norm_I, one_mul]
  rw [hz] at h2
  nlinarith

variable {E S V : Type} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [InnerProductSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [SMulCommClass ℝ ℂ E]
  [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  {μ : Measure FieldSpace}
  (C : FourierRadiationCoordinates (E := E) (V := V) (μ := μ) (ν := photonMeasure))
  (B : SobolevMultiplierBackground S) (J : V ≃ₗᵢ[ℝ] S)

def radiationMultiplierConstant : ℝ := 1 + 2 * B.multiplierConstant ^ 2

theorem radiationMultiplierConstant_pos : 0 < radiationMultiplierConstant B := by
  unfold radiationMultiplierConstant
  positivity

private def transportedMultiplier (m : ℕ) : V →L[ℝ] V :=
  J.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((B.multiplier (retained (radius m))).comp J.toLinearIsometry.toContinuousLinearMap)

omit [CompleteSpace V] in
private theorem transportedMultiplier_norm (m : ℕ) :
    ‖transportedMultiplier B J m‖ ≤ B.multiplierConstant := by
  apply ContinuousLinearMap.opNorm_le_bound _ B.multiplierConstant_nonneg
  intro v
  change ‖J.symm (B.multiplier (retained (radius m)) (J v))‖ ≤ _
  rw [J.symm.norm_map]
  exact ((B.multiplier (retained (radius m))).le_opNorm (J v)).trans (by
    rw [J.norm_map]
    exact mul_le_mul_of_nonneg_right (B.retained_bound (radius m) (radius_pos m)) (norm_nonneg v))

omit [InnerProductSpace ℝ E] [IsScalarTower ℝ ℂ E] [SMulCommClass ℝ ℂ E] in
theorem radiationLocalization_coefficient_bound (k m : ℕ) (z : V) :
    ∑ i : Fin k, ‖⟪(radiationLocalizationFamily C B J).localized k m i, z⟫_ℂ‖ ^ 2 ≤
      radiationMultiplierConstant B * ‖z‖ ^ 2 := by
  have h := realLinear_bessel_bound (radiationLocalizationBasis C k)
    (radiationLocalizationBasis_bessel C k) (transportedMultiplier B J m)
    B.multiplierConstant (transportedMultiplier_norm B J m) z
  simp only [radiationLocalizationFamily_localized]
  apply le_trans h
  unfold radiationMultiplierConstant
  nlinarith [sq_nonneg ‖z‖]

variable (hmultiplier : ∀ (χ : FieldSpace → ℝ) (_hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (_hc : HasCompactSupport χ)
    (hχm : AEStronglyMeasurable χ μ) (hb : ∀ᵐ y ∂μ, |χ y| ≤ 1) a w,
    C.representative J a w →
    C.representative J (PhotonKernelLocalization.l2Multiplier χ hχm hb a)
      (B.multiplier χ w))

include hmultiplier in
theorem radiationLocalization_onePhoton_bound (hdispersion : C.momentum = Prod.fst)
    (m : ℕ) (u : Lp E 2 μ) :
    onePhotonFamilyValue radiationFamily
      (C.fourier (retainedMap (complexOnePhotonIsometry (radius m)) u)) ≤
      ENNReal.ofReal (radiationMultiplierConstant B) *
        onePhotonFamilyValue radiationFamily (C.fourier u) := by
  by_cases hu : onePhotonFamilyValue radiationFamily (C.fourier u) < ⊤
  · change (∑' i, ENNReal.ofReal (‖⟪radiationFamily i,
      C.fourier (retainedMap (complexOnePhotonIsometry (radius m)) u)⟫_ℂ‖ ^ 2)) ≤ _
    rw [ENNReal.tsum_eq_iSup_nat]
    apply iSup_le
    intro k
    obtain ⟨z, hz, hp⟩ := radiationLocalization_duality C B J hmultiplier hdispersion k m u hu
    have ht := radiationLocalization_truncation C k
      (retainedMap (complexOnePhotonIsometry (radius m)) u)
    rw [finiteFamily_value] at ht
    change radiationPartial (fun i v => ⟪radiationFamily i, v⟫_ℂ) k
      (C.fourier (retainedMap (complexOnePhotonIsometry (radius m)) u)) ≤ _
    rw [ht, hz, ← ENNReal.ofReal_mul (radiationMultiplierConstant_pos B).le]
    apply ENNReal.ofReal_le_ofReal
    simpa only [hp] using radiationLocalization_coefficient_bound C B J k m z
  · have hinf : onePhotonFamilyValue radiationFamily (C.fourier u) = ⊤ :=
      top_unique (not_lt.mp hu)
    simp only [hinf, ENNReal.mul_top (ENNReal.ofReal_pos.mpr
      (radiationMultiplierConstant_pos B)).ne', le_top]

include hmultiplier in
/-- A uniform bound for the full radiation form, on the same normal channel. -/
theorem fullFormCalculus_radiation_bound
    (BF : StandardSymmetricFockExponential) (CCR : CanonicalSectorCCR photonMeasure)
    (BT : StandardNormalTraceBackground) (N m : ℕ)
    (hdispersion : C.momentum = Prod.fst) {x : BT.FullTrace N}
    (hx : x ∈ (BT.realization (FullHilbert N)).rank.positive) :
    ((fullFormCalculus BF CCR BT C.fourier N).observable radiationFamily).expectation
      (BT.normal.extend ((fullFactorization BF C.fourier N).factor
        (complexOnePhotonIsometry (radius m))) x) ≤
      ENNReal.ofReal (radiationMultiplierConstant B) *
        ((fullFormCalculus BF CCR BT C.fourier N).observable radiationFamily).expectation x := by
  exact (fullFormCalculus BF CCR BT C.fourier N).channel_bound BT.normal
    (fun _ hx => hx) (complexOnePhotonIsometry (radius m)) radiationFamily radiationFamily
    (radiationLocalization_onePhoton_bound C B J hmultiplier hdispersion m) hx

include hmultiplier in
theorem fullFactorization_radiation_sum_bound
    (BF : StandardSymmetricFockExponential) (CCR : CanonicalSectorCCR photonMeasure)
    (BT : StandardNormalTraceBackground) (N m : ℕ)
    (hdispersion : C.momentum = Prod.fst) (u : FullHilbert N) :
    (∑' a, ((fullFormCalculus BF CCR BT C.fourier N).observable radiationFamily).expectation
      ((BT.realization (FullHilbert N)).rank.rankOne
        ((fullFactorization BF C.fourier N).factor
          (complexOnePhotonIsometry (radius m)) u a))) ≤
      ENNReal.ofReal (radiationMultiplierConstant B) *
        ((fullFormCalculus BF CCR BT C.fourier N).observable radiationFamily).expectation
          ((BT.realization (FullHilbert N)).rank.rankOne u) := by
  let D := fullFormCalculus BF CCR BT C.fourier N
  have hp := D.pullback (complexOnePhotonIsometry (radius m)) radiationFamily u
  have hr := D.rankOne radiationFamily u
  have hb : fockForm (fun v => D.value radiationFamily
      (retainedMap (complexOnePhotonIsometry (radius m)) v)) (D.slice u) ≤
      ENNReal.ofReal (radiationMultiplierConstant B) *
        fockForm (D.value radiationFamily) (D.slice u) :=
    fockForm_le (radiationLocalization_onePhoton_bound C B J hmultiplier hdispersion m) (D.slice u)
  exact hp.le.trans (hb.trans_eq
    (congrArg (fun r : ℝ≥0∞ => ENNReal.ofReal (radiationMultiplierConstant B) * r) hr.symm))

include hmultiplier in
/-- Each actual output has a radiation graph source when the input does. -/
theorem fullFactorization_radiation_domain
    (BF : StandardSymmetricFockExponential) (CCR : CanonicalSectorCCR photonMeasure)
    (BT : StandardNormalTraceBackground) (N m : ℕ)
    (hdispersion : C.momentum = Prod.fst) (u : FullHilbert N)
    (hu : ∃ s : SpatialRadiationGraph (volume : Measure (Configuration N)),
      spatialRadiationInclusion volume s = u) (a : ℕ) :
    ∃ s : SpatialRadiationGraph (volume : Measure (Configuration N)),
      spatialRadiationInclusion volume s =
        (fullFactorization BF C.fourier N).factor (complexOnePhotonIsometry (radius m)) u a := by
  let D := fullFormCalculus BF CCR BT C.fourier N
  have hfin : (D.observable radiationFamily).expectation
      ((BT.realization (FullHilbert N)).rank.rankOne u) < ⊤ :=
    (fullFormCalculus_radiation_finite_iff BF CCR BT C.fourier N u).mpr hu
  have hs : (∑' b, (D.observable radiationFamily).expectation
      ((BT.realization (FullHilbert N)).rank.rankOne
        ((fullFactorization BF C.fourier N).factor
          (complexOnePhotonIsometry (radius m)) u b))) ≤
      ENNReal.ofReal (radiationMultiplierConstant B) *
        (D.observable radiationFamily).expectation
          ((BT.realization (FullHilbert N)).rank.rankOne u) :=
    fullFactorization_radiation_sum_bound C B J hmultiplier BF CCR BT N m hdispersion u
  apply (fullFormCalculus_radiation_finite_iff BF CCR BT C.fourier N _).mp
  exact (ENNReal.le_tsum a).trans_lt (hs.trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin))

end GptLean.PhysicalFock
