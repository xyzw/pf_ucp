import GptLean.PhysicalSmearedCurl

/-!
Momentum cutoffs of the article field kernel, used for `prop-div-jph`.

The article kernel `G^μ_x(k, λ) = e^{-i k·x} ε^μ_λ(k) χ(-k)/√2` is only
continuous in `x`, since the cutoff assumption gives no `|k| χ ∈ L²`.
Keeping only the photon momenta `|k| ≤ n` gives kernels `G^{μ,n}_x` with
the derivative `∂_ν G^{μ,n}_x = -i k_ν G^{μ,n}_x` in the weighted kernel
norm. The polarization vectors are orthogonal to `k`, so
`∑_μ ∂_μ G^{μ,n}_x = 0`: the Coulomb gauge of the cutoff kernels. The cutoff
kernels converge to the article kernel uniformly in `x`.
-/

noncomputable section

namespace GptLean.PhysicalDivergenceKernel

open MeasureTheory Filter Asymptotics PhysicalFock Gaussian PhysicalPolarization
  PhotonLocalizationPhysicalKernels TransformationsKernelCovariance
open scoped ENNReal Topology

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

section Weights

/-- The momentum cutoff `1_{|k| ≤ n}`. -/
def band (n : ℕ) (p : PhotonMode) : ℂ := if ‖p.1‖ ≤ n then 1 else 0

theorem measurable_band (n : ℕ) : Measurable (band n) :=
  Measurable.ite (measurableSet_le measurable_fst.norm measurable_const)
    measurable_const measurable_const

theorem band_of_le {n : ℕ} {p : PhotonMode} (h : ‖p.1‖ ≤ n) : band n p = 1 := by
  simp [band, h]

theorem band_of_not_le {n : ℕ} {p : PhotonMode} (h : ¬ ‖p.1‖ ≤ n) : band n p = 0 := by
  simp [band, h]

theorem norm_band_le (n : ℕ) (p : PhotonMode) : ‖band n p‖ ≤ 1 := by
  by_cases h : ‖p.1‖ ≤ n
  · rw [band_of_le h, norm_one]
  · rw [band_of_not_le h, norm_zero]
    exact zero_le_one

theorem norm_one_sub_band_le (n : ℕ) (p : PhotonMode) : ‖1 - band n p‖ ≤ 1 := by
  by_cases h : ‖p.1‖ ≤ n
  · rw [band_of_le h, sub_self, norm_zero]
    exact zero_le_one
  · rw [band_of_not_le h, sub_zero, norm_one]

theorem measurable_coordinate (ν : Fin 3) :
    Measurable (fun p : PhotonMode => ((p.1 ν : ℝ) : ℂ)) :=
  Complex.measurable_ofReal.comp
    ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) ν).measurable.comp measurable_fst)

/-- The derivative weight `-i k_ν 1_{|k| ≤ n}`. -/
def slopeWeight (n : ℕ) (ν : Fin 3) (p : PhotonMode) : ℂ :=
  -(Complex.I * ((p.1 ν : ℝ) : ℂ)) * band n p

theorem measurable_slopeWeight (n : ℕ) (ν : Fin 3) : Measurable (slopeWeight n ν) :=
  ((measurable_coordinate ν).const_mul Complex.I).neg.mul (measurable_band n)

theorem norm_slopeWeight_le (n : ℕ) (ν : Fin 3) (p : PhotonMode) : ‖slopeWeight n ν p‖ ≤ n := by
  by_cases h : ‖p.1‖ ≤ n
  · have hk : ‖p.1 ν‖ ≤ n := (PiLp.norm_apply_le p.1 ν).trans h
    simp only [slopeWeight, band_of_le h, mul_one, norm_neg, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real]
    exact hk
  · simp only [slopeWeight, band_of_not_le h, mul_zero, norm_zero]
    exact Nat.cast_nonneg n

end Weights

section Scale

private theorem scale_sq_le (c : ℝ) (m z : ℂ) (hm : ‖m‖ ≤ c) :
    ‖m * z‖ ^ 2 ≤ c ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hm 2) (sq_nonneg _)

/-- Form factors multiplied by bounded measurable weights. -/
def scaleFactors (F₀ : FormFactors photonMeasure (Fin 3)) (m : Fin 3 → PhotonMode → ℂ)
    (hm : ∀ a, Measurable (m a)) (c : ℝ) (hc : ∀ a p, ‖m a p‖ ≤ c) :
    FormFactors photonMeasure (Fin 3) where
  momentum := F₀.momentum
  momentum_measurable := F₀.momentum_measurable
  base a p := m a p * F₀.base a p
  measurable a := (hm a).mul (F₀.measurable a)
  ultraviolet a := by
    refine ((F₀.ultraviolet a).const_mul (c ^ 2)).mono'
      (((hm a).mul (F₀.measurable a)).norm.pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun p => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact scale_sq_le c _ _ (hc a p)
  infrared a := by
    refine ((F₀.infrared a).const_mul (c ^ 2)).mono'
      ((F₀.momentum_measurable.norm.const_div 1).mul
        (((hm a).mul (F₀.measurable a)).norm.pow_const 2)).aestronglyMeasurable
      (ae_of_all _ fun p => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (sq_nonneg _))]
    calc (1 / ‖F₀.momentum p‖) * ‖m a p * F₀.base a p‖ ^ 2 ≤
        (1 / ‖F₀.momentum p‖) * (c ^ 2 * ‖F₀.base a p‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (scale_sq_le c _ _ (hc a p)) (by positivity)
      _ = c ^ 2 * ((1 / ‖F₀.momentum p‖) * ‖F₀.base a p‖ ^ 2) := by ring

end Scale

section Remainder

/-- Shifting the position along a coordinate multiplies the phase. -/
theorem phase_shift (k x : FieldSpace) (ν : Fin 3) (t : ℝ) :
    fieldPhase k (x + t • EuclideanSpace.single ν 1) =
      fieldPhase k x * Complex.exp (-(Complex.I * ((t * k ν : ℝ) : ℂ))) := by
  rw [← fieldPhase_mul]
  congr 1
  unfold fieldPhase
  congr 1
  simp only [inner_smul_right, EuclideanSpace.inner_single_right, one_mul, conj_trivial]
  push_cast
  ring

/-- The second-order Taylor remainder of a phase at one momentum. -/
theorem pointwise_remainder (k x : FieldSpace) (ν : Fin 3) (t : ℝ) (n : ℕ) (g : ℂ)
    (hband : ¬ ‖k‖ ≤ n → g = 0) (ht : |t| * n ≤ 1) :
    ‖fieldPhase k (x + t • EuclideanSpace.single ν 1) * g - fieldPhase k x * g -
        t • (fieldPhase k x * (-(Complex.I * ((k ν : ℝ) : ℂ)) * g))‖ ≤
      t ^ 2 * n ^ 2 * ‖fieldPhase k x * g‖ := by
  by_cases hk : ‖k‖ ≤ n
  · have hkν : |k ν| ≤ n := by
      have h := PiLp.norm_apply_le k ν
      rw [Real.norm_eq_abs] at h
      exact h.trans hk
    have hs : |t * k ν| ≤ 1 :=
      calc |t * k ν| = |t| * |k ν| := abs_mul _ _
        _ ≤ |t| * n := mul_le_mul_of_nonneg_left hkν (abs_nonneg t)
        _ ≤ 1 := ht
    have hz : ‖-(Complex.I * ((t * k ν : ℝ) : ℂ))‖ = |t * k ν| := by
      simp only [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_mul]
    have he := Complex.norm_exp_sub_one_sub_id_le (hz.trans_le hs)
    rw [hz, sq_abs] at he
    have hφ : ‖fieldPhase k x‖ = 1 := norm_fieldPhase k x
    have heq : fieldPhase k (x + t • EuclideanSpace.single ν 1) * g - fieldPhase k x * g -
        t • (fieldPhase k x * (-(Complex.I * ((k ν : ℝ) : ℂ)) * g)) =
        fieldPhase k x * g * (Complex.exp (-(Complex.I * ((t * k ν : ℝ) : ℂ))) - 1 -
          -(Complex.I * ((t * k ν : ℝ) : ℂ))) := by
      rw [phase_shift, Complex.real_smul]
      push_cast
      ring
    rw [heq, norm_mul, norm_mul, hφ, one_mul]
    have hsq : (t * k ν) ^ 2 ≤ t ^ 2 * n ^ 2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (sq_le_sq' (abs_le.mp hkν).1 (abs_le.mp hkν).2)
        (sq_nonneg t)
    calc ‖g‖ * ‖Complex.exp (-(Complex.I * ((t * k ν : ℝ) : ℂ))) - 1 -
          -(Complex.I * ((t * k ν : ℝ) : ℂ))‖ ≤ ‖g‖ * (t * k ν) ^ 2 :=
          mul_le_mul_of_nonneg_left he (norm_nonneg g)
      _ ≤ ‖g‖ * (t ^ 2 * n ^ 2) := mul_le_mul_of_nonneg_left hsq (norm_nonneg g)
      _ = t ^ 2 * n ^ 2 * ‖g‖ := mul_comm _ _
  · rw [hband hk]
    simp

/-- The Taylor remainder of a band-limited phase family in `L²` is
quadratic in the displacement. -/
theorem phase_remainder_le (Φ Ψ : FieldSpace → Lp ℂ 2 photonMeasure) (g h : PhotonMode → ℂ)
    (hΦ : ∀ x, Φ x =ᵐ[photonMeasure] fun p => fieldPhase p.1 x * g p)
    (hΨ : ∀ x, Ψ x =ᵐ[photonMeasure] fun p => fieldPhase p.1 x * h p)
    (n : ℕ) (ν : Fin 3) (hband : ∀ p, ¬ ‖p.1‖ ≤ n → g p = 0)
    (hh : ∀ p, h p = -(Complex.I * ((p.1 ν : ℝ) : ℂ)) * g p) (x : FieldSpace) (t : ℝ)
    (ht : |t| * n ≤ 1) :
    ‖Φ (x + t • EuclideanSpace.single ν 1) - Φ x - t • Ψ x‖ ≤ (t ^ 2 * n ^ 2) * ‖Φ x‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub (Φ (x + t • EuclideanSpace.single ν 1) - Φ x) (t • Ψ x),
    Lp.coeFn_sub (Φ (x + t • EuclideanSpace.single ν 1)) (Φ x), Lp.coeFn_smul t (Ψ x),
    hΦ (x + t • EuclideanSpace.single ν 1), hΦ x, hΨ x] with p h₁ h₂ h₃ hA hB hC
  have hv : (Φ (x + t • EuclideanSpace.single ν 1) - Φ x - t • Ψ x) p =
      fieldPhase p.1 (x + t • EuclideanSpace.single ν 1) * g p - fieldPhase p.1 x * g p -
        t • (fieldPhase p.1 x * (-(Complex.I * ((p.1 ν : ℝ) : ℂ)) * g p)) :=
    h₁.trans (congrArg₂ (fun a b : ℂ => a - b) (h₂.trans (congrArg₂ (fun a b : ℂ => a - b) hA hB))
      (h₃.trans (congrArg (fun z : ℂ => t • z) (hC.trans
        (congrArg (fun z : ℂ => fieldPhase p.1 x * z) (hh p))))))
  calc ‖(Φ (x + t • EuclideanSpace.single ν 1) - Φ x - t • Ψ x) p‖ = _ := congrArg norm hv
    _ ≤ t ^ 2 * n ^ 2 * ‖fieldPhase p.1 x * g p‖ :=
      pointwise_remainder p.1 x ν t n (g p) (hband p) ht
    _ = t ^ 2 * n ^ 2 * ‖Φ x p‖ := congrArg (fun z => t ^ 2 * n ^ 2 * ‖z‖) hB.symm

end Remainder

variable (F : Frame) (χ : ArticleCutoff)

section Kernels

/-- The article form factors restricted to the momenta `|k| ≤ n`. -/
def cutoffFactors (n : ℕ) : FormFactors photonMeasure (Fin 3) :=
  scaleFactors (formFactors F χ) (fun _ => band n) (fun _ => measurable_band n) 1
    (fun _ p => norm_band_le n p)

/-- The form factors `-i k_ν 1_{|k| ≤ n} G^μ_0` of the derivative in direction `ν`. -/
def slopeFactors (n : ℕ) (ν : Fin 3) : FormFactors photonMeasure (Fin 3) :=
  scaleFactors (formFactors F χ) (fun _ => slopeWeight n ν) (fun _ => measurable_slopeWeight n ν)
    n (fun _ p => norm_slopeWeight_le n ν p)

/-- The article kernel `G^μ_x`, as in `PhysicalPFCurrentAPriori.articleKernel`. -/
abbrev kernel : Fin 3 × FieldSpace → WeightedPhotonKernel :=
  PhysicalProfiles.momentumKernel (formFactors F χ) rfl (LinearIsometryEquiv.refl ℝ _)

/-- The cutoff kernel `G^{μ,n}_x`. -/
def cutoffKernel (n : ℕ) (μ : Fin 3) (x : FieldSpace) : WeightedPhotonKernel :=
  PhysicalProfiles.momentumKernel (cutoffFactors F χ n) rfl (LinearIsometryEquiv.refl ℝ _) (μ, x)

/-- The derivative `∂_ν G^{μ,n}_x = -i k_ν G^{μ,n}_x`. -/
def slopeKernel (n : ℕ) (μ ν : Fin 3) (x : FieldSpace) : WeightedPhotonKernel :=
  PhysicalProfiles.momentumKernel (slopeFactors F χ n ν) rfl (LinearIsometryEquiv.refl ℝ _) (μ, x)

theorem continuous_kernel (μ : Fin 3) : Continuous (fun x : FieldSpace => kernel F χ (μ, x)) :=
  (PhysicalProfiles.momentumKernel_continuous (formFactors F χ) rfl
    (LinearIsometryEquiv.refl ℝ _)).comp (continuous_const.prodMk continuous_id)

theorem continuous_cutoffKernel (n : ℕ) (μ : Fin 3) : Continuous (cutoffKernel F χ n μ) :=
  (PhysicalProfiles.momentumKernel_continuous (cutoffFactors F χ n) rfl
    (LinearIsometryEquiv.refl ℝ _)).comp (continuous_const.prodMk continuous_id)

theorem continuous_slopeKernel (n : ℕ) (μ ν : Fin 3) : Continuous (slopeKernel F χ n μ ν) :=
  (PhysicalProfiles.momentumKernel_continuous (slopeFactors F χ n ν) rfl
    (LinearIsometryEquiv.refl ℝ _)).comp (continuous_const.prodMk continuous_id)

theorem cutoff_band (n : ℕ) (μ : Fin 3) (p : PhotonMode) (h : ¬ ‖p.1‖ ≤ n) :
    (cutoffFactors F χ n).base μ p = 0 := by
  change band n p * base F χ μ p = 0
  rw [band_of_not_le h, zero_mul]

theorem cutoff_infrared_band (n : ℕ) (μ : Fin 3) (p : PhotonMode) (h : ¬ ‖p.1‖ ≤ n) :
    infraredBase Prod.fst ((cutoffFactors F χ n).base μ) p = 0 := by
  change (Real.sqrt ‖p.1‖)⁻¹ • ((cutoffFactors F χ n).base μ p) = 0
  rw [cutoff_band F χ n μ p h, smul_zero]

theorem slope_base (n : ℕ) (μ ν : Fin 3) (p : PhotonMode) :
    (slopeFactors F χ n ν).base μ p =
      -(Complex.I * ((p.1 ν : ℝ) : ℂ)) * (cutoffFactors F χ n).base μ p := by
  change slopeWeight n ν p * base F χ μ p = -(Complex.I * ((p.1 ν : ℝ) : ℂ)) *
    (band n p * base F χ μ p)
  unfold slopeWeight
  ring

theorem slope_infrared (n : ℕ) (μ ν : Fin 3) (p : PhotonMode) :
    infraredBase Prod.fst ((slopeFactors F χ n ν).base μ) p =
      -(Complex.I * ((p.1 ν : ℝ) : ℂ)) * infraredBase Prod.fst ((cutoffFactors F χ n).base μ) p := by
  change (Real.sqrt ‖p.1‖)⁻¹ • ((slopeFactors F χ n ν).base μ p) =
    -(Complex.I * ((p.1 ν : ℝ) : ℂ)) * ((Real.sqrt ‖p.1‖)⁻¹ • ((cutoffFactors F χ n).base μ p))
  rw [slope_base, Complex.real_smul, Complex.real_smul]
  ring

/-- **Differentiability of the cutoff kernels.** -/
theorem cutoffKernel_hasDerivAt (n : ℕ) (μ ν : Fin 3) (x : FieldSpace) :
    HasDerivAt (fun t : ℝ => cutoffKernel F χ n μ (x + t • EuclideanSpace.single ν 1))
      (slopeKernel F χ n μ ν x) 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  refine IsBigO.trans_isLittleO ?_ (isLittleO_pow_id (𝕜 := ℝ) one_lt_two)
  refine IsBigO.of_bound ((n : ℝ) ^ 2 * ‖cutoffKernel F χ n μ x‖) ?_
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, |t| * n ≤ 1 := by
    have hc : Continuous (fun t : ℝ => |t| * n) := continuous_abs.mul continuous_const
    have h0 : (fun t : ℝ => |t| * n) 0 < (fun _ : ℝ => (1 : ℝ)) 0 := by simp
    exact (hc.continuousAt.eventually_lt continuousAt_const h0).mono fun t ht => ht.le
  filter_upwards [hsmall] with t ht
  simp only [zero_add, zero_smul, add_zero]
  have h₁ := phase_remainder_le (fun y => (cutoffFactors F χ n).fourierKernel (μ, y))
    (fun y => (slopeFactors F χ n ν).fourierKernel (μ, y))
    ((cutoffFactors F χ n).base μ) ((slopeFactors F χ n ν).base μ)
    (fun y => fourierKernel_ae (cutoffFactors F χ n) rfl μ y)
    (fun y => fourierKernel_ae (slopeFactors F χ n ν) rfl μ y)
    n ν (cutoff_band F χ n μ) (slope_base F χ n μ ν) x t ht
  have h₂ := phase_remainder_le (fun y => (cutoffFactors F χ n).weightedFourierKernel (μ, y))
    (fun y => (slopeFactors F χ n ν).weightedFourierKernel (μ, y))
    (infraredBase Prod.fst ((cutoffFactors F χ n).base μ))
    (infraredBase Prod.fst ((slopeFactors F χ n ν).base μ))
    (fun y => weightedFourierKernel_ae (cutoffFactors F χ n) rfl μ y)
    (fun y => weightedFourierKernel_ae (slopeFactors F χ n ν) rfl μ y)
    n ν (cutoff_infrared_band F χ n μ) (slope_infrared F χ n μ ν) x t ht
  have hc₁ : (cutoffKernel F χ n μ (x + t • EuclideanSpace.single ν 1) -
      cutoffKernel F χ n μ x - t • slopeKernel F χ n μ ν x).val.1 =
      (cutoffFactors F χ n).fourierKernel (μ, x + t • EuclideanSpace.single ν 1) -
        (cutoffFactors F χ n).fourierKernel (μ, x) -
        t • (slopeFactors F χ n ν).fourierKernel (μ, x) :=
    congrArg₂ (fun a b => a - b)
      (congrArg₂ (fun a b => a - b)
        (momentumKernel_fst (cutoffFactors F χ n) rfl (LinearIsometryEquiv.refl ℝ _) (μ, x + t • EuclideanSpace.single ν 1))
        (momentumKernel_fst (cutoffFactors F χ n) rfl (LinearIsometryEquiv.refl ℝ _) (μ, x)))
      (congrArg (t • ·) (momentumKernel_fst (slopeFactors F χ n ν) rfl (LinearIsometryEquiv.refl ℝ _) (μ, x)))
  have hc₂ : (cutoffKernel F χ n μ (x + t • EuclideanSpace.single ν 1) -
      cutoffKernel F χ n μ x - t • slopeKernel F χ n μ ν x).val.2 =
      (cutoffFactors F χ n).weightedFourierKernel (μ, x + t • EuclideanSpace.single ν 1) -
        (cutoffFactors F χ n).weightedFourierKernel (μ, x) -
        t • (slopeFactors F χ n ν).weightedFourierKernel (μ, x) :=
    congrArg₂ (fun a b => a - b)
      (congrArg₂ (fun a b => a - b)
        (momentumKernel_snd (cutoffFactors F χ n) rfl (LinearIsometryEquiv.refl ℝ _) (μ, x + t • EuclideanSpace.single ν 1))
        (momentumKernel_snd (cutoffFactors F χ n) rfl (LinearIsometryEquiv.refl ℝ _) (μ, x)))
      (congrArg (t • ·) (momentumKernel_snd (slopeFactors F χ n ν) rfl (LinearIsometryEquiv.refl ℝ _) (μ, x)))
  have hk₁ : ‖(cutoffFactors F χ n).fourierKernel (μ, x)‖ ≤ ‖cutoffKernel F χ n μ x‖ :=
    (congrArg norm (momentumKernel_fst (cutoffFactors F χ n) rfl (LinearIsometryEquiv.refl ℝ _) (μ, x))).symm.trans_le
      (norm_fst_le (cutoffKernel F χ n μ x).val)
  have hk₂ : ‖(cutoffFactors F χ n).weightedFourierKernel (μ, x)‖ ≤ ‖cutoffKernel F χ n μ x‖ :=
    (congrArg norm (momentumKernel_snd (cutoffFactors F χ n) rfl (LinearIsometryEquiv.refl ℝ _) (μ, x))).symm.trans_le
      (norm_snd_le (cutoffKernel F χ n μ x).val)
  have hcoef : 0 ≤ t ^ 2 * (n : ℝ) ^ 2 := by positivity
  have hb : ‖cutoffKernel F χ n μ (x + t • EuclideanSpace.single ν 1) -
      cutoffKernel F χ n μ x - t • slopeKernel F χ n μ ν x‖ ≤
      t ^ 2 * (n : ℝ) ^ 2 * ‖cutoffKernel F χ n μ x‖ :=
    max_le ((congrArg norm hc₁).trans_le (h₁.trans (mul_le_mul_of_nonneg_left hk₁ hcoef)))
      ((congrArg norm hc₂).trans_le (h₂.trans (mul_le_mul_of_nonneg_left hk₂ hcoef)))
  refine hb.trans_eq ?_
  rw [Real.norm_of_nonneg (sq_nonneg t)]
  ring

/-- **The Coulomb gauge of the cutoff kernels**, `∑_μ ∂_μ G^{μ,n}_x = 0`. -/
theorem slope_transverse (n : ℕ) (x : FieldSpace) : ∑ μ, slopeKernel F χ n μ μ x = 0 := by
  have ht (p : PhotonMode) := PhysicalGroundState.base_transverse F χ p
  apply Subtype.ext
  rw [Submodule.coe_sum, Submodule.coe_zero, Fin.sum_univ_three]
  apply Prod.ext
  · change (slopeKernel F χ n 0 0 x).val.1 + (slopeKernel F χ n 1 1 x).val.1 +
      (slopeKernel F χ n 2 2 x).val.1 = 0
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [Lp.coeFn_add ((slopeKernel F χ n 0 0 x).val.1 + (slopeKernel F χ n 1 1 x).val.1)
        (slopeKernel F χ n 2 2 x).val.1,
      Lp.coeFn_add (slopeKernel F χ n 0 0 x).val.1 (slopeKernel F χ n 1 1 x).val.1,
      (Filter.EventuallyEq.of_eq (congrArg (fun f : Lp ℂ 2 photonMeasure => (f : PhotonMode → ℂ))
        (momentumKernel_fst (slopeFactors F χ n 0) rfl (LinearIsometryEquiv.refl ℝ _) (0, x)))).trans
        (fourierKernel_ae (slopeFactors F χ n 0) rfl 0 x),
      (Filter.EventuallyEq.of_eq (congrArg (fun f : Lp ℂ 2 photonMeasure => (f : PhotonMode → ℂ))
        (momentumKernel_fst (slopeFactors F χ n 1) rfl (LinearIsometryEquiv.refl ℝ _) (1, x)))).trans
        (fourierKernel_ae (slopeFactors F χ n 1) rfl 1 x),
      (Filter.EventuallyEq.of_eq (congrArg (fun f : Lp ℂ 2 photonMeasure => (f : PhotonMode → ℂ))
        (momentumKernel_fst (slopeFactors F χ n 2) rfl (LinearIsometryEquiv.refl ℝ _) (2, x)))).trans
        (fourierKernel_ae (slopeFactors F χ n 2) rfl 2 x)] with p hs hs' h0 h1 h2
    refine hs.trans ((congrArg₂ (fun a b : ℂ => a + b)
      (hs'.trans (congrArg₂ (fun a b : ℂ => a + b) h0 h1)) h2).trans ?_)
    have hp := ht p
    rw [Fin.sum_univ_three] at hp
    simp only [slope_base, Pi.zero_apply]
    change fieldPhase p.1 x * (-(Complex.I * ((p.1 0 : ℝ) : ℂ)) * (band n p * base F χ 0 p)) +
      fieldPhase p.1 x * (-(Complex.I * ((p.1 1 : ℝ) : ℂ)) * (band n p * base F χ 1 p)) +
      fieldPhase p.1 x * (-(Complex.I * ((p.1 2 : ℝ) : ℂ)) * (band n p * base F χ 2 p)) = 0
    linear_combination (-(fieldPhase p.1 x * Complex.I * band n p)) * hp
  · change (slopeKernel F χ n 0 0 x).val.2 + (slopeKernel F χ n 1 1 x).val.2 +
      (slopeKernel F χ n 2 2 x).val.2 = 0
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [Lp.coeFn_add ((slopeKernel F χ n 0 0 x).val.2 + (slopeKernel F χ n 1 1 x).val.2)
        (slopeKernel F χ n 2 2 x).val.2,
      Lp.coeFn_add (slopeKernel F χ n 0 0 x).val.2 (slopeKernel F χ n 1 1 x).val.2,
      (Filter.EventuallyEq.of_eq (congrArg (fun f : Lp ℂ 2 photonMeasure => (f : PhotonMode → ℂ))
        (momentumKernel_snd (slopeFactors F χ n 0) rfl (LinearIsometryEquiv.refl ℝ _) (0, x)))).trans
        (weightedFourierKernel_ae (slopeFactors F χ n 0) rfl 0 x),
      (Filter.EventuallyEq.of_eq (congrArg (fun f : Lp ℂ 2 photonMeasure => (f : PhotonMode → ℂ))
        (momentumKernel_snd (slopeFactors F χ n 1) rfl (LinearIsometryEquiv.refl ℝ _) (1, x)))).trans
        (weightedFourierKernel_ae (slopeFactors F χ n 1) rfl 1 x),
      (Filter.EventuallyEq.of_eq (congrArg (fun f : Lp ℂ 2 photonMeasure => (f : PhotonMode → ℂ))
        (momentumKernel_snd (slopeFactors F χ n 2) rfl (LinearIsometryEquiv.refl ℝ _) (2, x)))).trans
        (weightedFourierKernel_ae (slopeFactors F χ n 2) rfl 2 x)] with p hs hs' h0 h1 h2
    refine hs.trans ((congrArg₂ (fun a b : ℂ => a + b)
      (hs'.trans (congrArg₂ (fun a b : ℂ => a + b) h0 h1)) h2).trans ?_)
    have hp := ht p
    rw [Fin.sum_univ_three] at hp
    simp only [slope_infrared, Pi.zero_apply]
    change fieldPhase p.1 x * (-(Complex.I * ((p.1 0 : ℝ) : ℂ)) *
        ((Real.sqrt ‖p.1‖)⁻¹ • (band n p * base F χ 0 p))) +
      fieldPhase p.1 x * (-(Complex.I * ((p.1 1 : ℝ) : ℂ)) *
        ((Real.sqrt ‖p.1‖)⁻¹ • (band n p * base F χ 1 p))) +
      fieldPhase p.1 x * (-(Complex.I * ((p.1 2 : ℝ) : ℂ)) *
        ((Real.sqrt ‖p.1‖)⁻¹ • (band n p * base F χ 2 p))) = 0
    simp only [Complex.real_smul]
    linear_combination (-(fieldPhase p.1 x * Complex.I * band n p *
      (((Real.sqrt ‖p.1‖)⁻¹ : ℝ) : ℂ))) * hp

end Kernels

section Tail

theorem memLp_tail (n : ℕ) (μ : Fin 3) :
    MemLp (fun p => (1 - band n p) * base F χ μ p) 2 photonMeasure :=
  (PhysicalGroundState.base_memLp F χ μ).of_le
    (((measurable_const.sub (measurable_band n)).mul
      (base_measurable F χ μ)).aestronglyMeasurable)
    (ae_of_all _ fun p => by
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (norm_one_sub_band_le n p)))

theorem memLp_infraredBase (μ : Fin 3) :
    MemLp (infraredBase Prod.fst (base F χ μ)) 2 photonMeasure :=
  (memLp_two_iff_integrable_sq_norm
    (measurable_infraredBase Prod.fst measurable_fst _ (base_measurable F χ μ)).aestronglyMeasurable).2
    (infraredBase_integrable Prod.fst _ ((formFactors F χ).infrared μ))

theorem memLp_weightedTail (n : ℕ) (μ : Fin 3) :
    MemLp (fun p => (1 - band n p) * infraredBase Prod.fst (base F χ μ) p) 2 photonMeasure :=
  (memLp_infraredBase F χ μ).of_le
    (((measurable_const.sub (measurable_band n)).mul
      (measurable_infraredBase Prod.fst measurable_fst _ (base_measurable F χ μ))).aestronglyMeasurable)
    (ae_of_all _ fun p => by
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (norm_one_sub_band_le n p)))

/-- The `L²` part of the kernel with momenta `|k| > n`. -/
def tailL2 (n : ℕ) (μ : Fin 3) : Lp ℂ 2 photonMeasure :=
  (memLp_tail F χ n μ).toLp (fun p => (1 - band n p) * base F χ μ p)

/-- The inverse-frequency part of the kernel with momenta `|k| > n`. -/
def weightedTailL2 (n : ℕ) (μ : Fin 3) : Lp ℂ 2 photonMeasure :=
  (memLp_weightedTail F χ n μ).toLp
    (fun p => (1 - band n p) * infraredBase Prod.fst (base F χ μ) p)

/-- A uniform bound on the distance between the article and cutoff kernels. -/
def tail (n : ℕ) : ℝ := ∑ μ, (‖tailL2 F χ n μ‖ + ‖weightedTailL2 F χ n μ‖)

private theorem phase_sub_band (φ b c : ℂ) (hc : c = (1 - b)) (z : ℂ) :
    φ * z - φ * (b * z) = φ * (c * z) := by
  rw [hc]
  ring

theorem norm_kernel_sub_le (n : ℕ) (μ : Fin 3) (x : FieldSpace) :
    ‖kernel F χ (μ, x) - cutoffKernel F χ n μ x‖ ≤ tail F χ n := by
  have hle : ‖tailL2 F χ n μ‖ + ‖weightedTailL2 F χ n μ‖ ≤ tail F χ n :=
    Finset.single_le_sum (f := fun a => ‖tailL2 F χ n a‖ + ‖weightedTailL2 F χ n a‖)
      (fun a _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) (Finset.mem_univ μ)
  have h₁ : ‖(kernel F χ (μ, x) - cutoffKernel F χ n μ x).val.1‖ ≤ ‖tailL2 F χ n μ‖ := by
    have hv : (kernel F χ (μ, x) - cutoffKernel F χ n μ x).val.1 =
        (formFactors F χ).fourierKernel (μ, x) - (cutoffFactors F χ n).fourierKernel (μ, x) :=
      congrArg₂ (fun a b => a - b) (momentumKernel_fst (formFactors F χ) rfl (LinearIsometryEquiv.refl ℝ _) (μ, x))
        (momentumKernel_fst (cutoffFactors F χ n) rfl (LinearIsometryEquiv.refl ℝ _) (μ, x))
    refine (congrArg norm hv).trans_le ?_
    have h := Lp.norm_le_mul_norm_of_ae_le_mul (c := 1)
      (f := (formFactors F χ).fourierKernel (μ, x) - (cutoffFactors F χ n).fourierKernel (μ, x))
      (g := tailL2 F χ n μ) (by
        filter_upwards [Lp.coeFn_sub ((formFactors F χ).fourierKernel (μ, x))
            ((cutoffFactors F χ n).fourierKernel (μ, x)),
          fourierKernel_ae (formFactors F χ) rfl μ x,
          fourierKernel_ae (cutoffFactors F χ n) rfl μ x,
          (memLp_tail F χ n μ).coeFn_toLp] with p hs ha hb ht
        have hv : ((formFactors F χ).fourierKernel (μ, x) -
            (cutoffFactors F χ n).fourierKernel (μ, x)) p =
            fieldPhase p.1 x * ((1 - band n p) * base F χ μ p) :=
          hs.trans ((congrArg₂ (· - ·) ha hb).trans
            (phase_sub_band (fieldPhase p.1 x) (band n p) (1 - band n p) rfl (base F χ μ p)))
        rw [one_mul]
        refine (congrArg norm hv).trans_le (le_of_eq ?_)
        refine (norm_mul _ _).trans ?_
        rw [norm_fieldPhase, one_mul]
        exact congrArg norm ht.symm)
    rwa [one_mul] at h
  have h₂ : ‖(kernel F χ (μ, x) - cutoffKernel F χ n μ x).val.2‖ ≤
      ‖weightedTailL2 F χ n μ‖ := by
    have hv : (kernel F χ (μ, x) - cutoffKernel F χ n μ x).val.2 =
        (formFactors F χ).weightedFourierKernel (μ, x) -
          (cutoffFactors F χ n).weightedFourierKernel (μ, x) :=
      congrArg₂ (fun a b => a - b) (momentumKernel_snd (formFactors F χ) rfl (LinearIsometryEquiv.refl ℝ _) (μ, x))
        (momentumKernel_snd (cutoffFactors F χ n) rfl (LinearIsometryEquiv.refl ℝ _) (μ, x))
    refine (congrArg norm hv).trans_le ?_
    have h := Lp.norm_le_mul_norm_of_ae_le_mul (c := 1)
      (f := (formFactors F χ).weightedFourierKernel (μ, x) -
        (cutoffFactors F χ n).weightedFourierKernel (μ, x))
      (g := weightedTailL2 F χ n μ) (by
        filter_upwards [Lp.coeFn_sub ((formFactors F χ).weightedFourierKernel (μ, x))
            ((cutoffFactors F χ n).weightedFourierKernel (μ, x)),
          weightedFourierKernel_ae (formFactors F χ) rfl μ x,
          weightedFourierKernel_ae (cutoffFactors F χ n) rfl μ x,
          (memLp_weightedTail F χ n μ).coeFn_toLp] with p hs ha hb ht
        have hi : infraredBase Prod.fst ((cutoffFactors F χ n).base μ) p =
            band n p * infraredBase Prod.fst (base F χ μ) p := by
          change (Real.sqrt ‖p.1‖)⁻¹ • (band n p * base F χ μ p) =
            band n p * ((Real.sqrt ‖p.1‖)⁻¹ • base F χ μ p)
          rw [Complex.real_smul, Complex.real_smul]
          ring
        have hv : ((formFactors F χ).weightedFourierKernel (μ, x) -
            (cutoffFactors F χ n).weightedFourierKernel (μ, x)) p =
            fieldPhase p.1 x * ((1 - band n p) * infraredBase Prod.fst (base F χ μ) p) :=
          hs.trans ((congrArg₂ (· - ·) ha (hb.trans (congrArg (fieldPhase p.1 x * ·) hi))).trans
            (phase_sub_band (fieldPhase p.1 x) (band n p) (1 - band n p) rfl _))
        rw [one_mul]
        refine (congrArg norm hv).trans_le (le_of_eq ?_)
        refine (norm_mul _ _).trans ?_
        rw [norm_fieldPhase, one_mul]
        exact congrArg norm ht.symm)
    rwa [one_mul] at h
  exact (max_le (h₁.trans (le_add_of_nonneg_right (norm_nonneg _)))
    (h₂.trans (le_add_of_nonneg_left (norm_nonneg _)))).trans hle

private theorem tendsto_band_tail (g : PhotonMode → ℂ) (p : PhotonMode) :
    Tendsto (fun n : ℕ => (1 - band n p) * g p) atTop (𝓝 0) := by
  obtain ⟨m, hm⟩ := exists_nat_ge ‖p.1‖
  refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨m, fun n hn => ?_⟩)
  have hp : ‖p.1‖ ≤ n := hm.trans (Nat.cast_le.mpr hn)
  change (0 : ℂ) = (1 - band n p) * g p
  rw [band_of_le hp, sub_self, zero_mul]

private theorem tendsto_norm_tail (g : PhotonMode → ℂ) (hg : MemLp g 2 photonMeasure)
    (hf : ∀ n : ℕ, MemLp (fun p => (1 - band n p) * g p) 2 photonMeasure) :
    Tendsto (fun n => ‖(hf n).toLp (fun p => (1 - band n p) * g p)‖) atTop (𝓝 0) := by
  have h := SymmetricLift.tendsto_toLp_two_of_dominated_sq hf
    (MemLp.zero : MemLp (0 : PhotonMode → ℂ) 2 photonMeasure)
    ((memLp_two_iff_integrable_sq_norm hg.1).1 hg)
    (fun n => ae_of_all _ fun p => by
      rw [norm_mul, mul_pow]
      exact mul_le_of_le_one_left (sq_nonneg _)
        (pow_le_one₀ (norm_nonneg _) (norm_one_sub_band_le n p)))
    (ae_of_all _ fun p => by simp)
    (ae_of_all _ fun p => tendsto_band_tail g p)
  have hn := h.norm
  have h0 : ‖(MemLp.zero : MemLp (0 : PhotonMode → ℂ) 2 photonMeasure).toLp
      (0 : PhotonMode → ℂ)‖ = 0 := by
    rw [Lp.norm_toLp, eLpNorm_zero, ENNReal.toReal_zero]
  rwa [h0] at hn

/-- The cutoff kernels converge to the article kernel uniformly in `x`. -/
theorem tendsto_tail : Tendsto (tail F χ) atTop (𝓝 0) := by
  have h : Tendsto (tail F χ) atTop (𝓝 (∑ _μ : Fin 3, ((0 : ℝ) + 0))) :=
    tendsto_finsetSum _ fun μ _ =>
      (tendsto_norm_tail (base F χ μ) (PhysicalGroundState.base_memLp F χ μ)
        (fun n => memLp_tail F χ n μ)).add
      (tendsto_norm_tail (infraredBase Prod.fst (base F χ μ)) (memLp_infraredBase F χ μ)
        (fun n => memLp_weightedTail F χ n μ))
  simpa using h

end Tail

end GptLean.PhysicalDivergenceKernel
