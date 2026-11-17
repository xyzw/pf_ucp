import GptLean.PhysicalGroundStateAmplitude
import GptLean.TransformationsTimeReversalFrame

/-!
Smeared field kernels of test vector fields.

For a smooth compactly supported test field `u`, the article's smeared kernel is
`g_u = ∑_a ∫ u^a(x) G^a_x dx`. With `G^a_x(k, λ) = e^{-i k·x} ε^a_λ(k) χ(-k)/√2`
this is the momentum-space function `g_u(k, λ) = ∑_a G^a_0(k, λ) û^a(k)`, with
`û(k) = ∫ e^{-i k·x} u(x) dx`. The smeared vector potential is the Segal field of
the weighted kernel `(g_u, g_u/√ω)`. Integration by parts gives
`(∂_j u)^ = i k_j û`, so `ω g_u` is square integrable and the smeared transverse
electric field `-i (a†(ω g_u) - a(ω g_u))` is the Segal field of the weighted
kernel `-i (ω g_u, √ω g_u)`. The cutoff reality condition makes `g_u` odd under
the one-photon time reversal `Υ 𝒞`, exactly as the kernels `G^a_y` are, so every
`⟨G^a_y, g_u⟩` is real.
-/

noncomputable section

namespace GptLean.PhysicalGroundState

open MeasureTheory Filter PhysicalFock PhysicalPairSpace Gaussian PhysicalPolarization
  TransformationsTimeReversal TransformationsRotation TransformationsFock
  TransformationsKernelCovariance
open scoped ENNReal InnerProductSpace ContDiff

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

section Fourier

theorem continuous_fieldPhase_left (x : FieldSpace) :
    Continuous (fun k : FieldSpace => fieldPhase k x) := by
  have h : Continuous (fun k : FieldSpace => inner ℝ k x) := continuous_id.inner continuous_const
  exact Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp h.neg).mul continuous_const)

theorem continuous_fieldPhase_right (k : FieldSpace) :
    Continuous (fun x : FieldSpace => fieldPhase k x) := by
  have h : Continuous (fun x : FieldSpace => inner ℝ k x) := continuous_const.inner continuous_id
  exact Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp h.neg).mul continuous_const)

theorem fieldPhase_zero_right (k : FieldSpace) : fieldPhase k 0 = 1 := by
  simp [fieldPhase]

/-- The Fourier coefficient `û(k) = ∫ e^{-i k·x} u(x) dx` of a real function. -/
def fourierCoeff (w : FieldSpace → ℝ) (k : FieldSpace) : ℂ :=
  ∫ x, fieldPhase k x * (w x : ℂ)

theorem norm_phase_mul (k x : FieldSpace) (r : ℝ) : ‖fieldPhase k x * (r : ℂ)‖ = ‖r‖ := by
  rw [norm_mul, norm_fieldPhase, one_mul, Complex.norm_real]

theorem norm_fourierCoeff_le (w : FieldSpace → ℝ) (k : FieldSpace) :
    ‖fourierCoeff w k‖ ≤ ∫ x, ‖w x‖ :=
  (norm_integral_le_integral_norm _).trans_eq
    (integral_congr_ae (ae_of_all _ fun x => norm_phase_mul k x (w x)))

theorem integrable_phase_mul (w : FieldSpace → ℝ) (hw : Integrable w volume) (k : FieldSpace) :
    Integrable (fun x => fieldPhase k x * (w x : ℂ)) volume :=
  hw.norm.mono' ((continuous_fieldPhase_right k).aestronglyMeasurable.mul
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hw.1))
    (ae_of_all _ fun x => (norm_phase_mul k x (w x)).le)

theorem continuous_fourierCoeff (w : FieldSpace → ℝ) (hw : Integrable w volume) :
    Continuous (fourierCoeff w) :=
  continuous_of_dominated (fun k => (integrable_phase_mul w hw k).1)
    (fun k => ae_of_all _ fun x => (norm_phase_mul k x (w x)).le) hw.norm
    (ae_of_all _ fun x => (continuous_fieldPhase_left x).mul continuous_const)

theorem conj_fourierCoeff_neg (w : FieldSpace → ℝ) (k : FieldSpace) :
    starRingEnd ℂ (fourierCoeff w (-k)) = fourierCoeff w k := by
  unfold fourierCoeff
  rw [← integral_conj]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [map_mul, conj_fieldPhase_neg, Complex.conj_ofReal]

/-- The derivative of the phase `x ↦ e^{-i k·x}`. -/
theorem hasFDerivAt_fieldPhase (k x : FieldSpace) :
    HasFDerivAt (fun y => fieldPhase k y)
      (fieldPhase k x • ((-(innerSL ℝ k)).smulRight Complex.I)) x := by
  have h := (((-(innerSL ℝ k)).smulRight Complex.I).hasFDerivAt (x := x)).cexp
  have hfun : (fun y => fieldPhase k y) =
      fun y => Complex.exp (((-(innerSL ℝ k)).smulRight Complex.I) y) := by
    funext y
    simp [fieldPhase, Complex.real_smul]
  have hx : fieldPhase k x = Complex.exp (((-(innerSL ℝ k)).smulRight Complex.I) x) :=
    congrFun hfun x
  rw [hfun, hx]
  exact h

private theorem phase_derivative_apply (k x : FieldSpace) (j : Fin 3) (r : ℝ) :
    (fieldPhase k x • ((-(innerSL ℝ k)).smulRight Complex.I))
        (EuclideanSpace.single j (1 : ℝ)) * (r : ℂ) =
      -((k j : ℂ) * Complex.I) * (fieldPhase k x * (r : ℂ)) := by
  simp [EuclideanSpace.inner_single_right, Complex.real_smul]
  ring

/-- **Fourier coefficient of a partial derivative**, `(∂_j w)^(k) = i k_j ŵ(k)`. -/
theorem fourierCoeff_partial (w : FieldSpace → ℝ) (hw : ContDiff ℝ 1 w)
    (hs : HasCompactSupport w) (j : Fin 3) (k : FieldSpace) :
    fourierCoeff (fun x => fderiv ℝ w x (EuclideanSpace.single j 1)) k =
      ((k j : ℂ) * Complex.I) * fourierCoeff w k := by
  have hdiff : Differentiable ℝ w := hw.differentiable (by norm_num)
  have hcw : Continuous w := hw.continuous
  have hcd : Continuous (fun x => fderiv ℝ w x (EuclideanSpace.single j 1)) :=
    (hw.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hsd : HasCompactSupport (fun x => fderiv ℝ w x (EuclideanSpace.single j 1)) :=
    hs.fderiv_apply ℝ _
  have hiw : Integrable w volume := hcw.integrable_of_hasCompactSupport hs
  have hid : Integrable (fun x => fderiv ℝ w x (EuclideanSpace.single j 1)) volume :=
    hcd.integrable_of_hasCompactSupport hsd
  have hg (x : FieldSpace) : HasFDerivAt (fun y => (w y : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ w x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x (hdiff x).hasFDerivAt
  have hf'g : Integrable (fun x => (fieldPhase k x • ((-(innerSL ℝ k)).smulRight Complex.I))
      (EuclideanSpace.single j (1 : ℝ)) * (w x : ℂ)) volume :=
    ((integrable_phase_mul w hiw k).const_mul (-((k j : ℂ) * Complex.I))).congr
      (ae_of_all _ fun x => (phase_derivative_apply k x j (w x)).symm)
  have hfg' : Integrable (fun x => fieldPhase k x *
      (Complex.ofRealCLM.comp (fderiv ℝ w x)) (EuclideanSpace.single j (1 : ℝ))) volume :=
    integrable_phase_mul _ hid k
  have h := integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable
    (μ := volume) (B := ContinuousLinearMap.mul ℝ ℂ) (v := EuclideanSpace.single j (1 : ℝ))
    (f := fun y => fieldPhase k y)
    (f' := fun x => fieldPhase k x • ((-(innerSL ℝ k)).smulRight Complex.I))
    (g := fun y => (w y : ℂ)) (g' := fun x => Complex.ofRealCLM.comp (fderiv ℝ w x))
    hf'g hfg' (integrable_phase_mul w hiw k)
    (fun x _ => hasFDerivAt_fieldPhase k x) (fun x _ => hg x)
  have hL : fourierCoeff (fun x => fderiv ℝ w x (EuclideanSpace.single j 1)) k =
      ∫ x, fieldPhase k x *
        (Complex.ofRealCLM.comp (fderiv ℝ w x)) (EuclideanSpace.single j (1 : ℝ)) := rfl
  rw [hL]
  refine h.trans ?_
  have hR : (∫ x, (fieldPhase k x • ((-(innerSL ℝ k)).smulRight Complex.I))
      (EuclideanSpace.single j (1 : ℝ)) * (w x : ℂ)) =
      -((k j : ℂ) * Complex.I) * fourierCoeff w k := by
    exact (integral_congr_ae (ae_of_all _ fun x => phase_derivative_apply k x j (w x))).trans
      (integral_const_mul _ _)
  change -(∫ x, (fieldPhase k x • ((-(innerSL ℝ k)).smulRight Complex.I))
      (EuclideanSpace.single j (1 : ℝ)) * (w x : ℂ)) = _
  rw [hR]
  ring

theorem norm_le_sum_abs (k : FieldSpace) : ‖k‖ ≤ ∑ j, |k j| := by
  have h2 : ‖k‖ ^ 2 ≤ (∑ j, |k j|) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      (∑ j, k j ^ 2) = ∑ j, |k j| ^ 2 := Finset.sum_congr rfl fun j _ => (sq_abs _).symm
      _ ≤ (∑ j, |k j|) ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg fun j _ => abs_nonneg _
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Finset.sum_nonneg fun j _ => abs_nonneg _)
    two_ne_zero).mp h2

/-- The decay bound `|k| |ŵ(k)| ≤ ∑_j ‖∂_j w‖₁`. -/
theorem norm_mul_fourierCoeff_le (w : FieldSpace → ℝ) (hw : ContDiff ℝ 1 w)
    (hs : HasCompactSupport w) (k : FieldSpace) :
    ‖k‖ * ‖fourierCoeff w k‖ ≤
      ∑ j, ∫ x, ‖fderiv ℝ w x (EuclideanSpace.single j 1)‖ := by
  calc
    ‖k‖ * ‖fourierCoeff w k‖ ≤ (∑ j, |k j|) * ‖fourierCoeff w k‖ :=
      mul_le_mul_of_nonneg_right (norm_le_sum_abs k) (norm_nonneg _)
    _ = ∑ j, ‖fourierCoeff (fun x => fderiv ℝ w x (EuclideanSpace.single j 1)) k‖ := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [fourierCoeff_partial w hw hs j k, norm_mul, norm_mul, Complex.norm_real,
        Complex.norm_I, mul_one, Real.norm_eq_abs]
    _ ≤ _ := Finset.sum_le_sum fun j _ => norm_fourierCoeff_le _ k

end Fourier

/-- A smooth compactly supported real test vector field on physical space. -/
structure TestField where
  fn : FieldSpace → Vector
  smooth : ContDiff ℝ ∞ fn
  compact : HasCompactSupport fn

namespace TestField

variable (u : TestField)

/-- The component `u^a`. -/
def comp (a : Fin 3) (x : FieldSpace) : ℝ := u.fn x a

theorem comp_contDiff (a : Fin 3) : ContDiff ℝ ∞ (u.comp a) :=
  (EuclideanSpace.proj a : Vector →L[ℝ] ℝ).contDiff.comp u.smooth

theorem comp_compact (a : Fin 3) : HasCompactSupport (u.comp a) :=
  u.compact.comp_left (g := fun v : Vector => v a) (by simp)

theorem comp_integrable (a : Fin 3) : Integrable (u.comp a) volume :=
  (u.comp_contDiff a).continuous.integrable_of_hasCompactSupport (u.comp_compact a)

theorem comp_contDiff_one (a : Fin 3) : ContDiff ℝ 1 (u.comp a) :=
  (u.comp_contDiff a).of_le (by exact_mod_cast le_top)

/-- The `L¹` bound of `û^a`. -/
def massBound (a : Fin 3) : ℝ := ∫ x, ‖u.comp a x‖

/-- The `L¹` bound of `|k| |û^a|`. -/
def derivBound (a : Fin 3) : ℝ :=
  ∑ j, ∫ x, ‖fderiv ℝ (u.comp a) x (EuclideanSpace.single j 1)‖

theorem massBound_nonneg (a : Fin 3) : 0 ≤ u.massBound a :=
  integral_nonneg fun _ => norm_nonneg _

theorem derivBound_nonneg (a : Fin 3) : 0 ≤ u.derivBound a :=
  Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => norm_nonneg _

end TestField

variable (F : Frame) (χ : ArticleCutoff)

section Kernels

/-- The base kernels as `L²` functions. -/
theorem base_memLp (a : Fin 3) : MemLp (base F χ a) 2 photonMeasure :=
  (memLp_two_iff_integrable_sq_norm (base_measurable F χ a).aestronglyMeasurable).mpr
    (base_ultraviolet F χ a)

/-- `base_a / √ω`. -/
def weightedBase (a : Fin 3) (p : PhotonMode) : ℂ :=
  ((Real.sqrt ‖p.1‖ : ℝ) : ℂ)⁻¹ * base F χ a p

theorem measurable_sqrtOmega : Measurable (fun p : PhotonMode => ((Real.sqrt ‖p.1‖ : ℝ) : ℂ)) :=
  Complex.measurable_ofReal.comp measurable_fst.norm.sqrt

theorem measurable_omega : Measurable (fun p : PhotonMode => ((‖p.1‖ : ℝ) : ℂ)) :=
  Complex.measurable_ofReal.comp measurable_fst.norm

theorem weightedBase_memLp (a : Fin 3) : MemLp (weightedBase F χ a) 2 photonMeasure := by
  have hm : AEStronglyMeasurable (weightedBase F χ a) photonMeasure :=
    (measurable_sqrtOmega.inv.mul (base_measurable F χ a)).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hm).mpr ((base_infrared F χ a).congr
    (ae_of_all _ fun p => ?_))
  change (1 / ‖p.1‖) * ‖base F χ a p‖ ^ 2 = ‖weightedBase F χ a p‖ ^ 2
  rw [weightedBase, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, inv_pow, Real.sq_sqrt (norm_nonneg _), one_div]

/-- The smeared kernel `g_u(k, λ) = ∑_a G^a_0(k, λ) û^a(k)`. -/
def smearedFun (u : TestField) (p : PhotonMode) : ℂ :=
  ∑ a, base F χ a p * fourierCoeff (u.comp a) p.1

theorem measurable_smearedFun (u : TestField) : Measurable (smearedFun F χ u) :=
  Finset.measurable_sum _ fun a _ => (base_measurable F χ a).mul
    ((continuous_fourierCoeff _ (u.comp_integrable a)).measurable.comp measurable_fst)

theorem memLp_of_sum_bound {g : PhotonMode → ℂ} (hg : AEStronglyMeasurable g photonMeasure)
    (c : Fin 3 → ℝ) (b : Fin 3 → PhotonMode → ℂ) (hb : ∀ a, MemLp (b a) 2 photonMeasure)
    (h : ∀ p, ‖g p‖ ≤ ∑ a, c a * ‖b a p‖) : MemLp g 2 photonMeasure :=
  (memLp_finsetSum Finset.univ fun a _ => ((hb a).norm.const_mul (c a))).mono' hg
    (ae_of_all _ h)

theorem norm_smearedFun_le (u : TestField) (p : PhotonMode) :
    ‖smearedFun F χ u p‖ ≤ ∑ a, u.massBound a * ‖base F χ a p‖ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (norm_fourierCoeff_le _ _) (norm_nonneg _)

theorem smearedFun_memLp (u : TestField) : MemLp (smearedFun F χ u) 2 photonMeasure :=
  memLp_of_sum_bound (measurable_smearedFun F χ u).aestronglyMeasurable _ _ (base_memLp F χ)
    (norm_smearedFun_le F χ u)

theorem weightedSmeared_memLp (u : TestField) :
    MemLp (fun p => ((Real.sqrt ‖p.1‖ : ℝ) : ℂ)⁻¹ * smearedFun F χ u p) 2 photonMeasure := by
  refine memLp_of_sum_bound ((measurable_sqrtOmega.inv.mul
    (measurable_smearedFun F χ u)).aestronglyMeasurable) u.massBound _
    (weightedBase_memLp F χ) fun p => ?_
  rw [norm_mul]
  refine (mul_le_mul_of_nonneg_left (norm_smearedFun_le F χ u p) (norm_nonneg _)).trans_eq ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [weightedBase, norm_mul]
  ring

theorem norm_omegaSmearedFun_le (u : TestField) (p : PhotonMode) :
    ‖((‖p.1‖ : ℝ) : ℂ) * smearedFun F χ u p‖ ≤ ∑ a, u.derivBound a * ‖base F χ a p‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [norm_mul]
  have h := norm_mul_fourierCoeff_le (u.comp a) (u.comp_contDiff_one a) (u.comp_compact a) p.1
  calc
    ‖p.1‖ * (‖base F χ a p‖ * ‖fourierCoeff (u.comp a) p.1‖) =
        ‖base F χ a p‖ * (‖p.1‖ * ‖fourierCoeff (u.comp a) p.1‖) := by ring
    _ ≤ ‖base F χ a p‖ * u.derivBound a := mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = u.derivBound a * ‖base F χ a p‖ := mul_comm _ _

theorem omegaSmeared_memLp (u : TestField) :
    MemLp (fun p => ((‖p.1‖ : ℝ) : ℂ) * smearedFun F χ u p) 2 photonMeasure :=
  memLp_of_sum_bound ((measurable_omega.mul (measurable_smearedFun F χ u)).aestronglyMeasurable)
    u.derivBound _ (base_memLp F χ) (norm_omegaSmearedFun_le F χ u)

theorem sqrtOmegaSmeared_memLp (u : TestField) :
    MemLp (fun p => ((Real.sqrt ‖p.1‖ : ℝ) : ℂ) * smearedFun F χ u p) 2 photonMeasure := by
  refine ((smearedFun_memLp F χ u).norm.add (omegaSmeared_memLp F χ u).norm).mono'
    ((measurable_sqrtOmega.mul (measurable_smearedFun F χ u)).aestronglyMeasurable)
    (ae_of_all _ fun p => ?_)
  change ‖_‖ ≤ ‖smearedFun F χ u p‖ + ‖((‖p.1‖ : ℝ) : ℂ) * smearedFun F χ u p‖
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg (norm_nonneg _)]
  have hs : Real.sqrt ‖p.1‖ ≤ 1 + ‖p.1‖ := by
    nlinarith [Real.sq_sqrt (norm_nonneg p.1), Real.sqrt_nonneg ‖p.1‖,
      sq_nonneg (Real.sqrt ‖p.1‖ - 1)]
  nlinarith [norm_nonneg (smearedFun F χ u p)]

/-- The smeared kernel `g_u` as a photon `L²` function. -/
def smearedL2 (u : TestField) : Lp ℂ 2 photonMeasure := (smearedFun_memLp F χ u).toLp _

/-- **The smeared vector potential kernel** `(g_u, g_u/√ω)`, so that
`∫ u · A = Φ(g_u)`. -/
def smearedKernel (u : TestField) : WeightedPhotonKernel :=
  ⟨((smearedFun_memLp F χ u).toLp _, (weightedSmeared_memLp F χ u).toLp _), by
    show ∀ᵐ p ∂photonMeasure, _ = _
    filter_upwards [(smearedFun_memLp F χ u).coeFn_toLp, (weightedSmeared_memLp F χ u).coeFn_toLp,
      PhysicalOnePhotonFourier.momentum_nonzero] with p h₁ h₂ h₀
    rw [h₁, h₂, ← mul_assoc]
    have hne : ((Real.sqrt ‖p.1‖ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (norm_pos_iff.mpr h₀))
    rw [mul_inv_cancel₀ hne, one_mul]⟩

/-- **The electric direction kernel** `(ω g_u, √ω g_u)`. The smeared transverse
electric field is the Segal field of `-i` times this kernel. -/
def electricBase (u : TestField) : WeightedPhotonKernel :=
  ⟨((omegaSmeared_memLp F χ u).toLp _, (sqrtOmegaSmeared_memLp F χ u).toLp _), by
    show ∀ᵐ p ∂photonMeasure, _ = _
    filter_upwards [(omegaSmeared_memLp F χ u).coeFn_toLp,
      (sqrtOmegaSmeared_memLp F χ u).coeFn_toLp] with p h₁ h₂
    rw [h₁, h₂, ← mul_assoc, ← Complex.ofReal_mul, Real.mul_self_sqrt (norm_nonneg _)]⟩

theorem electricBase_snd (u : TestField) :
    ∀ᵐ p ∂photonMeasure, (electricBase F χ u).val.2 p =
      ((Real.sqrt ‖p.1‖ : ℝ) : ℂ) * smearedL2 F χ u p := by
  filter_upwards [(sqrtOmegaSmeared_memLp F χ u).coeFn_toLp,
    (smearedFun_memLp F χ u).coeFn_toLp] with p h₁ h₂
  exact h₁.trans (congrArg (fun z : ℂ => ((Real.sqrt ‖p.1‖ : ℝ) : ℂ) * z) h₂.symm)

end Kernels

section Reality

theorem smearedFun_odd (u : TestField) :
    ∀ᵐ k ∂(volume : Measure FieldSpace), k ≠ 0 → ∀ a,
      ∑ b, (overlap inversion F k a b : ℂ) * starRingEnd ℂ (smearedFun F χ u (-k, b)) =
        -smearedFun F χ u (k, a) := by
  filter_upwards [ae_all_iff.mpr fun c => base_ae F χ c] with k hk hk0 a
  unfold smearedFun
  simp only [map_sum, map_mul, conj_fourierCoeff_neg]
  calc
    _ = ∑ c, (∑ b, (overlap inversion F k a b : ℂ) * starRingEnd ℂ (base F χ c (-k, b))) *
        fourierCoeff (u.comp c) k := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => by ring
    _ = ∑ c, -base F χ c (k, a) * fourierCoeff (u.comp c) k :=
      Finset.sum_congr rfl fun c _ => by rw [hk c hk0 a]
    _ = _ := by simp only [neg_mul, Finset.sum_neg_distrib]

/-- The smeared kernel is odd under the one-photon time reversal `Υ 𝒞`. -/
theorem smeared_reversal (u : TestField) :
    (photonFamily inversion F).one (conjL2 (smearedL2 F χ u)) = -smearedL2 F χ u :=
  oneParticle_inversion F (smearedFun F χ u) (smearedFun_odd F χ u) 0 (by
    filter_upwards [(smearedFun_memLp F χ u).coeFn_toLp] with p hp
    rw [fieldPhase_zero_right, one_mul]
    exact hp)

theorem kernelAt_ae (b : Fin 3) (y : FieldSpace) :
    kernelAt F χ b y =ᵐ[photonMeasure] fun p => fieldPhase p.1 y * base F χ b p :=
  (Filter.EventuallyEq.of_eq (congrArg (fun f : Lp ℂ 2 photonMeasure => (f : PhotonMode → ℂ))
    (momentumKernel_fst (formFactors F χ) rfl (LinearIsometryEquiv.refl ℝ _) (b, y)))).trans
    (fourierKernel_ae (formFactors F χ) rfl b y)

theorem kernel_reversal_one (b : Fin 3) (y : FieldSpace) :
    (photonFamily inversion F).one (conjL2 (kernelAt F χ b y)) = -kernelAt F χ b y :=
  oneParticle_inversion F (base F χ b) (base_ae F χ b) y (kernelAt_ae F χ b y)

/-- **The scalar products `⟨G^b_y, g_u⟩` are real.** -/
theorem im_inner_kernel_smeared (u : TestField) (b : Fin 3) (y : FieldSpace) :
    (⟪kernelAt F χ b y, smearedL2 F χ u⟫_ℂ).im = 0 := by
  have h1 : ⟪(photonFamily inversion F).one (conjL2 (kernelAt F χ b y)),
      (photonFamily inversion F).one (conjL2 (smearedL2 F χ u))⟫_ℂ =
      starRingEnd ℂ ⟪kernelAt F χ b y, smearedL2 F χ u⟫_ℂ :=
    ((photonFamily inversion F).one.inner_map_map _ _).trans (inner_antiunitary conjL2 _ _)
  have h2 : ⟪(photonFamily inversion F).one (conjL2 (kernelAt F χ b y)),
      (photonFamily inversion F).one (conjL2 (smearedL2 F χ u))⟫_ℂ =
      ⟪kernelAt F χ b y, smearedL2 F χ u⟫_ℂ :=
    (congrArg₂ (fun x z : Lp ℂ 2 photonMeasure => ⟪x, z⟫_ℂ) (kernel_reversal_one F χ b y)
      (smeared_reversal F χ u)).trans (inner_neg_neg _ _)
  exact Complex.conj_eq_iff_im.mp (h1.symm.trans h2)

end Reality

end GptLean.PhysicalGroundState
