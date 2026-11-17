import PfHk.PhysicalFieldRegularity

/-! Strong derivatives of the full Fourier kernels, proved by dominated
convergence of difference quotients. No compact momentum support is used. -/

noncomputable section
namespace PfHk.PhysicalFieldRegularity

open MeasureTheory Filter GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.PhotonLocalizationPhysicalKernels GptLean.PhysicalNonattainmentFluxKernel Gaussian
open scoped ENNReal InnerProductSpace Topology

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

section General
variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

/-- The exact directional Fourier multiplier. -/
def directionBase (momentum : Ω → FieldSpace) (v : FieldSpace) (g : Ω → ℂ) (p : Ω) : ℂ :=
  (-Complex.I * (inner ℝ (momentum p) v : ℂ)) * g p

theorem directionBase_measurable (momentum : Ω → FieldSpace) (hm : Measurable momentum)
    (v : FieldSpace) (g : Ω → ℂ) (hg : Measurable g) :
    Measurable (directionBase momentum v g) := by
  exact ((Complex.measurable_ofReal.comp ((continuous_inner : Continuous (fun q : FieldSpace × FieldSpace => inner ℝ q.1 q.2)).measurable.comp (hm.prodMk measurable_const))).const_mul
    (-Complex.I)).mul hg

omit [MeasurableSpace Ω] in
theorem directionBase_norm (momentum : Ω → FieldSpace) (v : FieldSpace) (g : Ω → ℂ) (p : Ω) :
    ‖directionBase momentum v g p‖ = |inner ℝ (momentum p) v| * ‖g p‖ := by
  simp [directionBase]

omit [MeasurableSpace Ω] in
theorem momentumKernel_hasDerivAt (momentum : Ω → FieldSpace) (g : Ω → ℂ)
    (x v : FieldSpace) (p : Ω) (t : ℝ) :
    HasDerivAt (fun s : ℝ => momentumKernel momentum g (x + s • v) p)
      (momentumKernel momentum (directionBase momentum v g) (x + t • v) p) t := by
  convert! (fieldPhase_hasDerivAt (momentum p) x v t).mul_const (g p) using 1
  simp only [momentumKernel, directionBase]
  ring

omit [MeasurableSpace Ω] in
theorem momentumKernel_slope_bound (momentum : Ω → FieldSpace) (g : Ω → ℂ)
    (x v : FieldSpace) (p : Ω) (t : ℝ) :
    ‖t⁻¹ • (momentumKernel momentum g (x + t • v) p - momentumKernel momentum g x p)‖ ≤
      ‖directionBase momentum v g p‖ := by
  have hd := fun s => momentumKernel_hasDerivAt momentum g x v p s
  have hb : ∀ s : ℝ, ‖deriv (fun t : ℝ => momentumKernel momentum g (x + t • v) p) s‖ ≤
      ‖directionBase momentum v g p‖ := by
    intro s
    rw [(hd s).deriv, norm_momentumKernel]
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun s (_ : s ∈ Set.univ) => (hd s).differentiableAt)
    (fun s (_ : s ∈ Set.univ) => hb s) (convex_univ : Convex ℝ (Set.univ : Set ℝ))
    (Set.mem_univ (0 : ℝ)) (Set.mem_univ t)
  simp only [zero_smul, add_zero, sub_zero] at h
  by_cases ht : t = 0
  · simp [ht]
  · rw [norm_smul, norm_inv]
    calc
      _ ≤ ‖t‖⁻¹ * (‖directionBase momentum v g p‖ * ‖t‖) :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (norm_nonneg _))
      _ = _ := by field_simp

/-- Differentiation in one-photon L² needs only the corresponding first
moment, with no derivative of the cutoff or polarization frame. -/
theorem momentumKernelL2_hasLineDerivAt (momentum : Ω → FieldSpace)
    (hm : Measurable momentum) (g : Ω → ℂ) (hg : Measurable g)
    (hbase : Integrable (fun p => ‖g p‖ ^ 2) ν) (v : FieldSpace)
    (hder : Integrable (fun p => ‖directionBase momentum v g p‖ ^ 2) ν) (x : FieldSpace) :
    HasLineDerivAt ℝ (momentumKernelL2 momentum hm g hg hbase)
      (momentumKernelL2 momentum hm (directionBase momentum v g)
        (directionBase_measurable momentum hm v g hg) hder x) x v := by
  apply hasLineDerivAt_iff_tendsto_slope_zero.mpr
  apply Filter.tendsto_iff_seq_tendsto.mpr
  intro tn htn
  let f : ℕ → Ω → ℂ := fun n p => (tn n)⁻¹ •
    (momentumKernel momentum g (x + tn n • v) p - momentumKernel momentum g x p)
  let df : Ω → ℂ := momentumKernel momentum (directionBase momentum v g) x
  have hf : ∀ n, MemLp (f n) 2 ν := fun n =>
    ((momentumKernel_memLp momentum hm g hg hbase _).sub
      (momentumKernel_memLp momentum hm g hg hbase x)).const_smul ((tn n)⁻¹)
  have hdf : MemLp df 2 ν := momentumKernel_memLp momentum hm _
    (directionBase_measurable momentum hm v g hg) hder x
  have hlim := GptLean.SymmetricLift.tendsto_toLp_two_of_dominated_sq hf hdf hder
    (fun n => Eventually.of_forall (fun p =>
      pow_le_pow_left₀ (norm_nonneg _) (momentumKernel_slope_bound momentum g x v p (tn n)) 2))
    (Eventually.of_forall (fun p => by rw [norm_momentumKernel]))
    (Eventually.of_forall (fun p => by
      have hd : HasLineDerivAt ℝ (fun y => momentumKernel momentum g y p)
          (momentumKernel momentum (directionBase momentum v g) x p) x v := by
        simpa only [HasLineDerivAt, zero_smul, add_zero] using
          momentumKernel_hasDerivAt momentum g x v p 0
      exact hd.tendsto_slope_zero.comp htn))
  exact hlim

end General

variable (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ)

theorem directionBase_bound (i : Fin 3) (v : FieldSpace) (p : PhotonMode) :
    ‖directionBase Prod.fst v (base F χ i) p‖ ≤ ‖v‖ * ‖omegaBase F χ i p‖ := by
  rw [directionBase_norm, omegaBase, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)]
  have h := abs_real_inner_le_norm p.1 v
  nlinarith [mul_le_mul_of_nonneg_right h (norm_nonneg (base F χ i p))]

include hUV in
theorem directionBase_ultraviolet (i : Fin 3) (v : FieldSpace) :
    Integrable (fun p => ‖directionBase Prod.fst v (base F χ i) p‖ ^ 2) photonMeasure := by
  apply ((omegaBase_ultraviolet F χ hUV i).const_mul (‖v‖ ^ 2)).mono'
    ((directionBase_measurable Prod.fst measurable_fst v _ (base_measurable F χ i)).norm.pow_const 2).aestronglyMeasurable
  filter_upwards with p
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (directionBase_bound F χ i v p) 2

include hUV in
theorem directionBase_infrared (i : Fin 3) (v : FieldSpace) :
    Integrable (fun p : PhotonMode =>
      (1 / ‖p.1‖) * ‖directionBase Prod.fst v (base F χ i) p‖ ^ 2) photonMeasure := by
  apply ((omegaBase_infrared F χ hUV i).const_mul (‖v‖ ^ 2)).mono'
    (((measurable_fst.norm.const_div 1).mul
      ((directionBase_measurable Prod.fst measurable_fst v _ (base_measurable F χ i)).norm.pow_const 2)).aestronglyMeasurable)
  filter_upwards with p
  change ‖(1 / ‖p.1‖) * ‖directionBase Prod.fst v (base F χ i) p‖ ^ 2‖ ≤ _
  rw [Real.norm_of_nonneg (by positivity)]
  have h := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (directionBase_bound F χ i v p) 2)
    (show 0 ≤ 1 / ‖p.1‖ by positivity)
  simpa only [mul_pow, mul_left_comm] using h

def directionFactors (v : FieldSpace) : FormFactors photonMeasure (Fin 3) where
  momentum := Prod.fst
  momentum_measurable := measurable_fst
  base i := directionBase Prod.fst v (base F χ i)
  measurable i := directionBase_measurable Prod.fst measurable_fst v _ (base_measurable F χ i)
  ultraviolet i := directionBase_ultraviolet F χ hUV i v
  infrared i := directionBase_infrared F χ hUV i v

/-- The actual spatial derivative, with its inverse-frequency component. -/
def directionKernel (i : Fin 3) (v x : FieldSpace) : WeightedPhotonKernel :=
  PhysicalProfiles.momentumKernel (directionFactors F χ hUV v) rfl
    (LinearIsometryEquiv.refl ℝ _) (i, x)

theorem directionKernel_continuous (i : Fin 3) (v : FieldSpace) :
    Continuous (directionKernel F χ hUV i v) :=
  (PhysicalProfiles.momentumKernel_continuous (directionFactors F χ hUV v) rfl
    (LinearIsometryEquiv.refl ℝ _)).comp (continuous_const.prodMk continuous_id)



theorem physicalKernel_fst (i : Fin 3) (x : FieldSpace) :
    (physicalKernel F χ i x).val.1 = (formFactors F χ).fourierKernel (i, x) :=
  TransformationsKernelCovariance.momentumKernel_fst _ rfl _ _

theorem physicalKernel_snd (i : Fin 3) (x : FieldSpace) :
    (physicalKernel F χ i x).val.2 = (formFactors F χ).weightedFourierKernel (i, x) :=
  TransformationsKernelCovariance.momentumKernel_snd _ rfl _ _

theorem directionKernel_fst (i : Fin 3) (v x : FieldSpace) :
    (directionKernel F χ hUV i v x).val.1 = (directionFactors F χ hUV v).fourierKernel (i, x) :=
  TransformationsKernelCovariance.momentumKernel_fst _ rfl _ _

theorem directionKernel_snd (i : Fin 3) (v x : FieldSpace) :
    (directionKernel F χ hUV i v x).val.2 =
      (directionFactors F χ hUV v).weightedFourierKernel (i, x) :=
  TransformationsKernelCovariance.momentumKernel_snd _ rfl _ _

theorem infraredBase_directionBase (g : PhotonMode → ℂ) (v : FieldSpace) :
    infraredBase Prod.fst (directionBase Prod.fst v g) =
      directionBase Prod.fst v (infraredBase Prod.fst g) := by
  funext p
  simp only [infraredBase, directionBase, Complex.real_smul]
  ring

/-- The spatial derivative holds in the full weighted norm, controlling
both the ordinary field term and its annihilation-energy bound. -/
theorem physicalKernel_hasLineDerivAt (i : Fin 3) (v x : FieldSpace) :
    HasLineDerivAt ℝ (physicalKernel F χ i) (directionKernel F χ hUV i v x) x v := by
  have hfst : HasLineDerivAt ℝ (fun y => (physicalKernel F χ i y).val.1)
      (directionKernel F χ hUV i v x).val.1 x v := by
    simp_rw [physicalKernel_fst, directionKernel_fst]
    exact momentumKernelL2_hasLineDerivAt Prod.fst measurable_fst (base F χ i)
      (base_measurable F χ i) (base_ultraviolet F χ i) v
      (directionBase_ultraviolet F χ hUV i v) x
  have hir : Integrable (fun p =>
      ‖directionBase Prod.fst v (infraredBase Prod.fst (base F χ i)) p‖ ^ 2) photonMeasure := by
    rw [← infraredBase_directionBase]
    exact infraredBase_integrable Prod.fst _ (directionBase_infrared F χ hUV i v)
  have hsnd : HasLineDerivAt ℝ (fun y => (physicalKernel F χ i y).val.2)
      (directionKernel F χ hUV i v x).val.2 x v := by
    simp_rw [physicalKernel_snd, directionKernel_snd]
    have h := momentumKernelL2_hasLineDerivAt Prod.fst measurable_fst
      (infraredBase Prod.fst (base F χ i))
      (measurable_infraredBase Prod.fst measurable_fst _ (base_measurable F χ i))
      (infraredBase_integrable Prod.fst _ (base_infrared F χ i)) v hir x
    convert! h using 1
    apply Lp.ext
    filter_upwards [momentumKernelL2_ae Prod.fst measurable_fst
        (infraredBase Prod.fst (directionBase Prod.fst v (base F χ i)))
        (measurable_infraredBase Prod.fst measurable_fst _
          (directionBase_measurable Prod.fst measurable_fst v _ (base_measurable F χ i)))
        (infraredBase_integrable Prod.fst _ (directionBase_infrared F χ hUV i v)) x,
      momentumKernelL2_ae Prod.fst measurable_fst
        (directionBase Prod.fst v (infraredBase Prod.fst (base F χ i)))
        (directionBase_measurable Prod.fst measurable_fst v _
          (measurable_infraredBase Prod.fst measurable_fst _ (base_measurable F χ i))) hir x]
      with p hp hq
    change (momentumKernelL2 Prod.fst measurable_fst
      (infraredBase Prod.fst (directionBase Prod.fst v (base F χ i))) _ _ x : PhotonMode → ℂ) p = _
    rw [hp, hq, infraredBase_directionBase]
  apply hasLineDerivAt_iff_tendsto_slope_zero.mpr
  apply tendsto_subtype_rng.mpr
  exact hfst.tendsto_slope_zero.prodMk_nhds hsnd.tendsto_slope_zero



/-- The bound is uniform in the spatial point and linear in the direction. -/
theorem directionKernel_norm_le (i : Fin 3) (v x : FieldSpace) :
    ‖directionKernel F χ hUV i v x‖ ≤ ‖v‖ * ‖omegaKernel F χ hUV i x‖ := by
  have hfst : ‖(directionKernel F χ hUV i v x).val.1‖ ≤
      ‖v‖ * ‖(omegaKernel F χ hUV i x).val.1‖ := by
    rw [directionKernel_fst, show (omegaKernel F χ hUV i x).val.1 =
      (omegaFactors F χ hUV).fourierKernel (i, x) from
      TransformationsKernelCovariance.momentumKernel_fst _ rfl _ _]
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [TransformationsKernelCovariance.fourierKernel_ae
        (directionFactors F χ hUV v) rfl i x,
      TransformationsKernelCovariance.fourierKernel_ae (omegaFactors F χ hUV) rfl i x]
      with p hp hq
    rw [hp, hq, norm_mul, norm_mul, norm_fieldPhase, one_mul, one_mul]
    exact directionBase_bound F χ i v p
  have hsnd : ‖(directionKernel F χ hUV i v x).val.2‖ ≤
      ‖v‖ * ‖(omegaKernel F χ hUV i x).val.2‖ := by
    rw [directionKernel_snd, show (omegaKernel F χ hUV i x).val.2 =
      (omegaFactors F χ hUV).weightedFourierKernel (i, x) from
      TransformationsKernelCovariance.momentumKernel_snd _ rfl _ _]
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [TransformationsKernelCovariance.weightedFourierKernel_ae
        (directionFactors F χ hUV v) rfl i x,
      TransformationsKernelCovariance.weightedFourierKernel_ae (omegaFactors F χ hUV) rfl i x]
      with p hp hq
    rw [hp, hq, norm_mul, norm_mul, norm_fieldPhase, one_mul, one_mul]
    change ‖infraredBase Prod.fst (directionBase Prod.fst v (base F χ i)) p‖ ≤
      ‖v‖ * ‖infraredBase Prod.fst (omegaBase F χ i) p‖
    simp only [infraredBase, norm_smul]
    nlinarith [mul_le_mul_of_nonneg_left (directionBase_bound F χ i v p)
      (norm_nonneg ((Real.sqrt ‖p.1‖)⁻¹))]
  exact max_le
    (hfst.trans (mul_le_mul_of_nonneg_left (norm_fst_le _) (norm_nonneg v)))
    (hsnd.trans (mul_le_mul_of_nonneg_left (norm_snd_le _) (norm_nonneg v)))

theorem directionKernel_uniform_bound (i : Fin 3) (v x : FieldSpace) :
    ‖directionKernel F χ hUV i v x‖ ≤ ‖v‖ *
      PhysicalProfiles.kernelBound (omegaFactors F χ hUV) rfl (LinearIsometryEquiv.refl ℝ _) :=
  (directionKernel_norm_le F χ hUV i v x).trans
    (mul_le_mul_of_nonneg_left (omegaKernel_uniform_bound F χ hUV i x) (norm_nonneg v))



/-- Differentiating the translated real family preserves the physical
real structure in an arbitrary transverse frame. -/
theorem directionKernel_fixed (i : Fin 3) (v x : FieldSpace) :
    F.conjugation (directionKernel F χ hUV i v x).val.1 =
      (directionKernel F χ hUV i v x).val.1 := by
  rw [directionKernel_fst]
  apply F.conjugation_toLp_fixed (momentumKernel_memLp Prod.fst measurable_fst
    (directionBase Prod.fst v (base F χ i))
    (directionBase_measurable Prod.fst measurable_fst v _ (base_measurable F χ i))
    (directionBase_ultraviolet F χ hUV i v) x)
  have he : momentumKernel Prod.fst (directionBase Prod.fst v (base F χ i)) x =
      fun p : PhotonMode => (-Complex.I * (inner ℝ p.1 v : ℂ)) *
        momentumKernel Prod.fst (base F χ i) x p := by
    funext p
    simp only [momentumKernel, directionBase]
    ring
  change frameConjugation F (momentumKernel Prod.fst (directionBase Prod.fst v (base F χ i)) x)
    =ᵐ[photonMeasure] momentumKernel Prod.fst (directionBase Prod.fst v (base F χ i)) x
  rw [he]
  filter_upwards [momentumKernel_real F χ i x] with p hp
  rw [frameConjugation_mul F (fun k => -Complex.I * (inner ℝ k v : ℂ))
    (momentumKernel Prod.fst (base F χ i) x) p (by
      simp only [inner_neg_left, Complex.ofReal_neg, map_mul, map_neg,
        Complex.conj_I, Complex.conj_ofReal]
      ring), hp]



theorem directionKernel_real_smul (i : Fin 3) (v x : FieldSpace) (c : ℝ) :
    directionKernel F χ hUV i (c • v) x = c • directionKernel F χ hUV i v x :=
  (physicalKernel_hasLineDerivAt F χ hUV i (c • v) x).unique
    ((physicalKernel_hasLineDerivAt F χ hUV i v x).smul c)

end PfHk.PhysicalFieldRegularity
