import GptLean.Repair.FiniteCoordinateMollification
import GptLean.Repair.CovariantProduct
import GptLean.SymmetricLift.WeakDerivativeClosure

/-!
The weak product rule for a general form-domain source and a weakly
differentiable scalar multiplier. The multiplier derivative can be
unbounded. Only its product with the source must be locally square
integrable. Mollification of the scalar multiplier proves the weak
identity, with the derivative term passed in L1 by the L2 pairing bound.
No weighted approximation of the source is assumed.
-/

noncomputable section

namespace GptLean.Repair

open MeasureTheory Filter GptLean.SymmetricLift
open scoped ENNReal Topology ContDiff

section Pairing

variable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

private def scalarVectorPair (f : X → E) (k : Lp ℝ 2 μ) : E :=
  ∫ x, k x • f x ∂μ

private theorem scalarVectorPair_norm {f : X → E} (hf : MemLp f 2 μ)
    (k : Lp ℝ 2 μ) :
    ‖scalarVectorPair f k‖ ≤ ‖k‖ * ‖hf.toLp f‖ := by
  have h := norm_l2TestIntegral_le (Lp.memLp k) (hf.toLp f)
  rw [Lp.toLp_coeFn] at h
  convert h using 1
  congr 1
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

private theorem scalarVectorPair_sub {f : X → E} (hf : MemLp f 2 μ)
    (k l : Lp ℝ 2 μ) :
    scalarVectorPair f (k - l) = scalarVectorPair f k - scalarVectorPair f l := by
  unfold scalarVectorPair
  calc
    (∫ x, (k - l) x • f x ∂μ) = ∫ x, (k x - l x) • f x ∂μ := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub k l] with x hx
      rw [hx]
      rfl
    _ = _ := by
      simp only [sub_smul]
      exact integral_sub (memLp_one_iff_integrable.mp (hf.smul (Lp.memLp k)))
        (memLp_one_iff_integrable.mp (hf.smul (Lp.memLp l)))

private theorem scalarVectorPair_continuous {f : X → E} (hf : MemLp f 2 μ) :
    Continuous (scalarVectorPair f : Lp ℝ 2 μ → E) := by
  apply LipschitzWith.continuous (K := ‖hf.toLp f‖₊)
  apply LipschitzWith.of_dist_le_mul
  intro k l
  rw [dist_eq_norm, dist_eq_norm, ← scalarVectorPair_sub hf]
  simpa only [coe_nnnorm, mul_comm] using scalarVectorPair_norm hf (k - l)

/-- Pairing against a fixed vector-valued L2 function is continuous in
the scalar L2 argument. This permits an unbounded weak derivative. -/
theorem tendsto_integral_scalar_smul_of_eLpNorm
    {f : X → E} (hf : MemLp f 2 μ) {kn : ℕ → X → ℝ} {k : X → ℝ}
    (hkn : ∀ n, MemLp (kn n) 2 μ) (hk : MemLp k 2 μ)
    (hlim : Tendsto (fun n => eLpNorm (kn n - k) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, kn n x • f x ∂μ) atTop
      (𝓝 (∫ x, k x • f x ∂μ)) := by
  have hLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' kn hkn k hk).mpr hlim
  have h := ((scalarVectorPair_continuous hf).tendsto (hk.toLp k)).comp hLp
  have he (g : X → ℝ) (hg : MemLp g 2 μ) :
      scalarVectorPair f (hg.toLp g) = ∫ x, g x • f x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with x hx
    rw [hx]
  change Tendsto (fun n => scalarVectorPair f ((hkn n).toLp (kn n))) atTop
    (𝓝 (scalarVectorPair f (hk.toLp k))) at h
  simpa only [he] using h

end Pairing

section WeakProduct

variable {I : Type*} [Fintype I] [DecidableEq I] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

private theorem continuous_memLp_top_on_compact
    {f : EuclideanSpace ℝ I → ℝ} (hf : Continuous f)
    {K : Set (EuclideanSpace ℝ I)} (hK : IsCompact K) :
    MemLp f ∞ (volume.restrict K) := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  apply memLp_top_of_bound hf.aestronglyMeasurable.restrict C
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  exact hC x hx

/-- The scalar and source can both have only weak derivatives. The three
weighted L2 conditions concern their actual products and do not require
a uniform bound on the multiplier derivative. -/
theorem weakH1Local_real_smul_of_weighted
    {k : EuclideanSpace ℝ I → ℝ}
    {dk : I → EuclideanSpace ℝ I → ℝ}
    {f : EuclideanSpace ℝ I → E}
    {df : I → EuclideanSpace ℝ I → E}
    (hk : HasWeakH1Local k dk) (hf : HasWeakH1Local f df)
    (hvalue : ∀ K, IsCompact K → MemLp (fun x => k x • f x) 2 (volume.restrict K))
    (hsource : ∀ i K, IsCompact K →
      MemLp (fun x => k x • df i x) 2 (volume.restrict K))
    (hweight : ∀ i K, IsCompact K →
      MemLp (fun x => dk i x • f x) 2 (volume.restrict K)) :
    HasWeakH1Local (fun x => k x • f x)
      (fun i x => k x • df i x + dk i x • f x) := by
  refine ⟨hvalue, fun i K hK => (hsource i K hK).add (hweight i K hK), ?_⟩
  intro i φ hφ hs
  let K := tsupport φ
  let ν := volume.restrict K
  let v := EuclideanSpace.single i (1 : ℝ)
  let φ' := fun x => fderiv ℝ φ x v
  have hφ' : Continuous φ' := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφ2 := continuous_memLp_top_on_compact hφ.continuous hs
  have hφ'2 := continuous_memLp_top_on_compact hφ' hs
  have hc₁ : MemLp (fun x => φ x • df i x) 2 ν :=
    (hf.derivative_memLp i K hs).smul hφ2
  have hc₂ : MemLp (fun x => φ x • f x) 2 ν :=
    (hf.function_memLp K hs).smul hφ2
  have hc₃ : MemLp (fun x => φ' x • f x) 2 ν :=
    (hf.function_memLp K hs).smul hφ'2
  have hki := finite_localMemLp_two_locallyIntegrable hk.function_memLp
  have hdki := finite_localMemLp_two_locallyIntegrable (hk.derivative_memLp i)
  let kn := finiteMollification k
  let dkn := finiteMollification (dk i)
  have hkn (n : ℕ) : ContDiff ℝ ∞ (kn n) := finiteMollification_contDiff hki n
  have hdkn (n : ℕ) (x) : fderiv ℝ (kn n) x v = dkn n x := by
    exact ((hkn n).differentiable (by simp) x).lineDeriv_eq_fderiv.symm.trans
      (finiteMollification_hasLineDerivAt hki (hk.weak i) n x).lineDeriv
  have hkn2 (n : ℕ) : MemLp (kn n) 2 ν :=
    finiteMollification_memLp_two_restrict hki n hs
  have hdkn2 (n : ℕ) : MemLp (dkn n) 2 ν :=
    finiteMollification_memLp_two_restrict hdki n hs
  have hlim := finiteMollification_tendsto_eLpNorm_sub hk.function_memLp hs
  have hdlim := finiteMollification_tendsto_eLpNorm_sub (hk.derivative_memLp i) hs
  have ht₁ := tendsto_integral_scalar_smul_of_eLpNorm hc₁ hkn2 (hk.function_memLp K hs) hlim
  have ht₂ := tendsto_integral_scalar_smul_of_eLpNorm hc₂ hdkn2
    (hk.derivative_memLp i K hs) hdlim
  have ht₃ := tendsto_integral_scalar_smul_of_eLpNorm hc₃ hkn2 (hk.function_memLp K hs) hlim
  have hrestrict (g : EuclideanSpace ℝ I → E) :
      (∫ x, φ x • g x) = ∫ x, φ x • g x ∂ν :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (s := K)
      (fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx, zero_smul])).symm
  have hdrestrict (g : EuclideanSpace ℝ I → E) :
      (∫ x, φ' x • g x) = ∫ x, φ' x • g x ∂ν :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (s := K)
      (fun x hx => by dsimp [φ']; rw [fderiv_of_notMem_tsupport ℝ hx]; simp)).symm
  have he (n : ℕ) :
      (∫ x, kn n x • (φ x • df i x) ∂ν) +
        (∫ x, dkn n x • (φ x • f x) ∂ν) =
      -(∫ x, kn n x • (φ' x • f x) ∂ν) := by
    have hw := (weakH1Local_smooth_real_smul hf (hkn n)).weak i φ hφ hs
    change (∫ x, φ x • (kn n x • df i x + fderiv ℝ (kn n) x v • f x)) =
      -(∫ x, φ' x • (kn n x • f x)) at hw
    rw [hrestrict, hdrestrict] at hw
    simp_rw [hdkn, smul_add] at hw
    have h₁ : Integrable (fun x => kn n x • (φ x • df i x)) ν :=
      memLp_one_iff_integrable.mp (hc₁.smul (hkn2 n))
    have h₂ : Integrable (fun x => dkn n x • (φ x • f x)) ν :=
      memLp_one_iff_integrable.mp (hc₂.smul (hdkn2 n))
    simp_rw [smul_comm (φ _) (kn n _), smul_comm (φ _) (dkn n _)] at hw
    rw [integral_add h₁ h₂] at hw
    rw [show (∫ x, φ' x • (kn n x • f x) ∂ν) =
      (∫ x, kn n x • (φ' x • f x) ∂ν) from
      integral_congr_ae (Eventually.of_forall fun x => smul_comm (φ' x) (kn n x) (f x))] at hw
    exact hw
  have htarget := tendsto_nhds_unique (ht₁.add ht₂)
    (ht₃.neg.congr' (Eventually.of_forall fun n => (he n).symm))
  change (∫ x, φ x • (k x • df i x + dk i x • f x)) =
    -(∫ x, φ' x • (k x • f x))
  rw [hrestrict, hdrestrict]
  simp only [smul_add]
  simp_rw [smul_comm (φ _) (k _), smul_comm (φ _) (dk i _)]
  have hi₁ : Integrable (fun x => k x • (φ x • df i x)) ν :=
    memLp_one_iff_integrable.mp (hc₁.smul (hk.function_memLp K hs))
  have hi₂ : Integrable (fun x => dk i x • (φ x • f x)) ν :=
    memLp_one_iff_integrable.mp (hc₂.smul (hk.derivative_memLp i K hs))
  rw [integral_add hi₁ hi₂]
  rw [show (∫ x, φ' x • (k x • f x) ∂ν) =
    (∫ x, k x • (φ' x • f x) ∂ν) from
    integral_congr_ae (Eventually.of_forall fun x => smul_comm (φ' x) (k x) (f x))]
  exact htarget

end WeakProduct

section Complex

variable {X H : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem memLp_re_smul {k : X → ℂ} {f : X → H}
    (hk : AEStronglyMeasurable k μ) (hf : AEStronglyMeasurable f μ)
    (h : MemLp (fun x => k x • f x) 2 μ) :
    MemLp (fun x => (k x).re • f x) 2 μ := by
  apply h.mono (hk.re.smul hf)
  exact Eventually.of_forall fun x => by
    change ‖(k x).re • f x‖ ≤ ‖k x • f x‖
    simp only [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm (k x)) (norm_nonneg (f x))

private theorem memLp_im_smul {k : X → ℂ} {f : X → H}
    (hk : AEStronglyMeasurable k μ) (hf : AEStronglyMeasurable f μ)
    (h : MemLp (fun x => k x • f x) 2 μ) :
    MemLp (fun x => (k x).im • f x) 2 μ := by
  apply h.mono (hk.im.smul hf)
  exact Eventually.of_forall fun x => by
    change ‖(k x).im • f x‖ ≤ ‖k x • f x‖
    simp only [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm (k x)) (norm_nonneg (f x))

private theorem re_im_smul (c : ℂ) (u : H) :
    c.re • u + Complex.I • (c.im • u) = c • u := by
  calc
    c.re • u + Complex.I • (c.im • u) =
        ((c.re : ℂ) + Complex.I * (c.im : ℂ)) • u := by
      rw [add_smul, Complex.coe_smul]
      congr 1
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
      rfl
    _ = c • u := by
      congr 1
      simpa only [mul_comm] using c.re_add_im

omit [MeasurableSpace X] in
/-- The complex product rule for a general weak H1 source. In particular,
the weighted derivative condition applies to collision-singular tensor
lift coordinates and does not require a bounded commutator on L2. -/
theorem weakH1Local_complex_smul_of_weighted {I : Type*} [Fintype I] [DecidableEq I]
    {k : EuclideanSpace ℝ I → ℂ}
    {dk : I → EuclideanSpace ℝ I → ℂ}
    {f : EuclideanSpace ℝ I → H}
    {df : I → EuclideanSpace ℝ I → H}
    (hk : HasWeakH1Local k dk) (hf : HasWeakH1Local f df)
    (hvalue : ∀ K, IsCompact K → MemLp (fun x => k x • f x) 2 (volume.restrict K))
    (hsource : ∀ i K, IsCompact K →
      MemLp (fun x => k x • df i x) 2 (volume.restrict K))
    (hweight : ∀ i K, IsCompact K →
      MemLp (fun x => dk i x • f x) 2 (volume.restrict K)) :
    HasWeakH1Local (fun x => k x • f x)
      (fun i x => k x • df i x + dk i x • f x) := by
  let L : H →L[ℝ] H := (Complex.I • ContinuousLinearMap.id ℂ H).restrictScalars ℝ
  have hr := weakH1Local_real_smul_of_weighted (weakH1Local_map Complex.reCLM hk) hf
    (fun K hK => memLp_re_smul (hk.function_memLp K hK).1
      (hf.function_memLp K hK).1 (hvalue K hK))
    (fun i K hK => memLp_re_smul (hk.function_memLp K hK).1
      (hf.derivative_memLp i K hK).1 (hsource i K hK))
    (fun i K hK => memLp_re_smul (hk.derivative_memLp i K hK).1
      (hf.function_memLp K hK).1 (hweight i K hK))
  have hi := weakH1Local_map L
    (weakH1Local_real_smul_of_weighted (weakH1Local_map Complex.imCLM hk) hf
      (fun K hK => memLp_im_smul (hk.function_memLp K hK).1
        (hf.function_memLp K hK).1 (hvalue K hK))
      (fun i K hK => memLp_im_smul (hk.function_memLp K hK).1
        (hf.derivative_memLp i K hK).1 (hsource i K hK))
      (fun i K hK => memLp_im_smul (hk.derivative_memLp i K hK).1
        (hf.function_memLp K hK).1 (hweight i K hK)))
  apply (weakH1Local_add hr hi).congr
  · exact Eventually.of_forall fun x => re_im_smul _ _
  · intro i
    apply Eventually.of_forall
    intro x
    change (k x).re • df i x + (dk i x).re • f x +
      Complex.I • ((k x).im • df i x + (dk i x).im • f x) = _
    rw [smul_add]
    calc
      _ = ((k x).re • df i x + Complex.I • ((k x).im • df i x)) +
          ((dk i x).re • f x + Complex.I • ((dk i x).im • f x)) := by abel
      _ = _ := by rw [re_im_smul, re_im_smul]

end Complex

end GptLean.Repair
