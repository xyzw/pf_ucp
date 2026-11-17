import GptLean.WeylCoherentPhase

/-! The weak complex coherent chain rule, including its locally integrable
Berry term and the exact criterion for a locally square-integrable derivative. -/

noncomputable section

namespace GptLean.Representability

open MeasureTheory Filter SymmetricLift PhysicalFock
open scoped ENNReal Topology InnerProductSpace ContDiff

set_option Elab.async false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types true

structure HasWeakW11Local {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : CoherentBase d → E) (df : Fin d → CoherentBase d → E) : Prop where
  function_integrable : ∀ K, IsCompact K → Integrable f (volume.restrict K)
  derivative_integrable : ∀ i K, IsCompact K → Integrable (df i) (volume.restrict K)
  weak : ∀ i, WeakDirectionalIdentity f (df i) (EuclideanSpace.single i 1)

namespace ConcreteWeylLaw

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]
  (W : ConcreteWeylLaw μ) {d : ℕ}
  {f : CoherentBase d → Lp ℂ 2 μ} {df : Fin d → CoherentBase d → Lp ℂ 2 μ}
  {S : CoherentBase d → ℝ} {dS : Fin d → CoherentBase d → ℝ}
  (hf : HasWeakH1Local f df) (hS : HasWeakH1Local S dS)

include hf hS

private theorem phase_measurable :
    AEStronglyMeasurable (fun x => W.phaseCoherent μ (S x) (f x)) volume := by
  have hs : AEStronglyMeasurable S volume :=
    (localMemLp_two_locallyIntegrable hS.function_memLp).aestronglyMeasurable
  have hh : AEStronglyMeasurable f volume :=
    (localMemLp_two_locallyIntegrable hf.function_memLp).aestronglyMeasurable
  have h := (W.phaseCoherent_continuous μ).comp_aestronglyMeasurable (hs.prodMk hh)
  exact h

private theorem horizontal_measurable (i : Fin d) :
    AEStronglyMeasurable (fun x => W.phaseHorizontal μ (S x) (f x) (df i x)) volume := by
  have hs : AEStronglyMeasurable S volume :=
    (localMemLp_two_locallyIntegrable hS.function_memLp).aestronglyMeasurable
  have hh : AEStronglyMeasurable f volume :=
    (localMemLp_two_locallyIntegrable hf.function_memLp).aestronglyMeasurable
  have hd : AEStronglyMeasurable (df i) volume :=
    (localMemLp_two_locallyIntegrable (hf.derivative_memLp i)).aestronglyMeasurable
  have h := (W.phaseHorizontal_continuous μ).comp_aestronglyMeasurable ((hs.prodMk hh).prodMk hd)
  exact h

theorem phaseCoherent_localMemLp (K : Set (CoherentBase d)) (hK : IsCompact K) :
    MemLp (fun x => W.phaseCoherent μ (S x) (f x)) 2 (volume.restrict K) := by
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  exact MemLp.of_bound (phase_measurable μ W hf hS).restrict 1
    (ae_of_all _ fun x => (W.phaseCoherent_norm μ (S x) (f x)).le)

theorem phaseHorizontal_localMemLp (i : Fin d) (K : Set (CoherentBase d)) (hK : IsCompact K) :
    MemLp (fun x => W.phaseHorizontal μ (S x) (f x) (df i x)) 2 (volume.restrict K) :=
  (hf.derivative_memLp i K hK).mono (horizontal_measurable μ W hf hS i).restrict
    (ae_of_all _ fun x => (W.phaseHorizontal μ (S x) (f x)).norm_map (df i x) |>.le)

omit [SigmaFinite μ] in
theorem phaseBerry_integrable (i : Fin d) (K : Set (CoherentBase d)) (hK : IsCompact K) :
    Integrable (fun x => dS i x + (⟪f x, df i x⟫_ℂ).im) (volume.restrict K) := by
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  exact (hS.derivative_memLp i K hK).integrable (by norm_num) |>.add
    (memLp_one_iff_integrable.mp ((berryBilinear μ).memLp_of_bilin 1
      (hf.function_memLp K hK) (hf.derivative_memLp i K hK)))

omit hf hS in
private theorem phaseI_norm (s : ℝ) (h : Lp ℂ 2 μ) :
    ‖Complex.I • W.phaseCoherent μ s h‖ = 1 := by
  rw [norm_smul, Complex.norm_I, W.phaseCoherent_norm, mul_one]

theorem phaseCoherentDerivative_integrable (i : Fin d) (K : Set (CoherentBase d))
    (hK : IsCompact K) :
    Integrable (fun x => W.phaseCoherentDerivative μ (S x) (f x) (dS i x) (df i x))
      (volume.restrict K) := by
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hB := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Fock μ →L[ℝ] Fock μ).integrable_of_bilin_of_bdd_right 1 (phaseBerry_integrable μ hf hS i K hK)
      ((phase_measurable μ W hf hS).const_smul Complex.I).restrict
      (ae_of_all _ fun x => (phaseI_norm μ W (S x) (f x)).le)
  exact ((phaseHorizontal_localMemLp μ W hf hS i K hK).integrable (by norm_num) |>.add hB).congr
    (ae_of_all _ fun x => (W.phaseCoherentDerivative_split μ (S x) (f x) (dS i x) (df i x)).symm)

/-- The weak chain rule with the full complex Berry term. The input and its
derivative are only locally L2, so the output derivative is first obtained in L1. -/
theorem phaseCoherent_weakW11 :
    HasWeakW11Local (fun x => W.phaseCoherent μ (S x) (f x))
      (fun i x => W.phaseCoherentDerivative μ (S x) (f x) (dS i x) (df i x)) := by
  refine ⟨fun K hK => ?_, phaseCoherentDerivative_integrable μ W hf hS, ?_⟩
  · let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
    exact (phaseCoherent_localMemLp μ W hf hS K hK).integrable (by norm_num)
  intro i φ hφ hs
  let : SecondCountableTopologyEither (CoherentBase d) (Fock μ) := ⟨Or.inl inferInstance⟩
  let : SecondCountableTopologyEither (CoherentBase d) (Lp ℂ 2 μ) := ⟨Or.inl inferInstance⟩
  let K := tsupport φ
  have hK : IsCompact K := hs
  let ν := volume.restrict K
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hfi : LocallyIntegrable f volume := localMemLp_two_locallyIntegrable hf.function_memLp
  have hdfi : LocallyIntegrable (df i) volume := localMemLp_two_locallyIntegrable (hf.derivative_memLp i)
  have hSi : LocallyIntegrable S volume := localMemLp_two_locallyIntegrable hS.function_memLp
  have hdSi : LocallyIntegrable (dS i) volume := localMemLp_two_locallyIntegrable (hS.derivative_memLp i)
  let fn := boundedMollification f
  let dfn := boundedMollification (df i)
  let Sn := boundedMollification S
  let dSn := boundedMollification (dS i)
  have hfn (n) := boundedMollification_contDiff hfi n
  have hdfn (n) := boundedMollification_contDiff hdfi n
  have hSn (n) := boundedMollification_contDiff hSi n
  have hdSn (n) := boundedMollification_contDiff hdSi n
  let un n x := W.phaseCoherent μ (Sn n x) (fn n x)
  let u x := W.phaseCoherent μ (S x) (f x)
  let an n x := W.phaseHorizontal μ (Sn n x) (fn n x) (dfn n x)
  let a x := W.phaseHorizontal μ (S x) (f x) (df i x)
  let bn n x := dSn n x + (⟪fn n x, dfn n x⟫_ℂ).im
  let b x := dS i x + (⟪f x, df i x⟫_ℂ).im
  let cn n x := Complex.I • un n x
  let c x := Complex.I • u x
  have hun (n) : Continuous (un n) := (W.phaseCoherent_continuous μ).comp (f := fun x => (Sn n x, fn n x))
    ((hSn n).continuous.prodMk (hfn n).continuous)
  have han (n) : Continuous (an n) := (W.phaseHorizontal_continuous μ).comp (f := fun x => ((Sn n x, fn n x), dfn n x))
    (((hSn n).continuous.prodMk (hfn n).continuous).prodMk (hdfn n).continuous)
  have hbn (n) : Continuous (bn n) := (hdSn n).continuous.add
    (Complex.continuous_im.comp ((hfn n).continuous.inner (hdfn n).continuous))
  have hcn (n) : Continuous (cn n) := (hun n).const_smul Complex.I
  have hum : AEStronglyMeasurable u volume := phase_measurable μ W hf hS
  have ham : AEStronglyMeasurable a volume := horizontal_measurable μ W hf hS i
  have hcm : AEStronglyMeasurable c volume := hum.const_smul Complex.I
  have hbm : AEStronglyMeasurable b volume := hdSi.aestronglyMeasurable.add
    (Complex.continuous_im.comp_aestronglyMeasurable
      (hfi.aestronglyMeasurable.inner hdfi.aestronglyMeasurable))
  have hun2 (n) : MemLp (un n) 2 ν := MemLp.of_bound (hun n).aestronglyMeasurable.restrict 1
    (ae_of_all _ fun x => (W.phaseCoherent_norm μ (Sn n x) (fn n x)).le)
  have hu2 : MemLp u 2 ν := phaseCoherent_localMemLp μ W hf hS K hK
  have han2 (n) : MemLp (an n) 2 ν :=
    (boundedMollification_memLp_two_restrict hdfi n hK).mono
      (han n).aestronglyMeasurable.restrict
      (ae_of_all _ fun x => (W.phaseHorizontal μ (Sn n x) (fn n x)).norm_map (dfn n x) |>.le)
  have ha2 : MemLp a 2 ν := phaseHorizontal_localMemLp μ W hf hS i K hK
  have hbn1 (n) : Integrable (bn n) ν :=
    (boundedMollification_memLp_two_restrict hdSi n hK).integrable (by norm_num) |>.add
      (memLp_one_iff_integrable.mp ((berryBilinear μ).memLp_of_bilin 1
        (boundedMollification_memLp_two_restrict hfi n hK)
        (boundedMollification_memLp_two_restrict hdfi n hK)))
  have hb1 : Integrable b ν := phaseBerry_integrable μ hf hS i K hK
  have hulim_ae : ∀ᵐ x ∂ν, Tendsto (fun n => un n x) atTop (𝓝 (u x)) := by
    filter_upwards [ae_restrict_le (boundedMollification_ae_tendsto hSi),
      ae_restrict_le (boundedMollification_ae_tendsto hfi)] with x h₁ h₂
    have ht := ((W.phaseCoherent_continuous μ).tendsto (S x, f x)).comp (h₁.prodMk_nhds h₂)
    exact ht
  have hclim_ae : ∀ᵐ x ∂ν, Tendsto (fun n => cn n x) atTop (𝓝 (c x)) :=
    hulim_ae.mono fun x hx => hx.const_smul Complex.I
  have hulim : Tendsto (fun n => eLpNorm (un n - u) 2 ν) atTop (𝓝 0) := by
    apply tendsto_eLpNorm_two_of_dominated_sq (fun n => (hun2 n).1) hu2.1 (integrable_const 1)
    · exact fun n => ae_of_all _ fun x => by
        change ‖W.phaseCoherent μ (Sn n x) (fn n x)‖ ^ 2 ≤ (1 : ℝ)
        rw [W.phaseCoherent_norm]; norm_num
    · exact ae_of_all _ fun x => by
        change ‖W.phaseCoherent μ (S x) (f x)‖ ^ 2 ≤ (1 : ℝ)
        rw [W.phaseCoherent_norm]; norm_num
    · exact hulim_ae
  have halim : Tendsto (fun n => eLpNorm (an n - a) 2 ν) atTop (𝓝 0) := by
    have hfixed (n) : AEStronglyMeasurable
        (fun x => W.phaseHorizontal μ (Sn n x) (fn n x) (df i x)) ν := by
      have hm := (W.phaseHorizontal_continuous μ).comp_aestronglyMeasurable
        (((hSn n).continuous.aestronglyMeasurable.prodMk
          (hfn n).continuous.aestronglyMeasurable).prodMk hdfi.aestronglyMeasurable)
      exact hm.restrict
    have hpoint : ∀ᵐ x ∂ν, Tendsto
        (fun n => W.phaseHorizontal μ (Sn n x) (fn n x) (df i x)) atTop
          (𝓝 (W.phaseHorizontal μ (S x) (f x) (df i x))) := by
      filter_upwards [ae_restrict_le (boundedMollification_ae_tendsto hSi),
        ae_restrict_le (boundedMollification_ae_tendsto hfi)] with x h₁ h₂
      have ht := ((W.phaseHorizontal_continuous μ).tendsto ((S x, f x), df i x)).comp
        ((h₁.prodMk_nhds h₂).prodMk_nhds (tendsto_const_nhds (x := df i x)))
      exact ht
    exact isometry_apply_tendsto_eLpNorm_two
      (fun n x => W.phaseHorizontal μ (Sn n x) (fn n x))
      (fun x => W.phaseHorizontal μ (S x) (f x)) (hf.derivative_memLp i K hK)
      (fun n => (han n).aestronglyMeasurable.restrict) hfixed ham.restrict
      (boundedMollification_tendsto_eLpNorm_sub (hf.derivative_memLp i) hK) hpoint
  have hblim : Tendsto (fun n => eLpNorm (bn n - b) 1 ν) atTop (𝓝 0) := by
    have hdS2 := boundedMollification_tendsto_eLpNorm_sub (hS.derivative_memLp i) hK
    have hds1 := bilinear_tendsto_eLpNorm_one (ContinuousLinearMap.mul ℝ ℝ)
      (fun _ => (memLp_const (1 : ℝ) : MemLp (fun _ : CoherentBase d => (1 : ℝ)) 2 ν))
      (memLp_const (1 : ℝ))
      (fun n => boundedMollification_memLp_two_restrict hdSi n hK)
      (hS.derivative_memLp i K hK)
      (by simp only [sub_self, eLpNorm_zero]; exact tendsto_const_nhds) hdS2
    simp only [ContinuousLinearMap.mul_apply', one_mul] at hds1
    have hberry := bilinear_tendsto_eLpNorm_one (berryBilinear μ)
      (fun n => boundedMollification_memLp_two_restrict hfi n hK) (hf.function_memLp K hK)
      (fun n => boundedMollification_memLp_two_restrict hdfi n hK) (hf.derivative_memLp i K hK)
      (boundedMollification_tendsto_eLpNorm_sub hf.function_memLp hK)
      (boundedMollification_tendsto_eLpNorm_sub (hf.derivative_memLp i) hK)
    exact tendsto_eLpNorm_add_one
      (fun n => memLp_one_iff_integrable.mpr
        ((boundedMollification_memLp_two_restrict hdSi n hK).integrable (by norm_num)))
      (fun n => (berryBilinear μ).memLp_of_bilin 1
        (boundedMollification_memLp_two_restrict hfi n hK)
        (boundedMollification_memLp_two_restrict hdfi n hK))
      (memLp_one_iff_integrable.mpr ((hS.derivative_memLp i K hK).integrable (by norm_num)))
      ((berryBilinear μ).memLp_of_bilin 1 (hf.function_memLp K hK) (hf.derivative_memLp i K hK))
      hds1 hberry
  let φ' := fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)
  have hφ' : Continuous φ' := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hmφ : MemLp φ 2 ν := (hφ.continuous.memLp_of_hasCompactSupport hs).restrict K
  have hmφ' : MemLp φ' 2 ν := (hφ'.memLp_of_hasCompactSupport (hs.fderiv_apply ℝ _)).restrict K
  have hz : ∀ x, x ∉ K → φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hz' : ∀ x, x ∉ K → φ' x = 0 := fun x hx => by simp [φ', fderiv_of_notMem_tsupport ℝ hx]
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn hφ.continuous.continuousOn
  let C := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  have hφbound (x) : ‖φ x‖ ≤ C := by
    by_cases hx : x ∈ K
    · exact (hC₀ x hx).trans (le_max_left _ _)
    · rw [hz x hx, norm_zero]; exact hC
  have htestcn (n) : AEStronglyMeasurable (fun x => φ x • cn n x) ν :=
    (hφ.continuous.aestronglyMeasurable.smul (hcn n).aestronglyMeasurable).restrict
  have htestc : AEStronglyMeasurable (fun x => φ x • c x) ν :=
    (hφ.continuous.aestronglyMeasurable.smul hcm).restrict
  have htestcn_bound (n x) : ‖φ x • cn n x‖ ≤ C := by
    rw [norm_smul, phaseI_norm, mul_one]; exact hφbound x
  have htestc_bound (x) : ‖φ x • c x‖ ≤ C := by
    rw [norm_smul, phaseI_norm, mul_one]; exact hφbound x
  have hBn (n) : Integrable (fun x => bn n x • (φ x • cn n x)) ν :=
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Fock μ →L[ℝ] Fock μ).integrable_of_bilin_of_bdd_right C (hbn1 n) (htestcn n) (ae_of_all _ (htestcn_bound n))
  have hB : Integrable (fun x => b x • (φ x • c x)) ν :=
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Fock μ →L[ℝ] Fock μ).integrable_of_bilin_of_bdd_right C hb1 htestc (ae_of_all _ htestc_bound)
  have hBlim := bounded_smul_tendsto_eLpNorm_one hbn1 hb1 htestcn htestc C hC
    htestcn_bound htestc_bound hblim
    (hclim_ae.mono fun x hx => tendsto_const_nhds.smul hx)
  have hBint := tendsto_integral_of_L1' _ hB.aestronglyMeasurable
    (Eventually.of_forall hBn) hBlim
  have hAint := tendsto_integral_l2_test_of_eLpNorm hmφ han2 ha2 halim
  have hUint := tendsto_integral_l2_test_of_eLpNorm hmφ' hun2 hu2 hulim
  have hsum_integral (A B C : CoherentBase d → Fock μ) (a : CoherentBase d → ℝ)
      (hA : Integrable (fun x => φ x • A x) ν)
      (hB : Integrable (fun x => a x • (φ x • B x)) ν)
      (he : ∀ x, C x = A x + a x • B x) :
      (∫ x in K, φ x • C x) =
        (∫ x in K, φ x • A x) + ∫ x in K, a x • (φ x • B x) := by
    refine (integral_congr_ae (ae_of_all _ fun x => by rw [he x, smul_add, smul_comm (φ x) (a x)])).trans
      (integral_add hA hB)
  have hweak (n) : (∫ x in K, φ x • an n x) + (∫ x in K, bn n x • (φ x • cn n x)) =
      -(∫ x in K, φ' x • un n x) := by
    let dn x := W.phaseCoherentDerivative μ (Sn n x) (fn n x) (dSn n x) (dfn n x)
    have hdn : Integrable (fun x => φ x • dn x) ν := by
      refine ((memLp_one_iff_integrable.mp ((han2 n).smul hmφ)).add (hBn n)).congr ?_
      exact ae_of_all _ fun x => by
        change φ x • an n x + bn n x • (φ x • cn n x) =
          φ x • W.phaseCoherentDerivative μ (Sn n x) (fn n x) (dSn n x) (dfn n x)
        rw [W.phaseCoherentDerivative_split, smul_add]
        exact congrArg (fun z => φ x • an n x + z) (smul_comm (bn n x) (φ x) (cn n x))
    have hdn_global : Integrable (fun x => φ x • dn x) volume :=
      (integrableOn_iff_integrable_of_support_subset (fun x hx => by
        by_contra h
        exact hx (by change φ x • dn x = 0; rw [hz x h, zero_smul]))).mp hdn
    have hi := integral_smul_lineDeriv_eq_neg_of_ae_regularLine (D := Set.univ)
      (f := un n) (f' := dn)
      (ae_of_all _ fun _ _ => Set.mem_univ _) (fun x _ => ?_)
      (fun x => (hφ.differentiable (by simp) x).hasFDerivAt.hasLineDerivAt _)
      (integrable_smul_of_memLp_on_support hmφ' (hun2 n) hz') hdn_global
      (integrable_smul_of_memLp_on_support hmφ (hun2 n) hz)
    · rw [integral_smul_eq_setIntegral _ hz, integral_smul_eq_setIntegral _ hz'] at hi
      exact (hsum_integral (an n) (cn n) dn (bn n)
        (memLp_one_iff_integrable.mp ((han2 n).smul hmφ)) (hBn n)
          (fun x => W.phaseCoherentDerivative_split μ (Sn n x) (fn n x) (dSn n x) (dfn n x))).symm.trans hi
    · have h₁ := boundedMollification_hasLineDerivAt hSi (hS.weak i) n x
      have h₂ := boundedMollification_hasLineDerivAt hfi (hf.weak i) n x
      simpa only [HasLineDerivAt, zero_smul, add_zero] using
        W.phaseCoherent_hasDerivAt μ h₁ h₂
  have hfinal := tendsto_nhds_unique (hAint.add hBint)
    (hUint.neg.congr' (Eventually.of_forall fun n => (hweak n).symm))
  rw [integral_smul_eq_setIntegral _ hz, integral_smul_eq_setIntegral _ hz']
  exact (hsum_integral a c _ b (memLp_one_iff_integrable.mp (ha2.smul hmφ)) hB
    (fun x => W.phaseCoherentDerivative_split μ (S x) (f x) (dS i x) (df i x))).trans hfinal

/-- Local square integrability of the total Berry connection upgrades the
constructed weak derivative from W1,1 to H1. -/
theorem phaseCoherent_weakH1
    (hberry : ∀ i K, IsCompact K →
      MemLp (fun x => dS i x + (⟪f x, df i x⟫_ℂ).im) 2 (volume.restrict K)) :
    HasWeakH1Local (fun x => W.phaseCoherent μ (S x) (f x))
      (fun i x => W.phaseCoherentDerivative μ (S x) (f x) (dS i x) (df i x)) := by
  refine ⟨phaseCoherent_localMemLp μ W hf hS, ?_, (phaseCoherent_weakW11 μ W hf hS).weak⟩
  intro i K hK
  apply memLp_two_of_sq_norm_le
    (phaseCoherentDerivative_integrable μ W hf hS i K hK).aestronglyMeasurable
    (((hf.derivative_memLp i K hK).integrable_norm_pow (by norm_num)).add
      ((hberry i K hK).integrable_norm_pow (by norm_num)))
  exact ae_of_all _ fun x => by
    simp only [W.phaseCoherentDerivative_metric, Pi.add_apply, Real.norm_eq_abs, sq_abs, le_refl]

end ConcreteWeylLaw

end GptLean.Representability
