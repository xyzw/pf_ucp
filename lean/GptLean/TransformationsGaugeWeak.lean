import GptLean.TransformationsPhase
import GptLean.ElectronicH1Complex
import GptLean.Repair.WeakMultiplierProduct
import GptLean.RepresentabilityCoherentSobolev

/-!
Weak electronic gauge phases with unbounded derivatives.

The phase chain rule uses only local integrability of the angle and local
square integrability of its weak derivatives. The action on the electronic
H1 graph requires square integrability of the actual gradient times source.
Neither statement requires a uniform bound on the gradient.
-/

noncomputable section

namespace GptLean.TransformationsGauge

open MeasureTheory Filter SymmetricLift Repair TransformationsPhase
open scoped ENNReal Topology ContDiff

set_option Elab.async false
set_option maxHeartbeats 800000

section WeakPhase

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The real derivative of the complex exponential on the imaginary axis. -/
def phaseDerivative (t : ℝ) : ℝ →L[ℝ] ℂ :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight
    (Complex.exp ((t : ℂ) * Complex.I) * Complex.I)

theorem phaseDerivative_apply (t r : ℝ) :
    phaseDerivative t r = Complex.exp ((t : ℂ) * Complex.I) * (Complex.I * (r : ℂ)) := by
  simp only [phaseDerivative, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, Complex.real_smul]
  ring

theorem phaseDerivative_continuous : Continuous phaseDerivative := by
  exact (ContinuousLinearMap.smulRightL ℝ ℝ ℂ (ContinuousLinearMap.id ℝ ℝ)).continuous.comp
    (by fun_prop)

theorem phaseDerivative_norm (t r : ℝ) : ‖phaseDerivative t r‖ = ‖r‖ := by
  rw [phaseDerivative_apply, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I,
    Complex.norm_I, Complex.norm_real, one_mul, one_mul]

theorem finiteMollification_ae_tendsto {f : EuclideanSpace ℝ I → ℝ}
    (hf : LocallyIntegrable f volume) :
    ∀ᵐ x ∂volume, Tendsto (fun n => finiteMollification f n x) atTop (𝓝 (f x)) := by
  have h := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (finiteApproximationBump_rOut_tendsto (I := I))
    (Eventually.of_forall (fun n =>
      (show (finiteApproximationBump I n).rOut ≤ 2 * (finiteApproximationBump I n).rIn
        from le_rfl))) hf
  simpa only [finiteMollification, convolution_flip] using h

/-- The weak phase chain rule. This accepts a W1,1 local angle whenever its
weak derivatives are locally square integrable, including L3 + Linfinity. -/
theorem weak_phase_of_locallyIntegrable
    {g : EuclideanSpace ℝ I → ℝ} {dg : I → EuclideanSpace ℝ I → ℝ}
    (hg : LocallyIntegrable g volume)
    (hdg : ∀ i K, IsCompact K → MemLp (dg i) 2 (volume.restrict K))
    (hweak : ∀ i (φ : EuclideanSpace ℝ I → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, φ x * dg i x) = -(∫ x, fderiv ℝ φ x (EuclideanSpace.single i 1) * g x)) :
    HasWeakH1Local (factor g) (fun i x => phaseDerivative (g x) (dg i x)) := by
  let gn := finiteMollification g
  let dgn := fun i => finiteMollification (dg i)
  have hgn (n : ℕ) : ContDiff ℝ ∞ (gn n) := finiteMollification_contDiff hg n
  have hdgi (i : I) := finite_localMemLp_two_locallyIntegrable (hdg i)
  have hdgn (i : I) (n : ℕ) : ContDiff ℝ ∞ (dgn i n) :=
    finiteMollification_contDiff (hdgi i) n
  have hgm := hg.aestronglyMeasurable
  have hfm := factor_aestronglyMeasurable hgm
  have hdm (i : I) : AEStronglyMeasurable
      (fun x => phaseDerivative (g x) (dg i x)) volume :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      ((phaseDerivative_continuous.comp_aestronglyMeasurable hgm).prodMk
        (hdgi i).aestronglyMeasurable)
  have hfloc (K : Set (EuclideanSpace ℝ I)) (hK : IsCompact K) :
      MemLp (factor g) 2 (volume.restrict K) := by
    let : IsFiniteMeasure (volume.restrict K) :=
      isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
    exact MemLp.of_bound hfm.restrict 1 (ae_of_all _ fun x => (norm_factor g x).le)
  have hdloc (i : I) (K : Set (EuclideanSpace ℝ I)) (hK : IsCompact K) :
      MemLp (fun x => phaseDerivative (g x) (dg i x)) 2 (volume.restrict K) :=
    (hdg i K hK).mono (hdm i).restrict
      (ae_of_all _ fun x => (phaseDerivative_norm (g x) (dg i x)).le)
  refine ⟨hfloc, hdloc, ?_⟩
  intro i φ hφ hs
  let K := tsupport φ
  have hK : IsCompact K := hs
  let : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  let fn := fun n => factor (gn n)
  let dfn := fun n x => phaseDerivative (gn n x) (dgn i n x)
  have hfnm (n : ℕ) : AEStronglyMeasurable (fn n) volume :=
    factor_aestronglyMeasurable (hgn n).continuous.aestronglyMeasurable
  have hfn (n : ℕ) : MemLp (fn n) 2 (volume.restrict K) :=
    MemLp.of_bound (hfnm n).restrict 1
      (ae_of_all _ fun x => (norm_factor (gn n) x).le)
  have hdfn (n : ℕ) : MemLp (dfn n) 2 (volume.restrict K) :=
    (finiteMollification_memLp_two_restrict (hdgi i) n hK).mono
      (((phaseDerivative_continuous.comp (hgn n).continuous).clm_apply
        (hdgn i n).continuous).aestronglyMeasurable.restrict)
      (ae_of_all _ fun x => (phaseDerivative_norm (gn n x) (dgn i n x)).le)
  have hlim := finiteMollification_ae_tendsto hg
  have hflim : Tendsto (fun n => eLpNorm (fn n - factor g) 2 (volume.restrict K))
      atTop (𝓝 0) := by
    apply tendsto_eLpNorm_two_of_dominated_sq (fun n => (hfn n).1) hfm.restrict
      (integrable_const (1 : ℝ))
    · exact fun n => ae_of_all _ fun x => by simp only [fn, norm_factor, one_pow, le_refl]
    · exact ae_of_all _ fun x => by simp only [norm_factor, one_pow, le_refl]
    · filter_upwards [ae_restrict_le hlim] with x hx
      exact (show Continuous (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) by
        fun_prop).continuousAt.tendsto.comp hx
  have hdflim : Tendsto (fun n => eLpNorm
      (dfn n - fun x => phaseDerivative (g x) (dg i x)) 2 (volume.restrict K))
      atTop (𝓝 0) := by
    apply Representability.contraction_apply_tendsto_eLpNorm
      (fun n x => phaseDerivative (gn n x)) (fun x => phaseDerivative (g x))
      (fun n => (phaseDerivative_continuous.comp (hgn n).continuous).aestronglyMeasurable.restrict)
      (phaseDerivative_continuous.comp_aestronglyMeasurable hgm).restrict
      (fun n x v => (phaseDerivative_norm (gn n x) v).le)
      (fun x v => (phaseDerivative_norm (g x) v).le)
      (dgn i) (dg i) (fun n => (hdgn i n).continuous.aestronglyMeasurable.restrict)
      (hdg i K hK) (finiteMollification_tendsto_eLpNorm_sub (hdg i) hK)
    filter_upwards [ae_restrict_le hlim] with x hx
    exact ((phaseDerivative_continuous.clm_apply continuous_const).tendsto (g x)).comp hx
  let φ' := fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)
  have hφ' : Continuous φ' := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hmφ : MemLp φ 2 (volume.restrict K) :=
    (hφ.continuous.memLp_of_hasCompactSupport hs).restrict K
  have hmφ' : MemLp φ' 2 (volume.restrict K) :=
    (hφ'.memLp_of_hasCompactSupport (hs.fderiv_apply ℝ _)).restrict K
  have hz : ∀ x, x ∉ K → φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hz' : ∀ x, x ∉ K → φ' x = 0 := fun x hx => by
    simp [φ', fderiv_of_notMem_tsupport ℝ hx]
  have hn (n : ℕ) : (∫ x in K, φ x • dfn n x) = -(∫ x in K, φ' x • fn n x) := by
    rw [← integral_smul_eq_setIntegral _ hz, ← integral_smul_eq_setIntegral _ hz']
    apply integral_smul_lineDeriv_eq_neg_of_ae_regularLine (D := Set.univ)
    · exact ae_of_all _ fun _ _ => Set.mem_univ _
    · intro x _
      have hd := finiteMollification_hasLineDerivAt hg (hweak i) n x
      have hd' : HasDerivAt
          (fun t : ℝ => gn n (x + t • EuclideanSpace.single i 1)) (dgn i n x) 0 := hd
      have h := (hd'.ofReal_comp.mul_const Complex.I).cexp
      simpa only [HasLineDerivAt, fn, factor, dfn, phaseDerivative_apply, add_zero, zero_smul,
        mul_comm (dgn i n x : ℂ) Complex.I] using h
    · exact fun x => (hφ.differentiable (by simp) x).hasFDerivAt.hasLineDerivAt _
    · exact integrable_smul_of_memLp_on_support hmφ' (hfn n) hz'
    · exact integrable_smul_of_memLp_on_support hmφ (hdfn n) hz
    · exact integrable_smul_of_memLp_on_support hmφ (hfn n) hz
  have hfinal := weak_derivative_identity_closed_eLpNorm hmφ hmφ' hfn hdfn
    (hfloc K hK) (hdloc i K hK) hflim hdflim (Eventually.of_forall hn)
  rw [integral_smul_eq_setIntegral _ hz, integral_smul_eq_setIntegral _ hz']
  exact hfinal

end WeakPhase

/-- A weak gauge angle whose derivative is locally square integrable.
The scalar angle itself is required only to be locally integrable. -/
structure WeakGaugeFunction (I : Type*) [Fintype I] [DecidableEq I] where
  fn : EuclideanSpace ℝ I → ℝ
  locallyIntegrable : LocallyIntegrable fn volume
  gradient : I → EuclideanSpace ℝ I → ℝ
  gradient_local_memLp : ∀ i K, IsCompact K → MemLp (gradient i) 2 (volume.restrict K)
  weak : ∀ i (φ : EuclideanSpace ℝ I → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ x, φ x * gradient i x) = -(∫ x, fderiv ℝ φ x (EuclideanSpace.single i 1) * fn x)

namespace WeakGaugeFunction

variable {I : Type*} [Fintype I] [DecidableEq I] (G : WeakGaugeFunction I)

theorem measurable : AEStronglyMeasurable G.fn volume :=
  G.locallyIntegrable.aestronglyMeasurable

theorem gradient_measurable (i : I) : AEStronglyMeasurable (G.gradient i) volume :=
  (finite_localMemLp_two_locallyIntegrable (G.gradient_local_memLp i)).aestronglyMeasurable

theorem weak_phase : HasWeakH1Local (factor G.fn)
    (fun i x => phaseDerivative (G.fn x) (G.gradient i x)) :=
  weak_phase_of_locallyIntegrable G.locallyIntegrable G.gradient_local_memLp G.weak

/-- Negation of the weak angle gives the inverse phase. -/
def neg : WeakGaugeFunction I where
  fn := -G.fn
  locallyIntegrable := G.locallyIntegrable.neg
  gradient i := -G.gradient i
  gradient_local_memLp i K hK := (G.gradient_local_memLp i K hK).neg
  weak i φ hφ hs := by
    simpa only [Pi.neg_apply, mul_neg, integral_neg, neg_neg] using
      congrArg Neg.neg (G.weak i φ hφ hs)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The precise integrability condition for the weak phase to act on a source. -/
def Admissible (u : ElectronicH1Complex.ComplexH1 H I) : Prop :=
  ∀ i, MemLp (fun x => G.gradient i x • ElectronicH1Complex.value u x) 2 volume

theorem phase_derivative_memLp (u : ElectronicH1Complex.ComplexH1 H I)
    (hu : G.Admissible u) (i : I) :
    MemLp (fun x => phaseDerivative (G.fn x) (G.gradient i x) •
      ElectronicH1Complex.value u x) 2 volume := by
  apply (hu i).mono
  · exact ((finite_localMemLp_two_locallyIntegrable
      (G.weak_phase.derivative_memLp i)).aestronglyMeasurable).smul (Lp.aestronglyMeasurable _)
  · exact ae_of_all _ fun x => by rw [norm_smul, norm_smul, phaseDerivative_norm]

set_option backward.isDefEq.respectTransparency.types false in
/-- The gauge action on the actual electronic weak H1 graph. -/
def gaugeH1 (u : ElectronicH1Complex.ComplexH1 H I) (hu : G.Admissible u) :
    ElectronicH1Complex.ComplexH1 H I :=
  ElectronicH1Complex.realEquiv.symm
    (ElectronicH1Space.ofFunctions
      (fun x => factor G.fn x • ElectronicH1Complex.value u x)
      (fun i x => factor G.fn x • ElectronicH1Complex.derivative i u x +
        phaseDerivative (G.fn x) (G.gradient i x) • ElectronicH1Complex.value u x)
      (phase_memLp G.measurable (ElectronicH1Complex.value u))
      (fun i => (phase_memLp G.measurable (ElectronicH1Complex.derivative i u)).add
        (G.phase_derivative_memLp u hu i))
      (weakH1Local_complex_smul_of_weighted
        (k := factor G.fn) (dk := fun i x => phaseDerivative (G.fn x) (G.gradient i x))
        (f := fun x => ElectronicH1Complex.value u x)
        (df := fun i x => ElectronicH1Complex.derivative i u x)
        G.weak_phase (ElectronicH1Complex.weak u)
        (fun K _ => (phase_memLp G.measurable (ElectronicH1Complex.value u)).restrict K)
        (fun i K _ => (phase_memLp G.measurable (ElectronicH1Complex.derivative i u)).restrict K)
        (fun i K _ => (G.phase_derivative_memLp u hu i).restrict K)))

theorem value_gaugeH1_ae (u : ElectronicH1Complex.ComplexH1 H I) (hu : G.Admissible u) :
    ElectronicH1Complex.value (G.gaugeH1 u hu) =ᵐ[volume]
      fun x => factor G.fn x • ElectronicH1Complex.value u x :=
  (phase_memLp G.measurable _).coeFn_toLp

theorem value_gaugeH1 (u : ElectronicH1Complex.ComplexH1 H I) (hu : G.Admissible u) :
    ElectronicH1Complex.value (G.gaugeH1 u hu) = phase G.measurable
      (ElectronicH1Complex.value u) := by
  apply Lp.ext
  exact (G.value_gaugeH1_ae u hu).trans (phase_ae G.measurable _).symm

theorem derivative_gaugeH1_ae (u : ElectronicH1Complex.ComplexH1 H I)
    (hu : G.Admissible u) (i : I) :
    ElectronicH1Complex.derivative i (G.gaugeH1 u hu) =ᵐ[volume]
      fun x => factor G.fn x • (ElectronicH1Complex.derivative i u x +
        Complex.I • (G.gradient i x • ElectronicH1Complex.value u x)) := by
  have h := ((phase_memLp G.measurable (ElectronicH1Complex.derivative i u)).add
    (G.phase_derivative_memLp u hu i)).coeFn_toLp
  refine h.trans (ae_of_all _ fun x => ?_)
  simp only [Pi.add_apply, phaseDerivative_apply, factor, smul_add,
    ← Complex.coe_smul, smul_smul, mul_assoc]

theorem admissible_neg_gaugeH1 (u : ElectronicH1Complex.ComplexH1 H I)
    (hu : G.Admissible u) : G.neg.Admissible (G.gaugeH1 u hu) := by
  intro i
  apply (hu i).mono
  · exact (G.neg.gradient_measurable i).smul (Lp.aestronglyMeasurable _)
  · filter_upwards [G.value_gaugeH1_ae u hu] with x hx
    rw [hx, norm_smul, norm_smul, norm_smul, norm_factor, one_mul]
    change ‖-G.gradient i x‖ * ‖ElectronicH1Complex.value u x‖ ≤ _
    rw [norm_neg]

/-- No bounded-gradient assumption is needed for invertibility on the weighted domain. -/
theorem neg_gaugeH1 (u : ElectronicH1Complex.ComplexH1 H I) (hu : G.Admissible u) :
    G.neg.gaugeH1 (G.gaugeH1 u hu) (G.admissible_neg_gaugeH1 u hu) = u := by
  apply ElectronicH1Complex.ext_ae
  filter_upwards [G.neg.value_gaugeH1_ae (G.gaugeH1 u hu)
    (G.admissible_neg_gaugeH1 u hu), G.value_gaugeH1_ae u hu] with x hx hy
  rw [hx, hy, smul_smul]
  change (factor (-G.fn) x * factor G.fn x) • ElectronicH1Complex.value u x = _
  rw [factor_neg_mul, one_smul]

end WeakGaugeFunction

/-- Membership in L3 + Linfinity, stated through an almost-everywhere
decomposition into the two usual Lebesgue spaces. -/
def InLpThreeAddTop (f : EuclideanSpace ℝ (Fin 3) → ℝ) : Prop :=
  ∃ a b, MemLp a 3 volume ∧ MemLp b ∞ volume ∧ f =ᵐ[volume] fun x => a x + b x

theorem InLpThreeAddTop.local_memLp_two {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : InLpThreeAddTop f) (K : Set (EuclideanSpace ℝ (Fin 3))) (hK : IsCompact K) :
    MemLp f 2 (volume.restrict K) := by
  obtain ⟨a, b, ha, hb, he⟩ := hf
  let : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  exact (((ha.restrict K).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 3)).add
    ((hb.restrict K).mono_exponent le_top)).ae_eq (ae_restrict_le he.symm)

/-- The spatial gauge regularity in the article. The distribution identity
and local integrability express W1,1 local, and each component of the weak
gradient belongs to L3 + Linfinity. -/
structure WeakSpatialGauge where
  fn : EuclideanSpace ℝ (Fin 3) → ℝ
  locallyIntegrable : LocallyIntegrable fn volume
  gradient : Fin 3 → EuclideanSpace ℝ (Fin 3) → ℝ
  gradient_in_sum : ∀ a, InLpThreeAddTop (gradient a)
  weak : ∀ a (φ : EuclideanSpace ℝ (Fin 3) → ℝ),
    ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ x, φ x * gradient a x) = -(∫ x, fderiv ℝ φ x (EuclideanSpace.single a 1) * fn x)

namespace WeakSpatialGauge

/-- Article spatial regularity supplies every assumption of the proved
weak phase chain rule. -/
def toWeakGaugeFunction (G : WeakSpatialGauge) : WeakGaugeFunction (Fin 3) where
  fn := G.fn
  locallyIntegrable := G.locallyIntegrable
  gradient := G.gradient
  gradient_local_memLp a K hK := (G.gradient_in_sum a).local_memLp_two K hK
  weak := G.weak

theorem weak_phase (G : WeakSpatialGauge) : HasWeakH1Local (factor G.fn)
    (fun a x => phaseDerivative (G.fn x) (G.gradient a x)) :=
  G.toWeakGaugeFunction.weak_phase

end WeakSpatialGauge

end GptLean.TransformationsGauge
