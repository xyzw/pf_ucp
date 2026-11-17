import GptLean.SymmetricLift.WeakDerivativeClosure
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-!
Strong L2 approximation by actual convolution for fields in L1 and L2.
The additional L1 assumption allows the existing Fubini theorem to identify
the L2-valued average of translations with the raw Bochner convolution.
Compactly supported L2 fields meet this assumption on locally finite spaces.
-/

noncomputable section

namespace GptLean.SymmetricLift

open MeasureTheory Filter Function Set
open scoped ENNReal Topology Convolution

variable {X V : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The L2 scalar test pairing as a bounded linear map. -/
def l2TestIntegralCLM {φ : X → ℝ} (hφ : MemLp φ 2 μ) : Lp V 2 μ →L[ℝ] V :=
  LinearMap.mkContinuous
    { toFun := l2TestIntegral φ
      map_add' := by
        intro f g
        unfold l2TestIntegral
        calc
          (∫ x, φ x • (f + g) x ∂μ) = ∫ x, φ x • (f x + g x) ∂μ := by
            apply integral_congr_ae
            filter_upwards [Lp.coeFn_add f g] with x hx
            simp only [Pi.add_apply] at hx
            rw [hx]
          _ = _ := by
            simp only [smul_add]
            exact integral_add (integrable_l2_test hφ f) (integrable_l2_test hφ g)
      map_smul' := by
        intro c f
        unfold l2TestIntegral
        calc
          (∫ x, φ x • (c • f) x ∂μ) = ∫ x, c • (φ x • f x) ∂μ := by
            apply integral_congr_ae
            filter_upwards [Lp.coeFn_smul c f] with x hx
            simp only [Pi.smul_apply] at hx
            rw [hx, smul_comm]
          _ = _ := integral_smul c _ }
    ‖hφ.toLp φ‖ (norm_l2TestIntegral_le hφ)

@[simp] theorem l2TestIntegralCLM_apply {φ : X → ℝ} (hφ : MemLp φ 2 μ)
    (f : Lp V 2 μ) : l2TestIntegralCLM hφ f = ∫ x, φ x • f x ∂μ := rfl

/-- Integration over a finite-measure set is a bounded map on L2. -/
def l2SetIntegralCLM (s : Set X) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    Lp V 2 μ →L[ℝ] V :=
  l2TestIntegralCLM (memLp_indicator_const 2 hs (1 : ℝ) (Or.inr hμs))

theorem l2SetIntegralCLM_apply (s : Set X) (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (f : Lp V 2 μ) : l2SetIntegralCLM s hs hμs f = ∫ x in s, f x ∂μ := by
  change (∫ x, s.indicator (fun _ => (1 : ℝ)) x • f x ∂μ) = _
  calc
    _ = ∫ x, s.indicator (fun x => f x) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x ∈ s <;> simp [hx]
    _ = _ := integral_indicator hs

section Translation

variable {G : Type*} [NormedAddCommGroup G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsAddLeftInvariant] [μ.InnerRegularCompactLTTop]
  [IsLocallyFiniteMeasure μ]

/-- Translation acts on the actual L2 equivalence classes. -/
def translateL2 (y : G) (f : Lp V 2 μ) : Lp V 2 μ :=
  Lp.compMeasurePreserving (fun x => x + y) (measurePreserving_add_right μ y) f

omit [NormedSpace ℝ V] [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure μ] in
theorem coeFn_translateL2 (y : G) (f : Lp V 2 μ) :
    translateL2 y f =ᵐ[μ] fun x => f (x + y) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right μ y)

omit [NormedSpace ℝ V] [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure μ] in
@[simp] theorem translateL2_zero (f : Lp V 2 μ) : translateL2 0 f = f := by
  apply Lp.ext
  filter_upwards [coeFn_translateL2 0 f] with x hx
  simpa only [add_zero] using hx

omit [NormedSpace ℝ V] [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure μ] in
@[simp] theorem norm_translateL2 (y : G) (f : Lp V 2 μ) :
    ‖translateL2 y f‖ = ‖f‖ := Lp.norm_compMeasurePreserving f _

omit [NormedSpace ℝ V] in
theorem continuous_translateL2 (f : Lp V 2 μ) : Continuous fun y => translateL2 y f := by
  let g : G → C(G, G) := fun y => ⟨fun x => x + y, continuous_id.add continuous_const⟩
  have hg : Continuous g :=
    ContinuousMap.continuous_of_continuous_uncurry g (continuous_snd.add continuous_fst)
  exact continuous_const.compMeasurePreservingLp hg
    (fun y => measurePreserving_add_right μ y) (by norm_num)

omit [NormedSpace ℝ V] [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure μ] in
theorem coeFn_translateL2_toLp (y : G) {f : G → V} (hf : MemLp f 2 μ) :
    translateL2 y (hf.toLp f) =ᵐ[μ] fun x => f (x + y) :=
  (hf.comp_measurePreserving (measurePreserving_add_right μ y)).coeFn_toLp

variable [SecondCountableTopology G] [CompleteSpace V]

/-- The Bochner average is formed inside the complete L2 space. -/
def l2ConvolutionAverage (κ : G → ℝ) (f : Lp V 2 μ) : Lp V 2 μ :=
  ∫ y, κ y • translateL2 (-y) f ∂μ

omit [CompleteSpace V] in
theorem integrable_l2ConvolutionAverage {κ : G → ℝ} (hκ : Integrable κ μ)
    (f : Lp V 2 μ) : Integrable (fun y => κ y • translateL2 (-y) f) μ := by
  apply (hκ.norm.mul_const ‖f‖).mono'
    (hκ.aestronglyMeasurable.smul
      ((continuous_translateL2 f).comp continuous_neg).aestronglyMeasurable)
  filter_upwards [] with y
  change ‖κ y • translateL2 (-y) f‖ ≤ ‖κ y‖ * ‖f‖
  simp only [norm_smul, norm_translateL2, le_refl]

variable [SigmaFinite μ]

/-- Fubini identifies the L2-valued average with the actual convolution.
The extra L1 assumption concerns only the field, not the conclusion. -/
theorem coeFn_l2ConvolutionAverage {κ : G → ℝ} (hκ : Integrable κ μ)
    {f : G → V} (hf₁ : Integrable f μ) (hf₂ : MemLp f 2 μ) :
    l2ConvolutionAverage κ (hf₂.toLp f) =ᵐ[μ]
      (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) := by
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · intro s _ hμs
    exact integrableOn_Lp_of_measure_ne_top _ (by norm_num) hμs.ne
  · intro s _ _
    exact (hκ.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hf₁).integrableOn
  · intro s hs hμs
    let J : Lp V 2 μ →L[ℝ] V := l2SetIntegralCLM s hs hμs.ne
    have hJ (g : Lp V 2 μ) : J g = ∫ x in s, g x ∂μ :=
      l2SetIntegralCLM_apply s hs hμs.ne g
    have hprod : Integrable (fun p : G × G => κ p.2 • f (p.1 - p.2))
        ((μ.restrict s).prod μ) := by
      rw [Measure.restrict_prod_eq_prod_univ]
      exact (hκ.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hf₁).integrableOn
    calc
      (∫ x in s, l2ConvolutionAverage κ (hf₂.toLp f) x ∂μ) =
          J (l2ConvolutionAverage κ (hf₂.toLp f)) := (hJ _).symm
      _ = ∫ y, J (κ y • translateL2 (-y) (hf₂.toLp f)) ∂μ :=
        (J.integral_comp_comm (integrable_l2ConvolutionAverage hκ _)).symm
      _ = ∫ y, κ y • (∫ x in s, f (x - y) ∂μ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with y
        rw [map_smul, hJ]
        congr 1
        apply setIntegral_congr_ae hs
        filter_upwards [coeFn_translateL2_toLp (-y) hf₂] with x hx
        intro _
        simpa only [sub_eq_add_neg] using hx
      _ = ∫ y, ∫ x in s, κ y • f (x - y) ∂μ ∂μ := by
        simp only [integral_smul]
      _ = ∫ x in s, ∫ y, κ y • f (x - y) ∂μ ∂μ :=
        (integral_integral_swap hprod).symm
      _ = _ := rfl

theorem memLp_convolution_of_integrable {κ : G → ℝ} (hκ : Integrable κ μ)
    {f : G → V} (hf₁ : Integrable f μ) (hf₂ : MemLp f 2 μ) :
    MemLp (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) 2 μ :=
  (Lp.memLp _).ae_eq (coeFn_l2ConvolutionAverage hκ hf₁ hf₂)

/-- Shrinking nonnegative unit-mass kernels converge strongly as L2 averages. -/
theorem tendsto_l2ConvolutionAverage {A : Type*} {l : Filter A} {κ : A → G → ℝ}
    (hnκ : ∀ᶠ n in l, ∀ x, 0 ≤ κ n x)
    (hiκ : ∀ᶠ n in l, ∫ x, κ n x ∂μ = 1)
    (hsκ : Tendsto (fun n => support (κ n)) l (𝓝 0).smallSets)
    (f : Lp V 2 μ) : Tendsto (fun n => l2ConvolutionAverage (κ n) f) l (𝓝 f) := by
  have hcg : Tendsto (uncurry fun (_ : A) (y : G) => translateL2 y f)
      (l ×ˢ 𝓝 0) (𝓝 f) := by
    change Tendsto (fun p : A × G => translateL2 p.2 f) (l ×ˢ 𝓝 0) (𝓝 f)
    simpa only [translateL2_zero, Function.comp_def] using
      ((continuous_translateL2 f).tendsto 0).comp tendsto_snd
  have h := convolution_tendsto_right hnκ hiκ hsκ
    (Eventually.of_forall fun _ => (continuous_translateL2 f).aestronglyMeasurable)
    hcg (tendsto_const_nhds (x := (0 : G)))
  simpa only [l2ConvolutionAverage, convolution_def, ContinuousLinearMap.lsmul_apply,
    zero_sub] using h

/-- Actual raw convolutions converge in L2. The L1 condition applies to the
input field and is satisfied by the compact truncations used for local H1. -/
theorem tendsto_eLpNorm_convolution_sub {A : Type*} {l : Filter A} {κ : A → G → ℝ}
    (hκ : ∀ n, Integrable (κ n) μ)
    (hnκ : ∀ᶠ n in l, ∀ x, 0 ≤ κ n x)
    (hiκ : ∀ᶠ n in l, ∫ x, κ n x ∂μ = 1)
    (hsκ : Tendsto (fun n => support (κ n)) l (𝓝 0).smallSets)
    {f : G → V} (hf₁ : Integrable f μ) (hf₂ : MemLp f 2 μ) :
    Tendsto (fun n => eLpNorm ((κ n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) - f) 2 μ)
      l (𝓝 0) := by
  have havg := tendsto_l2ConvolutionAverage hnκ hiκ hsκ (hf₂.toLp f)
  have heq (n : A) :
      (memLp_convolution_of_integrable (hκ n) hf₁ hf₂).toLp
        (κ n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) =
      l2ConvolutionAverage (κ n) (hf₂.toLp f) := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp _).trans (coeFn_l2ConvolutionAverage (hκ n) hf₁ hf₂).symm
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _
    (fun n => memLp_convolution_of_integrable (hκ n) hf₁ hf₂) f hf₂).mp
  simpa only [heq] using havg

end Translation

end GptLean.SymmetricLift
