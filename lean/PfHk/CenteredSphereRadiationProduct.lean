import PfHk.CenteredSphereRadiationEnergy
import PfHk.SpatialBilinearDerivative
import PfHk.L2QuadraticForms

/-! Moving-state differentiation of the actual centered radiation form
on the sphere, through its bounded radiation-analysis map. -/

noncomputable section
namespace PfHk.CenteredSphereRadiationEnergy

open MeasureTheory Filter GptLean GptLean.PhysicalFock GptLean.PhysicalWeyl
  GptLean.PhysicalPolarization GptLean.SymmetricLift GptLean.Representability
  PfHk.PhysicalFieldRegularity PfHk.PolarCalculus PfHk.SphereAngularField
open scoped ENNReal Topology InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 100000

abbrev AnalysisSpace := lp (fun _ : ℕ => PhotonFock) 2
abbrev SphereAnalysis (N : ℕ) := Lp AnalysisSpace 2 (sphereMeasure (Fin N × Fin 3))
local instance : InnerProductSpace ℝ AnalysisSpace := InnerProductSpace.rclikeToReal ℂ _

attribute [local irreducible] coefficientTensor radiationAnalysis radiationGraphInclusion
  RadialGaugeRadiation.displacedAnalysis label labelDerivative energy formDerivative

def tensorMap : Lp ℂ 2 photonMeasure →L[ℂ] RadiationGraphSpace →L[ℂ] AnalysisSpace :=
  (ContinuousLinearMap.compL ℂ RadiationGraphSpace PhotonFock AnalysisSpace).flip
    radiationGraphInclusion |>.comp coefficientTensor

theorem tensorMap_apply (y : Lp ℂ 2 photonMeasure) (q : RadiationGraphSpace) :
    tensorMap y q = coefficientTensor y (radiationGraphInclusion q) := rfl

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (O : Configuration N)

def shift (t : ℝ) : SphereRadiation N →L[ℂ] SphereAnalysis N :=
  SpatialBilinearDerivative.operator (sphereMeasure (Fin N × Fin 3)) tensorMap
    (label F χ hUV e O t) (label_measurable F χ hUV e O t)
    (Real.exp (-t) * CenteredRadialGauge.radiationConstant (N := N) F χ hUV e)
    (ae_of_all _ (label_norm_le F χ hUV e O t))

def shiftDerivative (t : ℝ) : SphereRadiation N →L[ℂ] SphereAnalysis N :=
  SpatialBilinearDerivative.operator (sphereMeasure (Fin N × Fin 3)) tensorMap
    (labelDerivative F χ hUV e O t) (labelDerivative_measurable F χ hUV e O t)
    (Real.exp (1-t) * CenteredRadialGauge.radiationConstant (N := N) F χ hUV e)
    (ae_of_all _ fun θ => (labelDerivative_norm_le F χ hUV e O t θ).trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith))
        (radiationConstant_nonneg F χ hUV e)))

def analysis (t : ℝ) : SphereRadiation N →L[ℂ] SphereAnalysis N :=
  radiationAnalysis.compLpL 2 (sphereMeasure (Fin N × Fin 3)) + shift F χ hUV e O t

theorem shift_ae (t : ℝ) (q : SphereRadiation N) :
    shift F χ hUV e O t q =ᵐ[sphereMeasure (Fin N × Fin 3)] fun θ =>
      coefficientTensor (label F χ hUV e O t θ) (radiationGraphInclusion (q θ)) :=
  SpatialBilinearDerivative.operator_ae _ _ _ _ _ _ _

theorem shiftDerivative_ae (t : ℝ) (q : SphereRadiation N) :
    shiftDerivative F χ hUV e O t q =ᵐ[sphereMeasure (Fin N × Fin 3)] fun θ =>
      coefficientTensor (labelDerivative F χ hUV e O t θ) (radiationGraphInclusion (q θ)) :=
  SpatialBilinearDerivative.operator_ae _ _ _ _ _ _ _

theorem analysis_ae (t : ℝ) (q : SphereRadiation N) :
    analysis F χ hUV e O t q =ᵐ[sphereMeasure (Fin N × Fin 3)] fun θ =>
      RadialGaugeRadiation.displacedAnalysis (label F χ hUV e O t θ) (q θ) := by
  unfold analysis
  filter_upwards [Lp.coeFn_add (radiationAnalysis.compLpL 2 _ q) (shift F χ hUV e O t q),
    radiationAnalysis.coeFn_compLpL q, shift_ae F χ hUV e O t q] with θ ha hb hc
  unfold RadialGaugeRadiation.displacedAnalysis
  simp only [Pi.add_apply] at ha
  exact ha.trans (congrArg₂ (fun x y : AnalysisSpace => x + y) hb hc)

theorem label_slope_bound (t h : ℝ) (hh : |h| ≤ 1) (θ : Sphere N) :
    ‖h⁻¹ • (label F χ hUV e O (t+h) θ - label F χ hUV e O t θ)‖ ≤
      Real.exp (1-t) * CenteredRadialGauge.radiationConstant (N := N) F χ hUV e := by
  apply L2ParameterDerivative.local_slope_norm_le
    (f := fun s => label F χ hUV e O s θ)
    (df := fun s => labelDerivative F χ hUV e O s θ)
    (mul_nonneg (Real.exp_pos _).le (radiationConstant_nonneg F χ hUV e))
    (fun s _ => by
      unfold label labelDerivative
      exact CenteredRadialGauge.inverseSqrtLabel_hasDerivAt F χ hUV e O θ.val s) _ hh
  intro s hs
  exact (labelDerivative_norm_le F χ hUV e O s θ).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith [hs.1]))
      (radiationConstant_nonneg F χ hUV e))

theorem shift_hasDerivAt (t : ℝ) (q : SphereRadiation N) :
    L2OperatorDerivative.HasL2DerivAt (fun s => shift F χ hUV e O s q)
      (shiftDerivative F χ hUV e O t q) t := by
  apply SpatialBilinearDerivative.operator_hasDerivAt
  · apply ae_of_all
    intro θ
    unfold label labelDerivative
    exact CenteredRadialGauge.inverseSqrtLabel_hasDerivAt F χ hUV e O θ.val t
  · have he : ∀ᶠ h in 𝓝[≠] (0 : ℝ), h ∈ Set.Ioo (-1 : ℝ) 1 :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
    filter_upwards [he] with h hh
    exact ae_of_all _ fun θ => label_slope_bound F χ hUV e O t h
      (abs_le.mpr ⟨hh.1.le, hh.2.le⟩) θ

theorem analysis_hasDerivAt (t : ℝ) (q : SphereRadiation N) :
    L2OperatorDerivative.HasL2DerivAt (fun s => analysis F χ hUV e O s q)
      (shiftDerivative F χ hUV e O t q) t := by
  convert! (shift_hasDerivAt F χ hUV e O t q).const_add
    (radiationAnalysis.compLpL 2 (sphereMeasure (Fin N × Fin 3)) q) using 1

theorem analysis_local_norm_le (t : ℝ) :
    ∀ᶠ s in 𝓝 t, ‖analysis F χ hUV e O s‖ ≤
      1 + Real.exp (1-t) * CenteredRadialGauge.radiationConstant (N := N) F χ hUV e := by
  filter_upwards [Ioo_mem_nhds (by linarith : t-1<t) (by linarith : t<t+1)] with s hs
  apply ContinuousLinearMap.opNorm_le_bound (analysis F χ hUV e O s)
    (add_nonneg (by norm_num) (mul_nonneg (Real.exp_pos _).le (radiationConstant_nonneg F χ hUV e)))
  intro q
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [analysis_ae F χ hUV e O s q] with θ hθ
  have hy := (label_norm_le F χ hUV e O s θ).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith [hs.1] : -s ≤ 1-t))
      (radiationConstant_nonneg F χ hUV e))
  calc
    _ = ‖RadialGaugeRadiation.displacedAnalysis (label F χ hUV e O s θ) (q θ)‖ := congrArg norm hθ
    _ ≤ (1 + ‖label F χ hUV e O s θ‖) * ‖q θ‖ := RadialGaugeRadiation.displacedAnalysis_norm_le _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (add_le_add (le_refl (1 : ℝ)) hy) (norm_nonneg _)

theorem analysis_moving_hasDerivAt {q : ℝ → SphereRadiation N} {dq : SphereRadiation N}
    {t : ℝ} (hq : L2OperatorDerivative.HasL2DerivAt q dq t) :
    L2OperatorDerivative.HasL2DerivAt (fun s => analysis F χ hUV e O s (q s))
      (analysis F χ hUV e O t dq + shiftDerivative F χ hUV e O t (q t)) t := by
  let A : ℝ → SphereRadiation N →L[ℝ] SphereAnalysis N :=
    fun s => (analysis F χ hUV e O s).restrictScalars ℝ
  have ha (u : SphereRadiation N) : HasDerivAt (fun s => A s u)
      (shiftDerivative F χ hUV e O t u) t := by
    convert! analysis_hasDerivAt F χ hUV e O t u using 1
  have hb := analysis_local_norm_le F χ hUV e O t
  have hb' : ∀ᶠ s in 𝓝 t, ‖A s‖ ≤
      1 + Real.exp (1-t) * CenteredRadialGauge.radiationConstant (N := N) F χ hUV e := by
    simpa only [A, ContinuousLinearMap.norm_restrictScalars] using hb
  convert! StrongOperatorDerivative.hasDerivAt_apply ha hb' hq using 1

theorem energy_eq_analysis (t : ℝ) (q : SphereRadiation N) :
    energy F χ hUV e O q t = 2 * ‖analysis F χ hUV e O t q‖ ^ 2 := by
  have h := L2QuadraticForms.scaled_norm_eq_integral 2
    (analysis F χ hUV e O t q) (analysis_ae F χ hUV e O t q)
  unfold energy CenteredRadialGauge.radiationForm RadialGaugeRadiation.energy
  unfold label at h
  exact h.symm

theorem formDerivative_eq_analysis (t : ℝ) (q : SphereRadiation N) :
    formDerivative F χ hUV e O q t =
      4 * inner ℝ (analysis F χ hUV e O t q) (shiftDerivative F χ hUV e O t q) := by
  have h := L2QuadraticForms.scaled_inner_eq_integral 4
    (analysis F χ hUV e O t q) (shiftDerivative F χ hUV e O t q)
    (analysis_ae F χ hUV e O t q) (shiftDerivative_ae F χ hUV e O t q)
  unfold formDerivative CenteredRadialGauge.radiationFormDerivative
    RadialGaugeRadiation.formDerivative
  unfold label labelDerivative at h
  exact h.symm

theorem analysis_pair_eq_integral (t : ℝ) (q v : SphereRadiation N) :
    2 * inner ℝ (analysis F χ hUV e O t q) (analysis F χ hUV e O t v) =
      ∫ θ : Sphere N, 2 * inner ℝ
        (RadialGaugeRadiation.displacedAnalysis (label F χ hUV e O t θ) (q θ))
        (RadialGaugeRadiation.displacedAnalysis (label F χ hUV e O t θ) (v θ))
        ∂sphereMeasure (Fin N × Fin 3) :=
  L2QuadraticForms.scaled_inner_eq_integral 2 _ _
    (analysis_ae F χ hUV e O t q) (analysis_ae F χ hUV e O t v)

theorem energy_moving_hasDerivAt {q : ℝ → SphereRadiation N} {dq : SphereRadiation N}
    {t : ℝ} (hq : L2OperatorDerivative.HasL2DerivAt q dq t) :
    HasDerivAt (fun s => energy F χ hUV e O (q s) s)
      (2 * (∫ θ : Sphere N, 2 * inner ℝ
        (RadialGaugeRadiation.displacedAnalysis (label F χ hUV e O t θ) (q t θ))
        (RadialGaugeRadiation.displacedAnalysis (label F χ hUV e O t θ) (dq θ))
        ∂sphereMeasure (Fin N × Fin 3)) + formDerivative F χ hUV e O (q t) t) t := by
  have h := ((analysis_moving_hasDerivAt F χ hUV e O hq).norm_sq).const_mul 2
  simp only [energy_eq_analysis, ← analysis_pair_eq_integral,
    formDerivative_eq_analysis]
  convert! h using 1
  simp only [inner_add_right]
  ring

end PfHk.CenteredSphereRadiationEnergy
