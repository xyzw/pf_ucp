import PfHk.RadialGaugeRadiation
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! The actual displaced radiation form integrated over a spatial measure.
Uniform bounds on displacement labels justify differentiation under the
integral. No operator derivative or radiation estimate is postulated. -/

noncomputable section
namespace PfHk.RadialGaugeRadiation

open MeasureTheory Filter GptLean GptLean.PhysicalFock GptLean.PhysicalWeyl
open scoped ENNReal InnerProductSpace Topology
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000

local instance : InnerProductSpace ℝ (lp (fun _ : ℕ => PhotonFock) 2) :=
  InnerProductSpace.rclikeToReal ℂ _
attribute [local irreducible] coefficientTensor radiationAnalysis
  radiationGraphInclusion radiationGraphDerivative displacedAnalysis energy formDerivative

theorem displacedAnalysis_continuous :
    Continuous (fun z : Lp ℂ 2 photonMeasure × RadiationGraphSpace => displacedAnalysis z.1 z.2) := by
  unfold displacedAnalysis
  exact (radiationAnalysis.continuous.comp continuous_snd).add
    (coefficientTensor.continuous₂.comp
      (continuous_fst.prodMk (radiationGraphInclusion.continuous.comp continuous_snd)))

theorem energy_continuous :
    Continuous (fun z : Lp ℂ 2 photonMeasure × RadiationGraphSpace => energy z.1 z.2) := by
  unfold energy
  exact continuous_const.mul (displacedAnalysis_continuous.norm.pow 2)

theorem formDerivative_continuous :
    Continuous (fun z : (Lp ℂ 2 photonMeasure × Lp ℂ 2 photonMeasure) × RadiationGraphSpace =>
      formDerivative z.1.1 z.1.2 z.2) := by
  have hleft : Continuous (fun z : (Lp ℂ 2 photonMeasure × Lp ℂ 2 photonMeasure) × RadiationGraphSpace =>
      displacedAnalysis z.1.1 z.2) := displacedAnalysis_continuous.comp
    ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  have hright : Continuous (fun z : (Lp ℂ 2 photonMeasure × Lp ℂ 2 photonMeasure) × RadiationGraphSpace =>
      coefficientTensor z.1.2 (radiationGraphInclusion z.2)) := coefficientTensor.continuous₂.comp
    ((continuous_snd.comp continuous_fst).prodMk
      (radiationGraphInclusion.continuous.comp continuous_snd))
  unfold formDerivative
  exact continuous_const.mul (hleft.inner hright)

theorem displacedAnalysis_norm_le (y : Lp ℂ 2 photonMeasure) (q : RadiationGraphSpace) :
    ‖displacedAnalysis y q‖ ≤ (1 + ‖y‖) * ‖q‖ := by
  have h₁ : ‖radiationGraphDerivative q‖ ≤ ‖q‖ := by
    unfold radiationGraphDerivative
    exact norm_snd_le q.val
  have h₂ : ‖radiationGraphInclusion q‖ ≤ ‖q‖ := by
    unfold radiationGraphInclusion
    exact norm_fst_le q.val
  have h : ‖displacedAnalysis y q‖ ≤ ‖radiationAnalysis q‖ +
      ‖coefficientTensor y (radiationGraphInclusion q)‖ := by
    unfold displacedAnalysis
    exact norm_add_le _ _
  have hn := radiationAnalysis_norm q
  have ht := coefficientTensor_norm y (radiationGraphInclusion q)
  have hm := mul_le_mul_of_nonneg_left h₂ (norm_nonneg y)
  nlinarith only [h, h₁, hm, hn, ht]

theorem energy_le_graph (y : Lp ℂ 2 photonMeasure) (q : RadiationGraphSpace)
    {Y : ℝ} (hy : ‖y‖ ≤ Y) : energy y q ≤ 2 * (1 + Y) ^ 2 * ‖q‖ ^ 2 := by
  have hn := (displacedAnalysis_norm_le y q).trans
    (mul_le_mul_of_nonneg_right (add_le_add (le_refl (1 : ℝ)) hy) (norm_nonneg q))
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  unfold energy
  nlinarith only [hs]

theorem formDerivative_abs_le_graph (y dy : Lp ℂ 2 photonMeasure)
    (q : RadiationGraphSpace) {Y D : ℝ} (hy : ‖y‖ ≤ Y) (hd : ‖dy‖ ≤ D) :
    |formDerivative y dy q| ≤ 4 * (1 + Y) * D * ‖q‖ ^ 2 := by
  have hn := (displacedAnalysis_norm_le y q).trans
    (mul_le_mul_of_nonneg_right (add_le_add (le_refl (1 : ℝ)) hy) (norm_nonneg q))
  have hi : ‖radiationGraphInclusion q‖ ≤ ‖q‖ := by
    unfold radiationGraphInclusion
    exact norm_fst_le q.val
  have ht : ‖coefficientTensor dy (radiationGraphInclusion q)‖ ≤ D * ‖q‖ := by
    rw [coefficientTensor_norm]
    exact mul_le_mul hd hi (norm_nonneg _) ((norm_nonneg _).trans hd)
  have hm := mul_le_mul hn ht (norm_nonneg _)
    (mul_nonneg (add_nonneg (by norm_num) ((norm_nonneg y).trans hy)) (norm_nonneg q))
  have h := abs_real_inner_le_norm (displacedAnalysis y q)
    (coefficientTensor dy (radiationGraphInclusion q))
  unfold formDerivative
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  nlinarith only [h, hm]

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem energy_integrable (y : X → Lp ℂ 2 photonMeasure) (q : Lp RadiationGraphSpace 2 μ)
    (hy : AEStronglyMeasurable y μ) {Y : ℝ} (hY : ∀ᵐ x ∂μ, ‖y x‖ ≤ Y) :
    Integrable (fun x => energy (y x) (q x)) μ := by
  apply (((Lp.memLp q).norm.integrable_sq).const_mul (2 * (1 + Y) ^ 2)).mono'
    (energy_continuous.comp_aestronglyMeasurable (hy.prodMk (Lp.aestronglyMeasurable q)))
  filter_upwards [hY] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (energy_nonneg _ _)]
  exact energy_le_graph (y x) (q x) hx

theorem integral_energy_hasDerivAt
    (y dy : ℝ → X → Lp ℂ 2 photonMeasure) (q : Lp RadiationGraphSpace 2 μ)
    (hy : ∀ s, AEStronglyMeasurable (y s) μ)
    (hdy : ∀ s, AEStronglyMeasurable (dy s) μ)
    (t Y D : ℝ)
    (hY : ∀ᵐ x ∂μ, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ‖y s x‖ ≤ Y)
    (hD : ∀ᵐ x ∂μ, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ‖dy s x‖ ≤ D)
    (hd : ∀ᵐ x ∂μ, ∀ s ∈ Set.Ioo (t - 1) (t + 1),
      HasDerivAt (fun a => y a x) (dy s x) s) :
    Integrable (fun x => formDerivative (y t x) (dy t x) (q x)) μ ∧
      HasDerivAt (fun s => ∫ x, energy (y s x) (q x) ∂μ)
        (∫ x, formDerivative (y t x) (dy t x) (q x) ∂μ) t := by
  have ht : t ∈ Set.Ioo (t - 1) (t + 1) := ⟨by linarith, by linarith⟩
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds ht.1 ht.2)
    (Eventually.of_forall fun s => energy_continuous.comp_aestronglyMeasurable
      ((hy s).prodMk (Lp.aestronglyMeasurable q)))
    (energy_integrable (y t) q (hy t) (hY.mono fun x hx => hx t ht))
    (formDerivative_continuous.comp_aestronglyMeasurable
      (((hy t).prodMk (hdy t)).prodMk (Lp.aestronglyMeasurable q)))
    (bound := fun x => 4 * (1 + Y) * D * ‖q x‖ ^ 2)
  · filter_upwards [hY, hD] with x hx hd
    intro s hs
    rw [Real.norm_eq_abs]
    exact formDerivative_abs_le_graph _ _ _ (hx s hs) (hd s hs)
  · exact ((Lp.memLp q).norm.integrable_sq).const_mul _
  · exact hd.mono fun x hx s hs => energy_hasDerivAt (hx s hs) (q x)

end PfHk.RadialGaugeRadiation
