import PfHk.RadialGaugeRadiation
import PfHk.RadialGaugeEnergyLabel

/-! The radiation derivative bound for the actual radial Pauli–Fierz
Weyl gauge, under exactly the paper's extra ultraviolet moment. -/

noncomputable section
namespace PfHk.RadialGauge

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalWeyl
  GptLean.PhysicalPolarization GptLean.SymmetricLift GptLean.Representability
  PfHk.PhysicalFieldRegularity
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 600000

attribute [local irreducible] radiationGraphDerivative radiationGraphInclusion
  weylWeightedGraph RadialGaugeRadiation.energy RadialGaugeRadiation.formDerivative

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)

def inverseLabel (X : Configuration N) : Lp ℂ 2 photonMeasure :=
  (-Complex.I) • (label F χ e X).val.1

def inverseSqrtLabel (X : Configuration N) : Lp ℂ 2 photonMeasure :=
  (-Complex.I) • sqrtLabel F χ hUV e X

theorem inverseSqrtLabel_relation (X : Configuration N) :
    ∀ᵐ p ∂photonMeasure, inverseSqrtLabel F χ hUV e X p =
      (Real.sqrt ‖p.1‖ : ℂ) * inverseLabel F χ e X p := by
  filter_upwards [sqrtLabel_relation F χ hUV e X,
    Lp.coeFn_smul (-Complex.I) (sqrtLabel F χ hUV e X),
    Lp.coeFn_smul (-Complex.I) (label F χ e X).val.1] with p hp hs hl
  change ((-Complex.I) • sqrtLabel F χ hUV e X) p =
    (Real.sqrt ‖p.1‖ : ℂ) * ((-Complex.I) • (label F χ e X).val.1) p
  rw [hs, hl]
  simp only [Pi.smul_apply, smul_eq_mul, hp]
  ring

/-- The inverse radial gauge acts on the actual closed radiation domain. -/
def inverseRadiationGraph (W : ConcreteWeylLaw photonMeasure) (X : Configuration N) :
    RadiationGraphSpace →L[ℂ] RadiationGraphSpace :=
  weylWeightedGraph W (inverseLabel F χ e X) (inverseSqrtLabel F χ hUV e X)
    (inverseSqrtLabel_relation F χ hUV e X)

theorem inverseRadiationGraph_inclusion (W : ConcreteWeylLaw photonMeasure)
    (X : Configuration N) (q : RadiationGraphSpace) :
    radiationGraphInclusion (inverseRadiationGraph F χ hUV e W X q) =
      (unitary F χ e W X).symm (radiationGraphInclusion q) := by
  rw [inverseRadiationGraph, weylWeightedGraph_inclusion, unitary,
    W.weyl_symm photonMeasure]
  simp only [inverseLabel, neg_smul]

/-- The physical cylinder radiation form `2 U H_rad U*`. -/
def radiationForm (X : Configuration N) (q : RadiationGraphSpace) : ℝ :=
  RadialGaugeRadiation.energy (inverseSqrtLabel F χ hUV e X) q

theorem radiationForm_eq (W : ConcreteWeylLaw photonMeasure)
    (X : Configuration N) (q : RadiationGraphSpace) :
    radiationForm F χ hUV e X q =
      2 * ‖radiationGraphDerivative (inverseRadiationGraph F χ hUV e W X q)‖ ^ 2 :=
  RadialGaugeRadiation.energy_eq_weyl W _ _ (inverseSqrtLabel_relation F χ hUV e X) q

def inverseSqrtDerivative (θ : Configuration N) (t : ℝ) : Lp ℂ 2 photonMeasure :=
  (-Complex.I) • ((-Real.exp (-t)) •
    energyComponent true (energyRay F χ hUV e θ (Real.exp (-t))))

theorem inverseSqrtLabel_hasDerivAt (θ : Configuration N) (t : ℝ) :
    HasDerivAt (fun s => inverseSqrtLabel F χ hUV e (Real.exp (-s) • θ))
      (inverseSqrtDerivative F χ hUV e θ t) t :=
  (sqrtLabel_logarithmic_hasDerivAt F χ hUV e θ t).const_smul (-Complex.I)

def radiationFormDerivative (θ : Configuration N) (t : ℝ) (q : RadiationGraphSpace) : ℝ :=
  RadialGaugeRadiation.formDerivative
    (inverseSqrtLabel F χ hUV e (Real.exp (-t) • θ))
    (inverseSqrtDerivative F χ hUV e θ t) q

/-- The displayed derivative in `pf-radiation-derivative` is a genuine
strong derivative of the physical quadratic form at every fixed vector. -/
theorem radiationForm_hasDerivAt (θ : Configuration N) (t : ℝ) (q : RadiationGraphSpace) :
    HasDerivAt (fun s => radiationForm F χ hUV e (Real.exp (-s) • θ) q)
      (radiationFormDerivative F χ hUV e θ t q) t :=
  RadialGaugeRadiation.energy_hasDerivAt (inverseSqrtLabel_hasDerivAt F χ hUV e θ t) q

def radiationConstant : ℝ := Fintype.card (Fin N × Fin 3) * |e| *
  PhysicalProfiles.kernelBound (omegaFactors F χ hUV) rfl (LinearIsometryEquiv.refl ℝ _)

theorem inverseSqrtDerivative_bound (θ : Configuration N) (t : ℝ) :
    ‖inverseSqrtDerivative F χ hUV e θ t‖ ≤
      radiationConstant (N := N) F χ hUV e * ‖θ‖ * Real.exp (-t) := by
  unfold inverseSqrtDerivative
  rw [norm_smul, norm_neg, Complex.norm_I, one_mul]
  have h := sqrtLabel_logarithmic_derivative_bound F χ hUV e θ (Real.exp (-t))
  rw [abs_of_pos (Real.exp_pos _)] at h
  exact h.trans_eq (by unfold radiationConstant; ring)

/-- Exact physical squared bound, with explicit directional dependence.
For unit `θ`, this is `|T'|² ≤ C r² T ||q||²`. -/
theorem radiationFormDerivative_sq_le (θ : Configuration N) (t : ℝ)
    (q : RadiationGraphSpace) :
    (radiationFormDerivative F χ hUV e θ t q) ^ 2 ≤
      8 * (radiationConstant (N := N) F χ hUV e) ^ 2 * ‖θ‖ ^ 2 *
      Real.exp (-t) ^ 2 * radiationForm F χ hUV e (Real.exp (-t) • θ) q *
      ‖radiationGraphInclusion q‖ ^ 2 := by
  have h := RadialGaugeRadiation.formDerivative_sq_le
    (inverseSqrtLabel F χ hUV e (Real.exp (-t) • θ))
    (inverseSqrtDerivative F χ hUV e θ t) q
  have hnorm := inverseSqrtDerivative_bound F χ hUV e θ t
  have hsq := mul_self_le_mul_self (norm_nonneg _) hnorm
  have hm := mul_le_mul_of_nonneg_right hsq
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8)
      (RadialGaugeRadiation.energy_nonneg (inverseSqrtLabel F χ hUV e (Real.exp (-t) • θ)) q)) (sq_nonneg ‖radiationGraphInclusion q‖))
  change (radiationFormDerivative F χ hUV e θ t q) ^ 2 ≤
    8 * radiationForm F χ hUV e (Real.exp (-t) • θ) q *
      ‖inverseSqrtDerivative F χ hUV e θ t‖ ^ 2 * ‖radiationGraphInclusion q‖ ^ 2 at h
  unfold radiationForm at h ⊢
  nlinarith only [h, hm]

end PfHk.RadialGauge
