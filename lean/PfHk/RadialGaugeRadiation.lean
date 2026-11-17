import GptLean.PhysicalWeightedRadiation
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Differentiation of the actual displaced photon radiation form. The
calculation takes place in the radiation analysis sequence space and uses
the existing Weyl graph theorem. Thus it needs no derivative of an
unbounded conjugated operator and no extra operator-domain assumption.
-/

noncomputable section
namespace PfHk.RadialGaugeRadiation

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalWeyl
  GptLean.Representability
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 800000

local instance : InnerProductSpace ℝ (lp (fun _ : ℕ => PhotonFock) 2) :=
  InnerProductSpace.rclikeToReal ℂ _

attribute [local irreducible] coefficientTensor radiationAnalysis
  radiationGraphDerivative radiationGraphInclusion weylWeightedGraph

/-- The radiation analysis vector after a Weyl displacement. -/
def displacedAnalysis (y : Lp ℂ 2 photonMeasure) (q : RadiationGraphSpace) :
    lp (fun _ : ℕ => PhotonFock) 2 :=
  radiationAnalysis q + coefficientTensor y (radiationGraphInclusion q)

/-- Twice the radiation quadratic form in the displaced gauge. -/
def energy (y : Lp ℂ 2 photonMeasure) (q : RadiationGraphSpace) : ℝ :=
  2 * ‖displacedAnalysis y q‖ ^ 2

/-- The derivative with respect to the displacement label, keeping the
physical photon vector fixed. This is the `T'(t)[q]` term. -/
def formDerivative (y dy : Lp ℂ 2 photonMeasure) (q : RadiationGraphSpace) : ℝ :=
  4 * inner ℝ (displacedAnalysis y q) (coefficientTensor dy (radiationGraphInclusion q))

theorem energy_nonneg (y : Lp ℂ 2 photonMeasure) (q : RadiationGraphSpace) :
    0 ≤ energy y q := mul_nonneg (by norm_num) (sq_nonneg _)

/-- Identification with the actual Weyl transform on the closed radiation
graph, under the square-root-frequency relation. -/
theorem energy_eq_weyl (W : ConcreteWeylLaw photonMeasure)
    (f y : Lp ℂ 2 photonMeasure)
    (hy : ∀ᵐ p ∂photonMeasure, y p = (Real.sqrt ‖p.1‖ : ℂ) * f p)
    (q : RadiationGraphSpace) :
    energy y q = 2 * ‖radiationGraphDerivative (weylWeightedGraph W f y hy q)‖ ^ 2 := by
  have h := coefficientTensor_add_norm_sq (radiationAnalysis q) y (radiationGraphInclusion q)
  have hn := congrArg (fun a : ℝ => a ^ 2) (radiationAnalysis_norm q)
  have hh := weylWeightedGraph_derivative_norm_sq W f y hy q
  unfold weightedField at hh
  unfold energy displacedAnalysis
  linarith only [h, hn, hh]

/-- Strong differentiation of the displaced radiation analysis vector. -/
theorem displacedAnalysis_hasDerivAt {y : ℝ → Lp ℂ 2 photonMeasure}
    {dy : Lp ℂ 2 photonMeasure} {t : ℝ} (hy : HasDerivAt y dy t)
    (q : RadiationGraphSpace) :
    HasDerivAt (fun s => displacedAnalysis (y s) q)
      (coefficientTensor dy (radiationGraphInclusion q)) t := by
  let L := ((coefficientTensor (H := PhotonFock)).flip
    (radiationGraphInclusion q)).restrictScalars ℝ
  have h := L.hasFDerivAt.comp_hasDerivAt t hy
  exact h.const_add (radiationAnalysis q)

/-- The form derivative is proved by ordinary Hilbert-space calculus. -/
theorem energy_hasDerivAt {y : ℝ → Lp ℂ 2 photonMeasure}
    {dy : Lp ℂ 2 photonMeasure} {t : ℝ} (hy : HasDerivAt y dy t)
    (q : RadiationGraphSpace) :
    HasDerivAt (fun s => energy (y s) q) (formDerivative (y t) dy q) t := by
  have h := ((displacedAnalysis_hasDerivAt hy q).norm_sq).const_mul 2
  convert h using 1 <;> first | rfl | (unfold formDerivative; ring)

/-- The square of the derivative is controlled by the actual displaced
radiation energy and the square-root-frequency derivative of the label. -/
theorem formDerivative_sq_le (y dy : Lp ℂ 2 photonMeasure) (q : RadiationGraphSpace) :
    (formDerivative y dy q) ^ 2 ≤
      8 * energy y q * ‖dy‖ ^ 2 * ‖radiationGraphInclusion q‖ ^ 2 := by
  have h := abs_real_inner_le_norm (displacedAnalysis y q)
    (coefficientTensor dy (radiationGraphInclusion q))
  rw [coefficientTensor_norm] at h
  have hh := mul_self_le_mul_self (abs_nonneg _) h
  rw [← sq, sq_abs] at hh
  unfold formDerivative energy
  nlinarith

/-- The cylinder radiation error has the required factor of radius when
the label derivative is bounded by a constant times that radius. -/
theorem formDerivative_sq_le_radius (y dy : Lp ℂ 2 photonMeasure)
    (q : RadiationGraphSpace) {C r : ℝ} (_hC : 0 ≤ C) (_hr : 0 ≤ r)
    (hdy : ‖dy‖ ≤ C * r) :
    (formDerivative y dy q) ^ 2 ≤
      8 * C ^ 2 * r ^ 2 * energy y q * ‖radiationGraphInclusion q‖ ^ 2 := by
  have h := formDerivative_sq_le y dy q
  have hsq := mul_self_le_mul_self (norm_nonneg dy) hdy
  have hm := mul_le_mul_of_nonneg_right hsq
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) (energy_nonneg y q))
      (sq_nonneg ‖radiationGraphInclusion q‖))
  nlinarith

end PfHk.RadialGaugeRadiation
