import PfHk.RadialGaugeCurvature
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Angular quadratic-form differentiation on the actual radiation graph.
The electronic angular derivatives are held fixed in this form derivative.
Their later realization as derivatives on the sphere is separate. -/

noncomputable section
namespace PfHk.RadialGaugeAngular

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.SymmetricLift GptLean.Representability PfHk.PhysicalFieldRegularity
  PfHk.RadialGauge
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 600000

local instance : InnerProductSpace ℝ PhotonFock := InnerProductSpace.rclikeToReal ℂ _
attribute [local irreducible] radiationGraphDerivative radiationGraphInclusion kernelField

variable {ι : Type*} [Fintype ι] (C : CanonicalSectorCCR photonMeasure)

/-- Angular covariant derivatives, evaluated at a fixed photon vector. -/
def angularValue (a : WeightedPhotonKernel) (q : RadiationGraphSpace) (v : PhotonFock) :
    PhotonFock := v + Complex.I • kernelField C a q

def energy (a : ι → WeightedPhotonKernel) (q : RadiationGraphSpace) (v : ι → PhotonFock) : ℝ :=
  ∑ j, ‖angularValue C (a j) q (v j)‖ ^ 2

def formDerivative (a da : ι → WeightedPhotonKernel) (q : RadiationGraphSpace)
    (v : ι → PhotonFock) : ℝ :=
  ∑ j, 2 * inner ℝ (angularValue C (a j) q (v j)) (Complex.I • kernelField C (da j) q)

theorem energy_nonneg (a : ι → WeightedPhotonKernel) (q : RadiationGraphSpace)
    (v : ι → PhotonFock) : 0 ≤ energy C a q v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem formDerivative_sq_le (a da : ι → WeightedPhotonKernel) (q : RadiationGraphSpace)
    (v : ι → PhotonFock) :
    (formDerivative C a da q v) ^ 2 ≤
      4 * energy C a q v * ∑ j, ‖kernelField C (da j) q‖ ^ 2 := by
  have hi (j : ι) :
      (2 * inner ℝ (angularValue C (a j) q (v j)) (Complex.I • kernelField C (da j) q)) ^ 2 ≤
        ‖angularValue C (a j) q (v j)‖ ^ 2 * (4 * ‖kernelField C (da j) q‖ ^ 2) := by
    have h := abs_real_inner_le_norm (angularValue C (a j) q (v j))
      (Complex.I • kernelField C (da j) q)
    rw [norm_smul, Complex.norm_I, one_mul] at h
    have hh := mul_self_le_mul_self (abs_nonneg _) h
    rw [← sq, sq_abs] at hh
    nlinarith
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (R := ℝ) Finset.univ
    (fun j _ => sq_nonneg ‖angularValue C (a j) q (v j)‖)
    (fun j _ => by positivity : ∀ j ∈ (Finset.univ : Finset ι), 0 ≤ 4 * ‖kernelField C (da j) q‖ ^ 2)
    (fun j _ => hi j)
  simp only [← Finset.mul_sum] at h
  unfold formDerivative energy
  simp only [← Finset.mul_sum]
  nlinarith only [h]

/-- The field bound turns the form derivative into the product of angular
energy, radiation energy and the squared derivative-label norm. -/
theorem formDerivative_sq_le_labels (a da : ι → WeightedPhotonKernel)
    (q : RadiationGraphSpace) (v : ι → PhotonFock) :
    (formDerivative C a da q v) ^ 2 ≤
      20 * (∑ j, ‖da j‖ ^ 2) * energy C a q v *
        (‖radiationGraphDerivative q‖ ^ 2 + ‖radiationGraphInclusion q‖ ^ 2) := by
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset ι))
    (fun j _ => fieldEvaluation_sq_le C (da j) q)
  have hm := mul_le_mul_of_nonneg_left hs
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (energy_nonneg C a q v))
  have h := (formDerivative_sq_le C a da q v).trans hm
  exact h.trans_eq (by rw [← Finset.sum_mul, ← Finset.mul_sum]; ring)

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)

def physicalLabels (θ : Configuration N) (ζ : ι → Configuration N) (t : ℝ) :
    ι → WeightedPhotonKernel :=
  fun j => angularLabel F χ hUV e θ (ζ j) (Real.exp (-t))

def physicalLabelDerivatives (θ : Configuration N) (ζ : ι → Configuration N) (t : ℝ) :
    ι → WeightedPhotonKernel :=
  fun j => (-(Real.exp (-t) ^ 2)) •
    curvature F χ hUV e (Real.exp (-t) • θ) θ (ζ j)

/-- The derivative of the physical angular form, obtained by differentiating
the actual Segal fields and then the norm squares. -/
theorem physical_energy_hasDerivAt (θ : Configuration N) (ζ : ι → Configuration N)
    (t : ℝ) (q : RadiationGraphSpace) (v : ι → PhotonFock) :
    HasDerivAt (fun s => energy C (physicalLabels F χ hUV e θ ζ s) q v)
      (formDerivative C (physicalLabels F χ hUV e θ ζ t)
        (physicalLabelDerivatives F χ hUV e θ ζ t) q v) t := by
  have hd (j : ι) := (((angularField_logarithmic_hasDerivAt F χ hUV e C θ (ζ j) q t).const_smul Complex.I).const_add (v j)).norm_sq
  have hs := HasDerivAt.sum (u := Finset.univ) (fun j _ => hd j)
  convert hs using 1 <;> first
    | rfl
    | (funext s; simp only [energy, physicalLabels, angularValue, Finset.sum_apply, Pi.smul_apply])
    | (simp only [formDerivative, physicalLabels, physicalLabelDerivatives, angularValue,
        Finset.sum_apply, Pi.smul_apply])

/-- The exact `r⁴` factor in the squared curvature error. All constants
are independent of the electronic position and the cylinder coordinate. -/
theorem physical_formDerivative_sq_le (θ : Configuration N) (ζ : ι → Configuration N)
    (t : ℝ) (q : RadiationGraphSpace) (v : ι → PhotonFock) :
    (formDerivative C (physicalLabels F χ hUV e θ ζ t)
      (physicalLabelDerivatives F χ hUV e θ ζ t) q v) ^ 2 ≤
    20 * Real.exp (-t) ^ 4 *
      (2 * Fintype.card (Fin N × Fin 3) * |e| * momentBound F χ hUV) ^ 2 *
      ‖θ‖ ^ 2 * (∑ j, ‖ζ j‖ ^ 2) * energy C (physicalLabels F χ hUV e θ ζ t) q v *
      (‖radiationGraphDerivative q‖ ^ 2 + ‖radiationGraphInclusion q‖ ^ 2) := by
  have hnorm (j : ι) : ‖physicalLabelDerivatives F χ hUV e θ ζ t j‖ ^ 2 ≤
      Real.exp (-t) ^ 4 *
        (2 * Fintype.card (Fin N × Fin 3) * |e| * momentBound F χ hUV) ^ 2 *
        ‖θ‖ ^ 2 * ‖ζ j‖ ^ 2 := by
    have h := pow_le_pow_left₀ (norm_nonneg _)
      (curvature_norm_le F χ hUV e (Real.exp (-t) • θ) θ (ζ j)) 2
    unfold physicalLabelDerivatives
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (sq_nonneg _), mul_pow]
    have hh := mul_le_mul_of_nonneg_left h (sq_nonneg (Real.exp (-t) ^ 2))
    exact hh.trans_eq (by ring)
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset ι)) (fun j _ => hnorm j)
  have h := formDerivative_sq_le_labels C
    (physicalLabels F χ hUV e θ ζ t) (physicalLabelDerivatives F χ hUV e θ ζ t) q v
  have hm := mul_le_mul_of_nonneg_right hs (mul_nonneg
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 20) (energy_nonneg C (physicalLabels F χ hUV e θ ζ t) q v))
      (add_nonneg (sq_nonneg ‖radiationGraphDerivative q‖) (sq_nonneg ‖radiationGraphInclusion q‖)))
  rw [← Finset.mul_sum] at hm
  nlinarith

end PfHk.RadialGaugeAngular
