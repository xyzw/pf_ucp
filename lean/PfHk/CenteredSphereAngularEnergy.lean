import PfHk.CenteredSphereAngularField
import PfHk.CenteredRadialGaugeAngular
import PfHk.IntegratedFormBounds
import PfHk.L2QuadraticForms

/-! Angular energy and its derivative on the actual sphere Hilbert space.
The derivative is computed by strong L2 differentiation of the physical
Segal fields. Its curvature bound is then integrated over surface measure. -/

noncomputable section
namespace PfHk.CenteredSphereAngularField

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.SymmetricLift GptLean.Representability PfHk.PhysicalFieldRegularity
  PfHk.CenteredRadialGauge PfHk.PolarCalculus
open PfHk.SphereAngularField (Sphere SphereRadiation SpherePhoton)
open PfHk.RadialGauge (curvatureConstant curvatureConstant_nonneg)
open scoped ENNReal InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 600000

local instance : InnerProductSpace ℝ PhotonFock := InnerProductSpace.rclikeToReal ℂ _
attribute [local irreducible] field fieldDerivative kernelField
  radiationGraphInclusion radiationGraphDerivative CenteredRadialGauge.radiationForm RadialGaugeAngular.angularValue

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ) (O : Configuration N)
  (C : CanonicalSectorCCR photonMeasure)

def angularVector (p : (Fin N × Fin 3) → SpherePhoton N) (q : SphereRadiation N)
    (j : Fin N × Fin 3) (t : ℝ) : SpherePhoton N :=
  p j + Complex.I • field F χ hUV e O C j t q

attribute [local irreducible] angularVector

def energy (p : (Fin N × Fin 3) → SpherePhoton N) (q : SphereRadiation N) (t : ℝ) : ℝ :=
  ∑ j, ‖angularVector F χ hUV e O C p q j t‖ ^ 2

def formDerivative (p : (Fin N × Fin 3) → SpherePhoton N)
    (q : SphereRadiation N) (t : ℝ) : ℝ :=
  ∑ j, 2 * inner ℝ (angularVector F χ hUV e O C p q j t)
    (Complex.I • fieldDerivative F χ hUV e O C j t q)

theorem energy_nonneg (p : (Fin N × Fin 3) → SpherePhoton N)
    (q : SphereRadiation N) (t : ℝ) : 0 ≤ energy F χ hUV e O C p q t :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem energy_hasDerivAt (p : (Fin N × Fin 3) → SpherePhoton N)
    (q : SphereRadiation N) (t : ℝ) :
    HasDerivAt (energy F χ hUV e O C p q) (formDerivative F χ hUV e O C p q t) t := by
  have hd (j : Fin N × Fin 3) :=
    (((field_hasDerivAt F χ hUV e O C j t q).const_smul Complex.I).const_add (p j)).norm_sq
  have hs := HasDerivAt.sum (u := Finset.univ) (fun j _ => hd j)
  convert hs using 1 <;> first
    | rfl
    | (funext s; simp only [energy, angularVector, Finset.sum_apply, Pi.smul_apply])
    | (simp only [formDerivative, angularVector, Finset.sum_apply, Pi.smul_apply])

theorem angularVector_ae (p : (Fin N × Fin 3) → SpherePhoton N)
    (q : SphereRadiation N) (j : Fin N × Fin 3) (t : ℝ) :
    angularVector F χ hUV e O C p q j t =ᵐ[sphereMeasure (Fin N × Fin 3)]
      fun θ => RadialGaugeAngular.angularValue C (coefficient F χ hUV e O j t θ)
        (q θ) (p j θ) := by
  have hf : field F χ hUV e O C j t q =ᵐ[sphereMeasure (Fin N × Fin 3)]
      fun θ => kernelField C (coefficient F χ hUV e O j t θ) (q θ) := by
    unfold field
    exact spatialField_ae _ C _ _ _ _ q
  simpa only [angularVector, RadialGaugeAngular.angularValue] using
    L2QuadraticForms.add_smul_ae Complex.I (p j) (field F χ hUV e O C j t q) hf

theorem fieldDerivative_ae (q : SphereRadiation N) (j : Fin N × Fin 3) (t : ℝ) :
    Complex.I • fieldDerivative F χ hUV e O C j t q =ᵐ[sphereMeasure (Fin N × Fin 3)]
      fun θ => Complex.I • kernelField C (derivativeCoefficient F χ hUV e O j t θ) (q θ) := by
  have hf : fieldDerivative F χ hUV e O C j t q =ᵐ[sphereMeasure (Fin N × Fin 3)]
      fun θ => kernelField C (derivativeCoefficient F χ hUV e O j t θ) (q θ) := by
    unfold fieldDerivative
    exact spatialField_ae _ C _ _ _ _ q
  exact L2QuadraticForms.smul_ae Complex.I (fieldDerivative F χ hUV e O C j t q) hf

theorem fiber_energy_integrable (p : (Fin N × Fin 3) → SpherePhoton N)
    (q : SphereRadiation N) (t : ℝ) :
    Integrable (fun θ => RadialGaugeAngular.energy C
      (fun j => coefficient F χ hUV e O j t θ) (q θ) (fun j => p j θ))
      (sphereMeasure (Fin N × Fin 3)) := by
  unfold RadialGaugeAngular.energy
  exact L2QuadraticForms.sum_norm_integrable
    (fun j => angularVector F χ hUV e O C p q j t) (fun j => angularVector_ae F χ hUV e O C p q j t)

theorem energy_eq_integral (p : (Fin N × Fin 3) → SpherePhoton N)
    (q : SphereRadiation N) (t : ℝ) :
    energy F χ hUV e O C p q t = ∫ θ,
      RadialGaugeAngular.energy C (fun j => coefficient F χ hUV e O j t θ)
        (q θ) (fun j => p j θ) ∂sphereMeasure (Fin N × Fin 3) := by
  unfold energy RadialGaugeAngular.energy
  exact L2QuadraticForms.sum_norm_eq_integral
    (fun j => angularVector F χ hUV e O C p q j t) (fun j => angularVector_ae F χ hUV e O C p q j t)

theorem fiber_derivative_integrable (p : (Fin N × Fin 3) → SpherePhoton N)
    (q : SphereRadiation N) (t : ℝ) :
    Integrable (fun θ => RadialGaugeAngular.formDerivative C
      (fun j => coefficient F χ hUV e O j t θ)
      (fun j => derivativeCoefficient F χ hUV e O j t θ) (q θ) (fun j => p j θ))
      (sphereMeasure (Fin N × Fin 3)) := by
  unfold RadialGaugeAngular.formDerivative
  exact L2QuadraticForms.sum_inner_integrable
    (fun j => angularVector F χ hUV e O C p q j t)
    (fun j => Complex.I • fieldDerivative F χ hUV e O C j t q)
    (fun j => angularVector_ae F χ hUV e O C p q j t) (fun j => fieldDerivative_ae F χ hUV e O C q j t)

theorem formDerivative_eq_integral (p : (Fin N × Fin 3) → SpherePhoton N)
    (q : SphereRadiation N) (t : ℝ) :
    formDerivative F χ hUV e O C p q t = ∫ θ,
      RadialGaugeAngular.formDerivative C (fun j => coefficient F χ hUV e O j t θ)
        (fun j => derivativeCoefficient F χ hUV e O j t θ) (q θ) (fun j => p j θ)
        ∂sphereMeasure (Fin N × Fin 3) := by
  unfold formDerivative RadialGaugeAngular.formDerivative
  exact L2QuadraticForms.sum_inner_eq_integral
    (fun j => angularVector F χ hUV e O C p q j t)
    (fun j => Complex.I • fieldDerivative F χ hUV e O C j t q)
    (fun j => angularVector_ae F χ hUV e O C p q j t) (fun j => fieldDerivative_ae F χ hUV e O C q j t)

/-- Integration of the physical curvature bound. The sole integrability
premise concerns the explicitly displayed radiation form. -/
theorem formDerivative_sq_le (W : ConcreteWeylLaw photonMeasure)
    (p : (Fin N × Fin 3) → SpherePhoton N) (q : SphereRadiation N) (t : ℝ)
    (hT : Integrable (fun θ : Sphere N => CenteredRadialGauge.radiationForm F χ hUV e O
      (Real.exp (-t) • θ.val) (q θ)) (sphereMeasure (Fin N × Fin 3))) :
    (formDerivative F χ hUV e O C p q t) ^ 2 ≤
      (5 * (Fintype.card (Fin N × Fin 3) + 1) * curvatureConstant (N := N) F χ hUV e) ^ 2 *
      Real.exp (-t) ^ 4 * energy F χ hUV e O C p q t *
      ((∫ θ : Sphere N, CenteredRadialGauge.radiationForm F χ hUV e O (Real.exp (-t) • θ.val) (q θ)
          ∂sphereMeasure (Fin N × Fin 3)) +
        ∫ θ : Sphere N, ‖radiationGraphInclusion (q θ)‖ ^ 2 ∂sphereMeasure (Fin N × Fin 3)) := by
  have hM : Integrable (fun θ : Sphere N => ‖radiationGraphInclusion (q θ)‖ ^ 2)
      (sphereMeasure (Fin N × Fin 3)) :=
    ((radiationGraphInclusion.comp_memLp q).norm).integrable_sq
  have hbound (θ : Sphere N) := CenteredRadialGaugeAngular.physical_formDerivative_sq_le_gauged
    F χ hUV e O C W θ.val (fun j : Fin N × Fin 3 => EuclideanSpace.single j 1) t (q θ)
      (fun j => p j θ)
  have h := IntegratedFormBounds.integrated_angular_bound
    (C := 5 * (Fintype.card (Fin N × Fin 3) + 1) * curvatureConstant (N := N) F χ hUV e)
    (r := Real.exp (-t))
    (fiber_derivative_integrable F χ hUV e O C p q t)
    (fiber_energy_integrable F χ hUV e O C p q t) hT hM
    (ae_of_all _ fun θ => RadialGaugeAngular.energy_nonneg C _ (q θ) _)
    (ae_of_all _ fun θ => by
      unfold CenteredRadialGauge.radiationForm
      exact RadialGaugeRadiation.energy_nonneg _ (q θ))
    (ae_of_all _ fun _ => sq_nonneg _)
    (ae_of_all _ fun θ => by
      have hb := hbound θ
      simp only [unitSphere_norm, PiLp.norm_single, norm_one, one_pow, mul_one,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hb
      change _ ≤ _ at hb
      have hcoef : 20 * (Fintype.card (Fin N × Fin 3) : ℝ) ≤
          (5 * ((Fintype.card (Fin N × Fin 3) : ℝ) + 1)) ^ 2 := by
        nlinarith [sq_nonneg ((Fintype.card (Fin N × Fin 3) : ℝ))]
      have hK := RadialGaugeAngular.energy_nonneg C
        (fun j => coefficient F χ hUV e O j t θ) (q θ) (fun j => p j θ)
      have hT₀ : 0 ≤ CenteredRadialGauge.radiationForm F χ hUV e O (Real.exp (-t) • θ.val) (q θ) := by
        unfold CenteredRadialGauge.radiationForm
        exact RadialGaugeRadiation.energy_nonneg _ (q θ)
      have hm := mul_le_mul_of_nonneg_right hcoef (show 0 ≤
          curvatureConstant (N := N) F χ hUV e ^ 2 * Real.exp (-t) ^ 4 *
          RadialGaugeAngular.energy C (fun j => coefficient F χ hUV e O j t θ) (q θ)
            (fun j => p j θ) *
          (CenteredRadialGauge.radiationForm F χ hUV e O (Real.exp (-t) • θ.val) (q θ) +
            ‖radiationGraphInclusion (q θ)‖ ^ 2) by positivity)
      change RadialGaugeAngular.formDerivative C
          (fun j => coefficient F χ hUV e O j t θ)
          (fun j => derivativeCoefficient F χ hUV e O j t θ) (q θ) (fun j => p j θ) ^ 2 ≤ _
      change RadialGaugeAngular.formDerivative C
          (fun j => coefficient F χ hUV e O j t θ)
          (fun j => derivativeCoefficient F χ hUV e O j t θ) (q θ) (fun j => p j θ) ^ 2 ≤ _ at hb
      change _ ≤ 20 * Real.exp (-t) ^ 4 *
        (2 * Fintype.card (Fin N × Fin 3) * |e| * RadialGauge.momentBound F χ hUV) ^ 2 *
        Fintype.card (Fin N × Fin 3) *
        RadialGaugeAngular.energy C (fun j => coefficient F χ hUV e O j t θ) (q θ)
          (fun j => p j θ) *
        (CenteredRadialGauge.radiationForm F χ hUV e O (Real.exp (-t) • θ.val) (q θ) +
          ‖radiationGraphInclusion (q θ)‖ ^ 2) at hb
      unfold curvatureConstant at hm ⊢
      nlinarith only [hb, hm])
  rw [← formDerivative_eq_integral, ← energy_eq_integral] at h
  exact h

end PfHk.CenteredSphereAngularField
