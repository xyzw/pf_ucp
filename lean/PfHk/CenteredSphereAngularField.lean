import PfHk.SpatialFieldParameterDerivative
import PfHk.CenteredRadialGauge
import PfHk.PhysicalSphereSpace

/-! The actual physical angular Segal fields on L2 of the unit sphere.
Their strong logarithmic derivative is proved from the physical curvature
formula and uniform local difference-quotient bounds. -/

noncomputable section
namespace PfHk.CenteredSphereAngularField

open MeasureTheory Filter GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.SymmetricLift GptLean.Representability PfHk.PhysicalFieldRegularity
  PfHk.CenteredRadialGauge PfHk.PolarCalculus PfHk.SphereAngularField
open PfHk.RadialGauge (curvatureConstant curvatureConstant_nonneg)
open scoped ENNReal Topology InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 600000

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ) (O : Configuration N)

def coefficient (j : Fin N × Fin 3) (t : ℝ) (θ : Sphere N) : WeightedPhotonKernel :=
  angularLabel F χ hUV e O θ.val (EuclideanSpace.single j 1) (Real.exp (-t))

def derivativeCoefficient (j : Fin N × Fin 3) (t : ℝ) (θ : Sphere N) : WeightedPhotonKernel :=
  (-(Real.exp (-t) ^ 2)) •
    curvature F χ hUV e O (Real.exp (-t) • θ.val) θ.val (EuclideanSpace.single j 1)

def coefficientBound (t : ℝ) : ℝ :=
  Real.exp (-t) ^ 2 * curvatureConstant (N := N) F χ hUV e

def localDerivativeBound (t : ℝ) : ℝ :=
  Real.exp (2 - 2 * t) * curvatureConstant (N := N) F χ hUV e

theorem coefficient_measurable (j : Fin N × Fin 3) (t : ℝ) :
    AEStronglyMeasurable (coefficient F χ hUV e O j t) (sphereMeasure (Fin N × Fin 3)) :=
  ((angularLabel_continuous_theta F χ hUV e O (EuclideanSpace.single j 1) (Real.exp (-t))).comp
    continuous_subtype_val).aestronglyMeasurable

theorem derivativeCoefficient_measurable (j : Fin N × Fin 3) (t : ℝ) :
    AEStronglyMeasurable (derivativeCoefficient F χ hUV e O j t) (sphereMeasure (Fin N × Fin 3)) :=
  ((angularDerivative_continuous_theta F χ hUV e O (EuclideanSpace.single j 1) t).comp
    continuous_subtype_val).aestronglyMeasurable

theorem coefficient_bound (j : Fin N × Fin 3) (t : ℝ) :
    ∀ᵐ θ ∂sphereMeasure (Fin N × Fin 3),
      ‖coefficient F χ hUV e O j t θ‖ ≤ coefficientBound (N := N) F χ hUV e t := by
  apply ae_of_all
  intro θ
  exact angularLabel_norm_le F χ hUV e O θ.val (EuclideanSpace.single j 1)
    (by rw [unitSphere_norm]) (by simp) (Real.exp_pos _).le

theorem derivativeCoefficient_bound (j : Fin N × Fin 3) (t : ℝ) :
    ∀ᵐ θ ∂sphereMeasure (Fin N × Fin 3),
      ‖derivativeCoefficient F χ hUV e O j t θ‖ ≤ localDerivativeBound (N := N) F χ hUV e t := by
  apply ae_of_all
  intro θ
  have h := angular_derivative_norm_le F χ hUV e O θ.val (EuclideanSpace.single j 1) t
  simp only [unitSphere_norm, PiLp.norm_single, norm_one, mul_one] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (by linarith : -2 * t ≤ 2 - 2 * t))
    (curvatureConstant_nonneg (N := N) F χ hUV e))

variable (C : CanonicalSectorCCR photonMeasure)

def field (j : Fin N × Fin 3) (t : ℝ) : SphereRadiation N →L[ℂ] SpherePhoton N :=
  spatialField (sphereMeasure (Fin N × Fin 3)) C (coefficient F χ hUV e O j t)
    (coefficient_measurable F χ hUV e O j t) (coefficientBound (N := N) F χ hUV e t)
    (coefficient_bound F χ hUV e O j t)

def fieldDerivative (j : Fin N × Fin 3) (t : ℝ) : SphereRadiation N →L[ℂ] SpherePhoton N :=
  spatialField (sphereMeasure (Fin N × Fin 3)) C (derivativeCoefficient F χ hUV e O j t)
    (derivativeCoefficient_measurable F χ hUV e O j t) (localDerivativeBound (N := N) F χ hUV e t)
    (derivativeCoefficient_bound F χ hUV e O j t)

/-- Strong differentiation on the true sphere Hilbert space, with the
fixed vector allowed to occupy all photon sectors. -/
theorem field_hasDerivAt (j : Fin N × Fin 3) (t : ℝ) (q : SphereRadiation N) :
    L2OperatorDerivative.HasL2DerivAt (E := PhotonFock)
      (fun s => field F χ hUV e O C j s q) (fieldDerivative F χ hUV e O C j t q) t := by
  apply SpatialFieldParameterDerivative.spatialField_hasDerivAt C
    (sphereMeasure (Fin N × Fin 3)) (coefficient F χ hUV e O j)
    (coefficient_measurable F χ hUV e O j) (coefficientBound (N := N) F χ hUV e)
    (coefficient_bound F χ hUV e O j) (derivativeCoefficient F χ hUV e O j t)
    (derivativeCoefficient_measurable F χ hUV e O j t) (localDerivativeBound (N := N) F χ hUV e t)
    (mul_nonneg (Real.exp_pos _).le (curvatureConstant_nonneg (N := N) F χ hUV e))
    (derivativeCoefficient_bound F χ hUV e O j t) t q
  · exact ae_of_all _ fun θ =>
      angularLabel_logarithmic_hasDerivAt F χ hUV e O θ.val (EuclideanSpace.single j 1) t
  · have he : Set.Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
    have he' : ∀ᶠ h in 𝓝[≠] (0 : ℝ), h ∈ Set.Ioo (-1 : ℝ) 1 :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds he
    filter_upwards [he'] with h hh
    exact ae_of_all _ fun θ => angularLabel_logarithmic_slope_bound F χ hUV e O θ.val
      (EuclideanSpace.single j 1) (by rw [unitSphere_norm]) (by simp) t h
      (abs_le.mpr ⟨hh.1.le, hh.2.le⟩)

end PfHk.CenteredSphereAngularField
