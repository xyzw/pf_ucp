import PfHk.CarlemanPolarMeasure
import PfHk.CarlemanWeights

/-! The exact physical radial weights and their logarithmic polar
integrals. The three scalar densities can be instantiated by the actual
mass, covariant kinetic energy, and radiation energy. -/

noncomputable section
namespace PfHk.CarlemanSpatialDensity

open MeasureTheory Set PfHk.PolarCalculus PfHk.CarlemanWeights
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

variable {I : Type*} [Fintype I] [DecidableEq I]

def density (τ α : ℝ) (M D R : Position I → ℝ) (X : Position I) : ℝ :=
  Real.exp (2*τ*weight α (-Real.log ‖X‖)) *
    (τ^3*beta α (-Real.log ‖X‖)*(‖X‖^2)⁻¹*M X +
      τ*beta α (-Real.log ‖X‖)*D X + 2*τ*R X)

def source (τ α : ℝ) (S : Position I → ℝ) (X : Position I) : ℝ :=
  Real.exp (2*τ*weight α (-Real.log ‖X‖)) * ‖X‖^2 * S X

theorem logarithmic_norm (t : ℝ) (θ : UnitSphere I) :
    ‖Real.exp (-t) • θ.val‖ = Real.exp (-t) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), unitSphere_norm, mul_one]

theorem logarithmic_coordinate (t : ℝ) (θ : UnitSphere I) :
    -Real.log ‖Real.exp (-t) • θ.val‖ = t := by
  rw [logarithmic_norm, Real.log_exp, neg_neg]

theorem density_logarithmic (τ α t : ℝ) (M D R : Position I → ℝ) (θ : UnitSphere I) :
    logarithmicJacobian I t * density τ α M D R (Real.exp (-t) • θ.val) =
      Real.exp (2*τ*weight α t) *
        (τ^3*beta α t*(Real.exp (-conformalExponent I*t)^2*M (Real.exp (-t) • θ.val)) +
          τ*beta α t*(Real.exp (-conformalExponent I*t)^2*Real.exp (-t)^2*D (Real.exp (-t) • θ.val)) +
          τ*Real.exp (-t)^2*(2*Real.exp (-conformalExponent I*t)^2*R (Real.exp (-t) • θ.val))) := by
  unfold density
  rw [logarithmic_coordinate, logarithmic_norm, density_factors]
  ring

theorem source_logarithmic (τ α t : ℝ) (S : Position I → ℝ) (θ : UnitSphere I) :
    Real.exp (2*τ*weight α t) *
      ((2*Real.exp (-(conformalExponent I+2)*t))^2*S (Real.exp (-t) • θ.val)) =
      4*logarithmicJacobian I t*source τ α S (Real.exp (-t) • θ.val) := by
  unfold source
  rw [logarithmic_coordinate, logarithmic_norm, source_factor]
  ring

theorem integral_density (P : StandardLogPolarCalculus I) (hd : 0 < Fintype.card I)
    (τ α t₀ : ℝ) (M D R : Position I → ℝ)
    (hi : IntegrableOn (density τ α M D R) (Metric.ball 0 (Real.exp (-t₀)))) :
    (∫ X in Metric.ball 0 (Real.exp (-t₀)), density τ α M D R X) =
      ∫ t in Ioi t₀, ∫ θ : UnitSphere I,
        Real.exp (2*τ*weight α t) *
          (τ^3*beta α t*(Real.exp (-conformalExponent I*t)^2*M (Real.exp (-t) • θ.val)) +
            τ*beta α t*(Real.exp (-conformalExponent I*t)^2*Real.exp (-t)^2*D (Real.exp (-t) • θ.val)) +
            τ*Real.exp (-t)^2*(2*Real.exp (-conformalExponent I*t)^2*R (Real.exp (-t) • θ.val)))
        ∂sphereMeasure I := by
  rw [integral_ball_logPolar I P hd t₀ _ hi]
  apply integral_congr_ae
  exact ae_of_all _ fun t => integral_congr_ae (ae_of_all _ fun θ =>
    density_logarithmic τ α t M D R θ)

theorem integral_source (P : StandardLogPolarCalculus I) (hd : 0 < Fintype.card I)
    (τ α t₀ : ℝ) (S : Position I → ℝ)
    (hi : IntegrableOn (source τ α S) (Metric.ball 0 (Real.exp (-t₀)))) :
    (∫ t in Ioi t₀, ∫ θ : UnitSphere I,
      Real.exp (2*τ*weight α t) *
        ((2*Real.exp (-(conformalExponent I+2)*t))^2*S (Real.exp (-t) • θ.val)) ∂sphereMeasure I) =
      4*∫ X in Metric.ball 0 (Real.exp (-t₀)), source τ α S X := by
  rw [integral_ball_logPolar I P hd t₀ _ hi, ← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun t => by
    dsimp only
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun θ => by
      dsimp only
      rw [source_logarithmic]
      ring

end PfHk.CarlemanSpatialDensity
