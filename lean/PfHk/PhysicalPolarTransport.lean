import PfHk.PhysicalPolarDensity

/-! Return of the actual centered physical energy densities from the
conformal cylinder to the spatial ball. -/

noncomputable section
namespace PfHk.PhysicalPolarDensity

open MeasureTheory Set GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.SymmetricLift GptLean.Representability PfHk.PhysicalFieldRegularity
  PfHk.PolarCalculus PfHk.CenteredRadialGauge PfHk.CarlemanWeights
  PfHk.CarlemanSpatialDensity
open scoped ENNReal InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 20000
local instance physicalPolarTransportRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (O : Configuration N) (C : CanonicalSectorCCR photonMeasure)
  (W : ConcreteWeylLaw photonMeasure)

attribute [local irreducible] coreValue gaugedValue coreCovariant angularCore
  CenteredRadialGauge.radiationForm graphLift

private theorem weighted_three {m k r m' k' r' : ℝ}
    (hm : m = m') (hk : k = k') (hr : r = r') (w A B C : ℝ) :
    w * (A * m + B * k + C * r) = w * (A * m' + B * k' + C * r') := by
  rw [hm, hk, hr]

def cylinderDensity (q : Configuration N → RadiationGraphSpace) (τ α t : ℝ)
    (θ : UnitSphere (Fin N × Fin 3)) : ℝ :=
  let a := Real.exp (-conformalExponent (Fin N × Fin 3)*t)
  let r := Real.exp (-t)
  Real.exp (2*τ*weight α t) *
    (τ^3*beta α t*‖a • gaugedValue F χ e O W q (r • θ.val)‖^2 +
      τ*beta α t*(‖(a*r) • radialFirst (gaugedValue F χ e O W q) r θ‖^2 +
        ∑ j, ‖a • angularCore F χ hUV e O C W q r θ j‖^2) +
      τ*r^2*(a^2*CenteredRadialGauge.radiationForm F χ hUV e O (r • θ.val)
        (graphLift F χ hUV e O W (r • θ.val) (q (r • θ.val)))))

theorem cylinderDensity_eq
    (P : StandardPolarCalculus (Fin N × Fin 3) PhotonFock)
    (q : Configuration N → RadiationGraphSpace)
    (hw : ContDiff ℝ (1 : ℕ∞) (gaugedValue F χ e O W q))
    (τ α t : ℝ) (θ : UnitSphere (Fin N × Fin 3))
    (hs : SphereC1 (radialRestriction (gaugedValue F χ e O W q) (Real.exp (-t))))
    (hu : DifferentiableAt ℝ (coreValue q) (Real.exp (-t) • θ.val)) (M : ℕ)
    (hM : FiniteNumberSupport photonMeasure M (coreValue q (Real.exp (-t) • θ.val))) :
    cylinderDensity F χ hUV e O C W q τ α t θ =
      logarithmicJacobian (Fin N × Fin 3) t *
        density τ α (mass q) (kinetic F χ e O C q) (radiation q) (Real.exp (-t) • θ.val) := by
  exact (weighted_three
    (conformal_mass F χ e O W q (Real.exp (-conformalExponent (Fin N × Fin 3)*t))
      (Real.exp (-t) • θ.val))
    (conformal_kinetic F χ hUV e O C W P q hw
      (Real.exp (-conformalExponent (Fin N × Fin 3)*t)) (Real.exp_pos _) θ hs hu M hM)
    (conformal_radiation F χ hUV e O W q
      (Real.exp (-conformalExponent (Fin N × Fin 3)*t)) (Real.exp (-t) • θ.val))
    (Real.exp (2*τ*weight α t)) (τ^3*beta α t) (τ*beta α t)
    (τ*Real.exp (-t)^2)).trans
      (density_logarithmic τ α t (mass q) (kinetic F χ e O C q) (radiation q) θ).symm

theorem integral_cylinderDensity
    (P : StandardPolarCalculus (Fin N × Fin 3) PhotonFock)
    (L : StandardLogPolarCalculus (Fin N × Fin 3)) (hd : 0 < Fintype.card (Fin N × Fin 3))
    (q : Configuration N → RadiationGraphSpace)
    (hw : ContDiff ℝ (1 : ℕ∞) (gaugedValue F χ e O W q))
    (τ α t₀ : ℝ)
    (hs : ∀ t, SphereC1 (radialRestriction (gaugedValue F χ e O W q) (Real.exp (-t))))
    (hu : ∀ X, DifferentiableAt ℝ (coreValue q) X) (M : ℕ)
    (hM : ∀ X, FiniteNumberSupport photonMeasure M (coreValue q X))
    (hi : IntegrableOn (density τ α (mass q) (kinetic F χ e O C q) (radiation q))
      (Metric.ball 0 (Real.exp (-t₀)))) :
    (∫ t in Ioi t₀, ∫ θ : UnitSphere (Fin N × Fin 3),
      cylinderDensity F χ hUV e O C W q τ α t θ ∂sphereMeasure (Fin N × Fin 3)) =
      ∫ X in Metric.ball 0 (Real.exp (-t₀)),
        density τ α (mass q) (kinetic F χ e O C q) (radiation q) X := by
  rw [integral_ball_logPolar _ L hd t₀ _ hi]
  apply integral_congr_ae
  exact ae_of_all _ fun t => integral_congr_ae (ae_of_all _ fun θ =>
    cylinderDensity_eq F χ hUV e O C W P q hw τ α t θ (hs t) (hu _) M (hM _))

end PfHk.PhysicalPolarDensity
