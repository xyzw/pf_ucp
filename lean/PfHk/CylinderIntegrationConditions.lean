import PfHk.CylinderEstimate

/-! Ordinary boundary and integrability conditions for the cylinder
integration. They contain no differential identity or coercivity bound. -/

noncomputable section
namespace PfHk.CylinderEstimate

open MeasureTheory Filter Set CylinderIdentity
open scoped InnerProductSpace Topology
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

structure IntegrationConditions (τ c t₀ : ℝ) (p b db ddb r kv qv : ℝ → ℝ)
    (z dz ddz k q : ℝ → H) : Prop where
  boundary_zero : boundaryFlux τ c p b db r z dz k q t₀ = 0
  boundary_infty : Tendsto (boundaryFlux τ c p b db r z dz k q) atTop (𝓝 0)
  multiplier_zero : multiplierFlux b db z dz t₀ = 0
  multiplier_infty : Tendsto (multiplierFlux b db z dz) atTop (𝓝 0)
  symmetric_integrable : IntegrableOn (fun t => ‖symmetricPart τ c p r z ddz k q t‖ ^ 2) (Ioi t₀)
  skew_integrable : IntegrableOn (fun t => ‖skewPart τ p b z dz t‖ ^ 2) (Ioi t₀)
  cross_integrable : IntegrableOn (fun t => 2 * inner ℝ
    (symmetricPart τ c p r z ddz k q t) (skewPart τ p b z dz t)) (Ioi t₀)
  commutator_integrable : IntegrableOn (commutatorDensity τ p b ddb r kv qv z dz q) (Ioi t₀)
  multiplier_integrable : IntegrableOn (multiplierDensity τ c p b ddb r z dz k q) (Ioi t₀)
  pairing_integrable : IntegrableOn (fun t =>
    inner ℝ (symmetricPart τ c p r z ddz k q t) (b t • z t)) (Ioi t₀)
  retained_integrable : IntegrableOn (retained τ c p b r z dz ddz k q) (Ioi t₀)

end PfHk.CylinderEstimate
