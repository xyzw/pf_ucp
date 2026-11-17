import PfHk.PhysicalCylinderSource
import PfHk.PhysicalPolarDensity

/-! The norm of the actual transformed operator source is exactly four
times the physical spatial source integral. -/

noncomputable section
namespace PfHk.PhysicalCylinderSource

open MeasureTheory Set GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.SymmetricLift GptLean.Representability PfHk.PhysicalFieldRegularity
  PfHk.PhysicalOperatorDomain PfHk.PolarCalculus PfHk.CenteredRadialGauge
  PfHk.CarlemanWeights
open PfHk.SphereAngularField (Sphere SpherePhoton)
open scoped InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 20000
local instance sourceNormTransportRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _
attribute [local irreducible] CenteredRadialGauge.unitary source

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (e : ℝ)
  (O : Configuration N) (W : ConcreteWeylLaw photonMeasure)
  {s : Set (Configuration N)}
  {f : PhysicalPFReference.WaveSpace (Fin N × Fin 3)} (g : CompactSource s f)

theorem weighted_source_norm (τ α c t : ℝ) :
    Real.exp (2*τ*weight α t)*‖source F χ e O W g c t‖^2 =
      ∫ θ : Sphere N, Real.exp (2*τ*weight α t)*
        ((2*Real.exp (-(c+2)*t))^2*‖g.representative (Real.exp (-t) • θ.val)‖^2)
        ∂sphereMeasure (Fin N × Fin 3) := by
  have h := L2QuadraticForms.scaled_norm_eq_integral (Real.exp (2*τ*weight α t))
    (source F χ e O W g c t) (source_ae F χ e O W g c t)
  apply h.trans
  apply integral_congr_ae
  exact ae_of_all _ fun θ => by
    dsimp only
    rw [PhysicalPolarDensity.norm_real_smul_sq, (unitary F χ e O W _).norm_map]

theorem weighted_source_integral
    (L : StandardLogPolarCalculus (Fin N × Fin 3)) (hd : 0 < Fintype.card (Fin N × Fin 3))
    (τ α t₀ : ℝ)
    (hi : IntegrableOn (CarlemanSpatialDensity.source τ α (fun X => ‖f X‖^2))
      (Metric.ball 0 (Real.exp (-t₀)))) :
    (∫ t in Ioi t₀, Real.exp (2*τ*weight α t)*
      ‖source F χ e O W g (conformalExponent (Fin N × Fin 3)) t‖^2) =
      4*∫ X in Metric.ball 0 (Real.exp (-t₀)),
        CarlemanSpatialDensity.source τ α (fun Y => ‖f Y‖^2) X := by
  have he : CarlemanSpatialDensity.source τ α (fun X => ‖f X‖^2) =ᵐ[volume]
      CarlemanSpatialDensity.source τ α (fun X => ‖g.representative X‖^2) := by
    filter_upwards [g.agrees] with X hX
    exact congrArg (fun v : PhotonFock =>
      Real.exp (2*τ*weight α (-Real.log ‖X‖))*‖X‖^2*‖v‖^2) hX
  have hi' := hi.congr (ae_restrict_of_ae he)
  calc
    _ = ∫ t in Ioi t₀, ∫ θ : Sphere N, Real.exp (2*τ*weight α t)*
        ((2*Real.exp (-(conformalExponent (Fin N × Fin 3)+2)*t))^2*
          ‖g.representative (Real.exp (-t) • θ.val)‖^2) ∂sphereMeasure (Fin N × Fin 3) :=
      integral_congr_ae (ae_of_all _ fun t => weighted_source_norm F χ e O W g τ α _ t)
    _ = 4*∫ X in Metric.ball 0 (Real.exp (-t₀)),
        CarlemanSpatialDensity.source τ α (fun Y => ‖g.representative Y‖^2) X :=
      CarlemanSpatialDensity.integral_source L hd τ α t₀ _ hi'
    _ = _ := congrArg (fun z : ℝ => 4*z) (integral_congr_ae (ae_restrict_of_ae he.symm))

end PfHk.PhysicalCylinderSource
