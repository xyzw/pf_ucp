import PfHk.CenteredRadialGaugePolar
import PfHk.CarlemanSpatialDensity

/-! The actual mass, covariant kinetic, and radiation densities under
the centered Weyl gauge and conformal polar scaling. -/

noncomputable section
namespace PfHk.PhysicalPolarDensity

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.PhysicalNonattainmentFluxKernel GptLean.SymmetricLift
  GptLean.Representability PfHk.PhysicalFieldRegularity PfHk.PolarCalculus
  PfHk.CenteredRadialGauge PfHk.CarlemanWeights PfHk.CarlemanSpatialDensity
open scoped ENNReal InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000
local instance physicalPolarDensityRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _

theorem norm_real_smul_sq {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (a : ℝ) (v : H) : ‖a • v‖^2 = a^2*‖v‖^2 := by
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (O : Configuration N) (C : CanonicalSectorCCR photonMeasure)
  (W : ConcreteWeylLaw photonMeasure)

attribute [local irreducible] coreValue gaugedValue coreCovariant angularCore
  CenteredRadialGauge.radiationForm graphLift

def mass (q : Configuration N → RadiationGraphSpace) (X : Configuration N) : ℝ :=
  ‖coreValue q X‖^2

def kinetic (q : Configuration N → RadiationGraphSpace) (X : Configuration N) : ℝ :=
  ∑ j, ‖coreCovariant F χ e O C q j X‖^2

def radiation (q : Configuration N → RadiationGraphSpace) (X : Configuration N) : ℝ :=
  ‖radiationGraphDerivative (q X)‖^2

theorem conformal_mass (q : Configuration N → RadiationGraphSpace)
    (a : ℝ) (X : Configuration N) :
    ‖a • gaugedValue F χ e O W q X‖^2 = a^2*mass q X := by
  rw [norm_real_smul_sq]
  unfold gaugedValue mass
  rw [(unitary F χ e O W X).norm_map]

theorem conformal_kinetic
    (P : StandardPolarCalculus (Fin N × Fin 3) PhotonFock)
    (q : Configuration N → RadiationGraphSpace)
    (hw : ContDiff ℝ (1 : ℕ∞) (gaugedValue F χ e O W q))
    (a : ℝ) {r : ℝ} (hr : 0 < r) (θ : UnitSphere (Fin N × Fin 3))
    (hs : SphereC1 (radialRestriction (gaugedValue F χ e O W q) r))
    (hu : DifferentiableAt ℝ (coreValue q) (r • θ.val)) (M : ℕ)
    (hM : FiniteNumberSupport photonMeasure M (coreValue q (r • θ.val))) :
    ‖(a*r) • radialFirst (gaugedValue F χ e O W q) r θ‖^2 +
      (∑ j, ‖a • angularCore F χ hUV e O C W q r θ j‖^2) =
      a^2*r^2*kinetic F χ e O C q (r • θ.val) := by
  have h := physical_polar_kinetic F χ hUV e O P C W q hw hr θ hs hu M hM
  simp_rw [norm_real_smul_sq]
  rw [← Finset.mul_sum]
  unfold kinetic
  rw [mul_pow]
  calc
    _ = a^2*(r^2*‖radialFirst (gaugedValue F χ e O W q) r θ‖^2 +
      ∑ j, ‖angularCore F χ hUV e O C W q r θ j‖^2) := by ring
    _ = _ := by rw [← h]; ring

theorem conformal_radiation (q : Configuration N → RadiationGraphSpace)
    (a : ℝ) (X : Configuration N) :
    a^2*CenteredRadialGauge.radiationForm F χ hUV e O X (graphLift F χ hUV e O W X (q X)) =
      2*a^2*radiation q X := by
  rw [radiationForm_graphLift]
  unfold radiation
  ring

theorem conformal_source (f : Configuration N → PhotonFock)
    (τ α t : ℝ) (θ : UnitSphere (Fin N × Fin 3)) :
    Real.exp (2*τ*weight α t) *
      ‖(2*Real.exp (-(conformalExponent (Fin N × Fin 3)+2)*t)) •
        unitary F χ e O W (Real.exp (-t) • θ.val) (f (Real.exp (-t) • θ.val))‖^2 =
      4*logarithmicJacobian (Fin N × Fin 3) t*
        source τ α (fun X => ‖f X‖^2) (Real.exp (-t) • θ.val) := by
  rw [norm_real_smul_sq, (unitary F χ e O W _).norm_map]
  exact source_logarithmic τ α t (fun X => ‖f X‖^2) θ

end PfHk.PhysicalPolarDensity
