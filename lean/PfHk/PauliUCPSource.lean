import PfHk.PauliSupportedCutoffEquation
import PfHk.SmoothCutoffOperations

/-! Annular cutoffs at nearby centers have the exact localized Pauli
source. Their support is derived from the actual buffered cutoffs and
the coefficient-ball geometry. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliUCPSource

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.SymmetricLift GptLean.Representability
  GptLean.ElectronicH1Multiplier PfHk.PauliSpin PfHk.PauliGroundState
  PfHk.PauliLocalEnergy PfHk.PhysicalLocalEnergy PfHk.PhysicalFieldRegularity
  PfHk.CenteredPhysicalReference PfHk.PhysicalOperatorDomain
  PfHk.WeylGraphC1Calculus PfHk.WeylCoreReference
  PfHk.FriedrichsDivergenceBackground PfHk.SmoothCutoffBounds
  PfHk.PhysicalCutoffCommutator

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000

attribute [local irreducible] referenceSubspace inclusion rawForm
  PhysicalPFScalarMultiplier.multiply PauliLocalEnergy.localize

variable {N : ℕ} {O y : Configuration N} {ρ R ε : ℝ}

theorem annular_supported (hρ : 0 < ρ) (hy : y ∈ Metric.ball O (ρ / 64))
    (hR : 0 < R) (hRρ : R ≤ ρ / 64) (hε : 0 < ε) (hεR : ε ≤ R / 4)
    (family : BufferedFamily y) :
    ∀ X, X ∉ Metric.ball O (ρ / 4) →
      (twiceSub (family.cutoff (R / 2)) (family.cutoff ε)).scalar.weight X = 0 := by
  intro X hX
  have hyO : dist y O < ρ / 64 := Metric.mem_ball.mp hy
  have hXR : R ≤ dist X y := by
    by_contra! h
    apply hX
    apply Metric.mem_ball.mpr
    have ht := dist_triangle X y O
    linarith only [h, hyO, ht, hRρ, hρ]
  have hout := BufferedCutoffLocality.cutoff_supported family (half_pos hR) X
    (by change ¬ dist X y < 2 * (R / 2); linarith only [hXR])
  have hin := BufferedCutoffLocality.cutoff_supported family hε X
    (by change ¬ dist X y < 2 * ε; linarith only [hXR, hεR, hR])
  change (family.cutoff (R / 2)).scalar.weight X - (family.cutoff ε).scalar.weight X = 0
  exact sub_eq_zero.mpr (hout.trans hin.symm)

variable (a : PauliLocalDomain.Data O ρ) (hρ : 0 < ρ)
  (C : CanonicalSectorCCR photonMeasure) (F : Frame) (χ : ArticleCutoff) (e : ℝ)
  (S : CoordinateSobolev.Data PhotonFock N)
  (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
  (joint : CoordinateComparisonSpectral.Data spectral)
  (friedrichs : StandardFriedrichsDivergence)
  (hUV : CarlemanUV χ) (W : ConcreteWeylLaw photonMeasure)
  (G : StandardWeylGraphC1 W) (D : StandardWeylFormCoreDensity W G)

include hρ S spectral joint friedrichs hUV W G D in
theorem annular_local_operatorPair (hy : y ∈ Metric.ball O (ρ / 64))
    (hR : 0 < R) (hRρ : R ≤ ρ / 64) (hε : 0 < ε) (hεR : ε ≤ R / 4)
    (family : BufferedFamily y) (E : ℝ) (u : Ref N)
    (hu : Domain a.orbital.vector a.orbital.positive a.orbital.negative u)
    (heigen : IsWeakEigenstate C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e a.orbital.vector a.orbital.positive
      a.orbital.negative E u hu) :
    let η := twiceSub (family.cutoff (R / 2)) (family.cutoff ε)
    PauliLocalOperatorTransfer.IsLocalOperatorPair C F χ e a.orbital.vector
      a.orbital.positive a.orbital.negative (Metric.ball O (ρ / 2))
      (localize η.scalar u) (domain_localize hu η.scalar)
      (fun s => PauliLocalCutoffRules.commutator C (profile F χ 0)
        (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e
        a.orbital.vector a.orbital.positive a.orbital.negative η u hu s +
        (E : ℂ) • inclusion (Fin N × Fin 3) (fun _ => 0) (localize η.scalar u s)) :=
  PauliSupportedCutoffEquation.eigenstate_local_operatorPair a hρ C F χ e
    S spectral joint friedrichs hUV W G D
    (twiceSub (family.cutoff (R / 2)) (family.cutoff ε))
    (annular_supported hρ hy hR hRρ hε hεR family) E u hu heigen
    (Metric.ball O (ρ / 2))

end PfHk.PauliUCPSource

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
