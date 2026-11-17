import PfHk.PhysicalCylinderSlabSource
import PfHk.SeparatedSlabIntegration
import PfHk.PolarChartEvaluation

/-! Evaluation of the actual source against a separated sphere test. -/

noncomputable section
namespace PfHk.PhysicalSlabCoreForm

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.SymmetricLift GptLean.Representability PfHk.PhysicalOperatorDomain
  PfHk.PolarCalculus PfHk.SphereCoreGeometry PfHk.OrdinaryPolarSobolevChart
open scoped InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000
local instance separatedSourceRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _
local instance separatedSourcePhotonModule : Module ℝ PhotonFock := separatedSourceRealInner.toNormedSpace.toModule
local instance separatedSourcePhotonSMul : SMul ℝ PhotonFock := separatedSourcePhotonModule.toSMul
attribute [local irreducible] valueAt LpRepresents PhysicalPFReference.referenceSubspace
  PhysicalCylinderSource.source PhysicalCylinderSource.slabSource

private theorem separated_pair {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {μ : Measure ℝ} {ν : Measure X} [SFinite μ] [SFinite ν]
    (η : ℝ → ℝ) (v : Lp H 2 ν) (q : ℝ → Lp H 2 ν)
    (a b : Lp H 2 (μ.prod ν)) {vf : X → H} {qf : ℝ → X → H}
    (ha : a =ᵐ[μ.prod ν] fun p => η p.1 • vf p.2)
    (hb : b =ᵐ[μ.prod ν] fun p => qf p.1 p.2)
    (hv : v =ᵐ[ν] vf) (hq : ∀ t, q t =ᵐ[ν] qf t) :
    inner ℝ a b = ∫ t, η t * inner ℝ v (q t) ∂μ :=
  (l2_inner_eq_integral a b ha hb).trans
    (SeparatedSlabIntegration.source_integral η v q hv hq
      (l2_inner_integrable a b ha hb))

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (e : ℝ)
  (O : Configuration N) (W : ConcreteWeylLaw photonMeasure)
  {s : Set (Configuration N)} {f : PhysicalPFReference.WaveSpace (Fin N × Fin 3)}
  (g : CompactSource s f) {c l r : ℝ} (P : SobolevChart N c l r)
  (u : PhysicalPFReference.Reference (Fin N × Fin 3) (fun _ => 0))
  (v : CoreVector N) (η : ℝ → ℝ)

theorem source_test_eq
    (hv : LpRepresents (slabMeasure N l r) (valueAt P u) (fun p => η p.1 • v.ambient p.2)) :
    inner ℝ (valueAt P u) (PhysicalCylinderSource.slabSource F χ e O W g c l r) =
      ∫ t in Set.Icc l r, η t * inner ℝ v.ambient (PhysicalCylinderSource.source F χ e O W g c t) := by
  exact separated_pair (H := PhotonFock)
    (μ := (volume : Measure ℝ).restrict (Set.Icc l r))
    (ν := sphereMeasure (Fin N × Fin 3)) η v.ambient
    (PhysicalCylinderSource.source F χ e O W g c) (valueAt P u)
    (PhysicalCylinderSource.slabSource F χ e O W g c l r)
    (qf := fun t θ => PhysicalCylinderSource.value F χ e O W g c (t, θ))
    hv.ae (PhysicalCylinderSource.slabSource_ae F χ e O W g c l r)
    Filter.EventuallyEq.rfl (PhysicalCylinderSource.source_ae F χ e O W g c)

end PfHk.PhysicalSlabCoreForm
