import PfHk.PhysicalChartCore
import PfHk.PhysicalCylinderSlabSource
import PfHk.AnnularPolarMeasure

/-! Exact source pairing for an actual gauged core test on a finite slab. -/

noncomputable section
namespace PfHk.PhysicalSlabCoreForm

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.PhysicalNonattainmentFluxKernel GptLean.SymmetricLift
  GptLean.Representability PfHk.PhysicalFieldRegularity PfHk.PhysicalOperatorDomain
  PfHk.WeylGraphC1Calculus PfHk.PolarCalculus PfHk.CenteredRadialGauge
  PfHk.OrdinaryPolarSobolevChart
open scoped ENNReal InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 60000
local instance slabSourcePairPhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _
local instance slabSourcePairPhotonModule : Module ℝ PhotonFock := slabSourcePairPhotonRealInner.toNormedSpace.toModule
local instance slabSourcePairPhotonSMul : SMul ℝ PhotonFock := slabSourcePairPhotonModule.toSMul
attribute [local irreducible] gaugedReference gaugedValue coreValue graphLift
  fullRadiationInclusion fullRootProjection fullRadiationSubmodule PhysicalPFReference.referenceSubspace

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (O : Configuration N) (W : ConcreteWeylLaw photonMeasure) (B : StandardWeylGraphC1 W)
  (S : StandardPolarSobolevCharts N)
  (L : StandardLogPolarCalculus (Fin N × Fin 3)) (hN : 0 < Fintype.card (Fin N × Fin 3))
  (l r : ℝ) (a : SmoothCore (annulus N l r))
  {s : Set (Configuration N)} {f : PhysicalPFReference.WaveSpace (Fin N × Fin 3)} (g : CompactSource s f)

include L hN in
theorem source_pair_eq_original :
    inner ℝ ((S.chart (conformalExponent (Fin N × Fin 3)) l r).value
      (gaugedReference F χ hUV e O W B a))
      (PhysicalCylinderSource.slabSource F χ e O W g (conformalExponent (Fin N × Fin 3)) l r) =
      2 * (inner ℂ (PhysicalPFReference.inclusion (Fin N × Fin 3) (fun _ => 0) a.reference) f).re := by
  let c := conformalExponent (Fin N × Fin 3)
  let original := fun X => inner ℝ (fullRadiationInclusion (a.representative X)) (g.representative X)
  have hi := l2_inner_integrable
    (PhysicalPFReference.inclusion (Fin N × Fin 3) (fun _ => 0) a.reference) f
    a.reference_value_ae g.agrees
  have hp := integral_annular_slab L hN l r (fun X => 2 * original X) (hi.const_mul 2)
    (fun X hX => by
      have hz : a.representative X = 0 := image_eq_zero_of_notMem_tsupport (fun hx => hX (a.support hx))
      have hz' := congrArg (fun q : FullRadiationGraph => fullRadiationInclusion q) hz
      have hzero : fullRadiationInclusion (a.representative X) = 0 :=
        hz'.trans (map_zero fullRadiationInclusion)
      change 2 * inner ℝ (fullRadiationInclusion (a.representative X)) (g.representative X) = 0
      rw [hzero]
      simp only [inner_zero_left, mul_zero])
  have he := l2_inner_eq_integral
    ((S.chart c l r).value (gaugedReference F χ hUV e O W B a))
    (PhysicalCylinderSource.slabSource F χ e O W g c l r)
    (PhysicalChartCore.value_ae F χ hUV e O W B S a).ae
    (PhysicalCylinderSource.slabSource_ae F χ e O W g c l r)
  have hraw := l2_inner_eq_integral
    (PhysicalPFReference.inclusion (Fin N × Fin 3) (fun _ => 0) a.reference) f
    a.reference_value_ae g.agrees
  apply he.trans
  calc
    _ = ∫ p : Slab N, logarithmicJacobian (Fin N × Fin 3) p.1 * (2 * original (chartPoint N p))
        ∂slabMeasure N l r := by
      apply integral_congr_ae
      exact ae_of_all _ fun p => by
        have hs := PhysicalCylinderSource.source_pair F χ e O W g p
          (fullRadiationInclusion (a.representative (chartPoint N p)))
        have hvalue : gaugedValue F χ e O W a.rootWave (chartPoint N p) =
            unitary F χ e O W (logarithmicPoint p)
              (fullRadiationInclusion (a.representative (chartPoint N p))) := by
          unfold gaugedValue coreValue SmoothCore.rootWave fullRadiationInclusion
          rfl
        change inner ℝ (Real.exp (-c*p.1) • gaugedValue F χ e O W a.rootWave (chartPoint N p))
          (PhysicalCylinderSource.value F χ e O W g c p) = _
        have hh := SlabFormAlgebra.scaled_inner_congr (Real.exp (-c*p.1))
          (PhysicalCylinderSource.value F χ e O W g c p) hvalue
        apply hh.trans
        apply hs.trans
        change 2 * logarithmicJacobian (Fin N × Fin 3) p.1 *
          inner ℝ (fullRadiationInclusion (a.representative (chartPoint N p)))
            (g.representative (chartPoint N p)) = _
        unfold original
        ring
    _ = ∫ X, 2 * original X := hp.symm
    _ = 2 * ∫ X, original X := integral_const_mul 2 original
    _ = 2 * inner ℝ (PhysicalPFReference.inclusion (Fin N × Fin 3) (fun _ => 0) a.reference) f :=
      congrArg (fun x : ℝ => 2 * x) hraw.symm
    _ = _ := congrArg (fun x : ℝ => 2 * x)
      (real_inner_eq_complex_re
        (PhysicalPFReference.inclusion (Fin N × Fin 3) (fun _ => 0) a.reference) f)

end PfHk.PhysicalSlabCoreForm
