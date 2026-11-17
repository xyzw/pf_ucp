import PfHk.WeylCoreReference
import PfHk.CenteredRadialGaugeCoreRegularity

/-! Physical specialization of universal Weyl form-core density. The
actual physical label regularity discharges every displacement premise.
The target topology is the existing free Reference graph norm. -/

noncomputable section
namespace PfHk.CenteredRadialGauge

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.PhysicalNonattainmentFluxKernel GptLean.SymmetricLift
  GptLean.Representability PfHk.PhysicalFieldRegularity PfHk.PhysicalOperatorDomain
  PfHk.WeylGraphC1Calculus
open scoped ENNReal Topology
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 250000
attribute [local irreducible] label sqrtLabel graphLift

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (O : Configuration N) (W : ConcreteWeylLaw photonMeasure)
  (B : StandardWeylGraphC1 W)

def weightedLabel (X : Configuration N) : WeightedPhotonKernel := Complex.I • label F χ e O X

include hUV in
theorem weightedLabel_contDiff : ContDiff ℝ (1 : ℕ∞) (weightedLabel F χ e O) :=
  (label_contDiff F χ hUV e O).const_smul Complex.I

def weightedEnergyLabel (X : Configuration N) : Lp ℂ 2 photonMeasure :=
  Complex.I • sqrtLabel F χ hUV e O X

theorem weightedEnergyLabel_continuous : Continuous (weightedEnergyLabel F χ hUV e O) :=
  (sqrtLabel_continuous F χ hUV e O).const_smul Complex.I

theorem weightedEnergyLabel_relation (X : Configuration N) :
    ∀ᵐ p ∂photonMeasure, weightedEnergyLabel F χ hUV e O X p =
      (Real.sqrt ‖p.1‖ : ℂ) * (weightedLabel F χ e O X).val.1 p :=
  imaginary_label_relation F χ hUV e O X

def gaugedReference {s : Set (Configuration N)} (a : SmoothCore s) :
    PhysicalPFReference.Reference (Fin N × Fin 3) (fun _ => 0) :=
  WeylCoreReference.reference W B (weightedLabel F χ e O) (weightedLabel_contDiff F χ hUV e O)
    (weightedEnergyLabel F χ hUV e O) (weightedEnergyLabel_continuous F χ hUV e O)
    (weightedEnergyLabel_relation F χ hUV e O) a

theorem gaugedReference_value_ae {s : Set (Configuration N)} (a : SmoothCore s) :
    PhysicalPFReference.inclusion (Fin N × Fin 3) (fun _ => 0)
      (gaugedReference F χ hUV e O W B a) =ᵐ[volume] gaugedValue F χ e O W a.rootWave := by
  have h := WeylCoreReference.reference_value_ae W B (weightedLabel F χ e O)
    (weightedLabel_contDiff F χ hUV e O) (weightedEnergyLabel F χ hUV e O)
    (weightedEnergyLabel_continuous F χ hUV e O) (weightedEnergyLabel_relation F χ hUV e O) a
  convert! h using 1

theorem gaugedReference_graph_ae {s : Set (Configuration N)} (a : SmoothCore s) :
    PhysicalPFReference.radiationSource (Fin N × Fin 3) (fun _ => 0)
      (gaugedReference F χ hUV e O W B a) =ᵐ[volume]
      fun X => graphLift F χ hUV e O W X (a.rootWave X) := by
  have h := WeylCoreReference.reference_graph_ae W B (weightedLabel F χ e O)
    (weightedLabel_contDiff F χ hUV e O) (weightedEnergyLabel F χ hUV e O)
    (weightedEnergyLabel_continuous F χ hUV e O) (weightedEnergyLabel_relation F χ hUV e O) a
  convert! h using 1
  funext X
  unfold WeylCoreReference.graph graphLift weightedLabel weightedEnergyLabel
  rfl

theorem gaugedReference_ordinary_ae {s : Set (Configuration N)} (a : SmoothCore s)
    (j : Fin N × Fin 3) :
    PhysicalPFReference.ordinary (Fin N × Fin 3) (fun _ => 0) j
      (gaugedReference F χ hUV e O W B a) =ᵐ[volume]
      fun X => fderiv ℝ (gaugedValue F χ e O W a.rootWave) X (EuclideanSpace.single j 1) := by
  have h := WeylCoreReference.reference_ordinary_ae W B (weightedLabel F χ e O)
    (weightedLabel_contDiff F χ hUV e O) (weightedEnergyLabel F χ hUV e O)
    (weightedEnergyLabel_continuous F χ hUV e O) (weightedEnergyLabel_relation F χ hUV e O) a j
  convert! h using 1

theorem form_core_approximation (D : WeylCoreReference.StandardWeylFormCoreDensity W B)
    (s : Set (Configuration N)) (hs : IsOpen s)
    (v : PhysicalPFReference.Reference (Fin N × Fin 3) (fun _ => 0))
    (hv : WeylCoreReference.CompactlySupportedIn s v) :
    ∃ a : ℕ → SmoothCore s,
      Filter.Tendsto (fun n => gaugedReference F χ hUV e O W B (a n)) Filter.atTop (𝓝 v) :=
  D.approximate (Fin N × Fin 3) (weightedLabel F χ e O) (weightedLabel_contDiff F χ hUV e O)
    (weightedEnergyLabel F χ hUV e O) (weightedEnergyLabel_continuous F χ hUV e O)
    (weightedEnergyLabel_relation F χ hUV e O) s hs v hv

end PfHk.CenteredRadialGauge
