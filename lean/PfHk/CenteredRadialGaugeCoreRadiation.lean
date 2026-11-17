import PfHk.CenteredRadialGaugeRawCore
import PfHk.CenteredRadialGaugeRadiationOperator
import PfHk.SphereCoreForms

/-! Actual radiation-operator representatives on the constructed sphere
core. The full radiation graph is taken before the gauge change. Its
unitary image represents the already constructed displaced form. -/

noncomputable section
namespace PfHk.CenteredRadialGauge

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.PhysicalNonattainmentFluxKernel GptLean.SymmetricLift
  GptLean.Representability GptLean.PhysicalWeyl PfHk.PhysicalFieldRegularity
  PfHk.PhysicalOperatorDomain PfHk.WeylGraphC1Calculus PfHk.PolarCalculus
  PfHk.SphereCoreGeometry
open PfHk.SphereAngularField (Sphere SpherePhoton SphereRadiation)
open scoped ENNReal InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 300000
local instance coreRadiationPhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _
attribute [local irreducible] radiationGraphInclusion fullRadiationInclusion fullRadiationOutput
  graphLift unitary label

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (O : Configuration N) (W : ConcreteWeylLaw photonMeasure)
  {s : Set (Configuration N)} (a : SmoothCore s)

def rawRadiationValue (p : ℝ × Sphere N) : PhotonFock :=
  (2 : ℝ) • unitary F χ e O W (logarithmicPoint p)
    (fullRadiationOutput (a.representative (logarithmicPoint p)))

theorem rawRadiationValue_continuous : Continuous (rawRadiationValue F χ e O W a) := by
  have hx := logarithmicPoint_continuous (N := N)
  have hf := ((component false).continuous.comp ((label_continuous F χ e O).comp hx)).const_smul Complex.I
  have hq := fullRadiationOutput.continuous.comp (a.smooth.continuous.comp hx)
  have h := (W.continuous.comp (hf.prodMk hq)).const_smul (2 : ℝ)
  convert! h using 1
  funext p
  unfold rawRadiationValue unitary
  rfl

def rawRadiation (t : ℝ) : SpherePhoton N :=
  CompactL2Parameter.sectionLp (rawRadiationValue F χ e O W a)
    (rawRadiationValue_continuous F χ e O W a) t

theorem rawRadiation_continuous : Continuous (rawRadiation F χ e O W a) :=
  CompactL2Parameter.sectionLp_continuous (rawRadiationValue_continuous F χ e O W a)

theorem rawRadiation_ae (t : ℝ) : rawRadiation F χ e O W a t =ᵐ[sphereMeasure (Fin N × Fin 3)]
    fun θ => rawRadiationValue F χ e O W a (t, θ) :=
  (CompactL2Parameter.section_memLp (rawRadiationValue_continuous F χ e O W a) t).coeFn_toLp

theorem rawCore_radiationRepresentative (C : CanonicalSectorCCR photonMeasure)
    (B : StandardWeylGraphC1 W) (P : StandardPolarCalculus (Fin N × Fin 3) PhotonFock)
    (G : StandardSphereGradient (Fin N × Fin 3) PhotonFock) (t : ℝ) :
    IsRadiationRepresentative F χ hUV e O t ((rawCore F χ hUV e O C W B a P G).value t)
      (rawRadiation F χ e O W a t) := by
  intro v
  have hv : v.ambient =ᵐ[sphereMeasure (Fin N × Fin 3)]
      fun θ => radiationGraphInclusion (v.radiation θ) := radiationGraphInclusion.coeFn_compLpL v.radiation
  have hi := l2_inner_eq_integral v.ambient (rawRadiation F χ e O W a t) hv
    (rawRadiation_ae F χ e O W a t)
  apply hi.trans
  unfold radiationPair
  apply integral_congr_ae
  filter_upwards [rawCore_radiation_ae F χ hUV e O C W B a P G t] with θ hq
  rw [hq]
  have hg : (radiationGraphInclusion (a.rootWave (logarithmicPoint (t, θ))),
      fullRadiationOutput (a.representative (logarithmicPoint (t, θ)))) ∈ radiationHamiltonian.graph := by
    convert! a.radiation_graph (logarithmicPoint (t, θ)) using 1
    unfold SmoothCore.rootWave fullRadiationInclusion
    rfl
  exact radiation_operator_pair F χ hUV e O W (logarithmicPoint (t, θ))
    (v.radiation θ) (a.rootWave (logarithmicPoint (t, θ)))
    (fullRadiationOutput (a.representative (logarithmicPoint (t, θ)))) hg

end PfHk.CenteredRadialGauge
