import PfHk.CenteredRadialGaugePolarInner
import GptLean.WeylRadiationOperator

/-! The actual displaced radiation form is represented by twice the
unitary conjugate of the original radiation Hamiltonian. This is derived
from the existing radiation graph and the proved bilinear Weyl identity. -/

noncomputable section
namespace PfHk.CenteredRadialGauge

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.PhysicalNonattainmentFluxKernel GptLean.SymmetricLift
  GptLean.Representability GptLean.PhysicalWeyl PfHk.PhysicalFieldRegularity
open scoped InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 250000
local instance radiationOperatorPhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _
local instance radiationOperatorAnalysisRealInner : InnerProductSpace ℝ (lp (fun _ : ℕ => PhotonFock) 2) :=
  InnerProductSpace.rclikeToReal ℂ _
attribute [local irreducible] radiationGraphInclusion radiationGraphDerivative
  graphLift inverseRadiationGraph unitary RadialGaugeRadiation.displacedAnalysis

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (O : Configuration N) (W : ConcreteWeylLaw photonMeasure)

theorem graphLift_inverse (X : Configuration N) (q : RadiationGraphSpace) :
    graphLift F χ hUV e O W X (inverseRadiationGraph F χ hUV e O W X q) = q := by
  apply radiationGraphInclusion_injective_weyl
  rw [graphLift_inclusion, inverseRadiationGraph_inclusion, LinearIsometryEquiv.apply_symm_apply]

theorem radiation_operator_pair (X : Configuration N) (q p : RadiationGraphSpace)
    (v : PhotonFock) (hv : (radiationGraphInclusion p, v) ∈ radiationHamiltonian.graph) :
    inner ℝ (radiationGraphInclusion q) ((2 : ℝ) • unitary F χ e O W X v) =
      2 * inner ℝ
        (RadialGaugeRadiation.displacedAnalysis (inverseSqrtLabel F χ hUV e O X) q)
        (RadialGaugeRadiation.displacedAnalysis (inverseSqrtLabel F χ hUV e O X)
          (graphLift F χ hUV e O W X p)) := by
  let q₀ := inverseRadiationGraph F χ hUV e O W X q
  have hform := (radiationHamiltonian_graph p v).mp hv q₀
  have hreal : inner ℝ (radiationGraphDerivative q₀) (radiationGraphDerivative p) =
      inner ℝ (radiationGraphInclusion q₀) v := by
    rw [PolarCalculus.real_inner_eq_complex_re, PolarCalculus.real_inner_eq_complex_re]
    exact congrArg Complex.re hform
  have hweyl := radiationPair_graphLift F χ hUV e O W X q₀ p
  rw [show graphLift F χ hUV e O W X q₀ = q from graphLift_inverse F χ hUV e O W X q] at hweyl
  have hi := PolarCalculus.complexIsometry_real_inner (unitary F χ e O W X)
    (radiationGraphInclusion q₀) v
  have hq₀ : radiationGraphInclusion q₀ =
      (unitary F χ e O W X).symm (radiationGraphInclusion q) :=
    inverseRadiationGraph_inclusion F χ hUV e O W X q
  have hin : unitary F χ e O W X (radiationGraphInclusion q₀) = radiationGraphInclusion q :=
    (congrArg (fun z : PhotonFock => unitary F χ e O W X z) hq₀).trans
      ((unitary F χ e O W X).apply_symm_apply (radiationGraphInclusion q))
  have hinner : inner ℝ (radiationGraphInclusion q) (unitary F χ e O W X v) =
      inner ℝ (radiationGraphInclusion q₀) v :=
    (congrArg (fun z : PhotonFock => inner ℝ z (unitary F χ e O W X v)) hin).symm.trans hi
  calc
    _ = 2 * inner ℝ (radiationGraphInclusion q) (unitary F χ e O W X v) :=
      real_inner_smul_right _ _ _
    _ = 2 * inner ℝ (radiationGraphInclusion q₀) v := congrArg (fun z : ℝ => 2*z) hinner
    _ = 2 * inner ℝ (radiationGraphDerivative q₀) (radiationGraphDerivative p) :=
      congrArg (fun z : ℝ => 2*z) hreal.symm
    _ = _ := hweyl.symm

end PfHk.CenteredRadialGauge
