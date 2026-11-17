import PfHk.CenteredRadialGaugeCoreRadiation
import PfHk.PhysicalOperatorCoreSource
import PfHk.SphereCoreConformal
import PfHk.SphereCoreFormScaling
import PfHk.CylinderConjugation

/-! The actual continuous transformed physical source, the conjugated
radiation representative, and the angular candidate recovered from the
radial equation. Its angular weak-form representation is a separate
proof obligation, not an assumption in these definitions. -/

noncomputable section
namespace PfHk.PhysicalCylinderSource

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.PhysicalNonattainmentFluxKernel GptLean.SymmetricLift
  GptLean.Representability PfHk.PhysicalFieldRegularity PfHk.PhysicalOperatorDomain
  PfHk.WeylGraphC1Calculus PfHk.PolarCalculus PfHk.SphereCoreGeometry
  PfHk.CenteredRadialGauge
open PfHk.SphereAngularField (Sphere SpherePhoton)
open scoped InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 250000
local instance cylinderSourcePhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _
attribute [local irreducible] CenteredRadialGauge.unitary label

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (O : Configuration N) (C : CanonicalSectorCCR photonMeasure)
  (W : ConcreteWeylLaw photonMeasure) (B : StandardWeylGraphC1 W)
  (P : StandardPolarCalculus (Fin N × Fin 3) PhotonFock)
  (G : StandardSphereGradient (Fin N × Fin 3) PhotonFock)
  {s : Set (Configuration N)} (a : SmoothCore s)
  {f : PhysicalPFReference.WaveSpace (Fin N × Fin 3)} (g : CompactSource s f)

def value (c : ℝ) (p : ℝ × Sphere N) : PhotonFock :=
  (2 * Real.exp (-(c + 2) * p.1)) • unitary F χ e O W (logarithmicPoint p)
    (g.representative (logarithmicPoint p))

theorem value_continuous (c : ℝ) : Continuous (value F χ e O W g c) := by
  have hx := logarithmicPoint_continuous (N := N)
  have hf := ((component false).continuous.comp ((label_continuous F χ e O).comp hx)).const_smul Complex.I
  have hg := g.continuous.comp hx
  have ha : Continuous (fun p : ℝ × Sphere N => 2 * Real.exp (-(c+2)*p.1)) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_fst))
  convert! ha.smul (W.continuous.comp (hf.prodMk hg)) using 1
  funext p
  unfold value CenteredRadialGauge.unitary
  rfl

def source (c t : ℝ) : SpherePhoton N :=
  CompactL2Parameter.sectionLp (value F χ e O W g c) (value_continuous F χ e O W g c) t

theorem source_continuous (c : ℝ) : Continuous (source F χ e O W g c) :=
  CompactL2Parameter.sectionLp_continuous (value_continuous F χ e O W g c)

theorem source_ae (c t : ℝ) : source F χ e O W g c t =ᵐ[sphereMeasure (Fin N × Fin 3)]
    fun θ => (2 * Real.exp (-(c+2)*t)) • unitary F χ e O W (Real.exp (-t) • θ.val)
      (g.representative (Real.exp (-t) • θ.val)) :=
  (CompactL2Parameter.section_memLp (value_continuous F χ e O W g c) t).coeFn_toLp

def curve (c : ℝ) : CoreCurve N := (rawCore F χ hUV e O C W B a P G).conformal c

def radiation (c t : ℝ) : SpherePhoton N :=
  Real.exp (-c*t) • rawRadiation F χ e O W a t

theorem radiation_representative (c t : ℝ) :
    IsRadiationRepresentative F χ hUV e O t ((curve F χ hUV e O C W B P G a c).value t)
      (radiation F χ e O W a c t) :=
  (rawCore_radiationRepresentative F χ hUV e O W a C B P G t).scale F χ hUV e O
    (Real.exp (-c*t))

def angularCandidate (c t : ℝ) : SpherePhoton N :=
  source F χ e O W g c t + (curve F χ hUV e O C W B P G a c).second t -
    c^2 • (curve F χ hUV e O C W B P G a c).ambient t -
      Real.exp (-t)^2 • radiation F χ e O W a c t

theorem operator_eq_source (c t : ℝ) :
    -(curve F χ hUV e O C W B P G a c).second t +
      angularCandidate F χ hUV e O C W B P G a g c t +
      c^2 • (curve F χ hUV e O C W B P G a c).ambient t +
      Real.exp (-t)^2 • radiation F χ e O W a c t = source F χ e O W g c t := by
  unfold angularCandidate
  abel

end PfHk.PhysicalCylinderSource
