import PfHk.PhysicalCylinderSource

/-! Continuity of the actual logarithmic physical core curve, its second
derivative, and the angular and radiation source representatives. -/

noncomputable section
namespace PfHk.PhysicalCylinderSource

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.SymmetricLift GptLean.Representability PfHk.PhysicalFieldRegularity
  PfHk.PhysicalOperatorDomain PfHk.WeylGraphC1Calculus PfHk.PolarCalculus
  PfHk.SphereCoreGeometry PfHk.CenteredRadialGauge
open PfHk.SphereAngularField (SpherePhoton)

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 20000

local instance cylinderContinuityPhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _

attribute [local irreducible] CoreCurve.ambient CoreCurve.firstAmbient
  source radiation angularCandidate

private theorem ambient_continuous {N : ℕ} (u : CoreCurve N) : Continuous u.ambient :=
  continuous_iff_continuousAt.mpr fun t => (u.ambient_hasDerivAt t).continuousAt

private theorem first_continuous {N : ℕ} (u : CoreCurve N) : Continuous u.firstAmbient := by
  unfold CoreCurve.firstAmbient
  exact continuous_iff_continuousAt.mpr fun t => (u.first_hasDerivAt t).continuousAt

private theorem continuous_three_smul {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {a b c : ℝ → ℝ} {u v w z : ℝ → H}
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c)
    (hu : Continuous u) (hv : Continuous v) (hw : Continuous w)
    (heq : ∀ t, z t = a t • u t + b t • v t + c t • w t) : Continuous z := by
  have h : Continuous (fun t => a t • u t + b t • v t + c t • w t) :=
    ((ha.smul hu).add (hb.smul hv)).add (hc.smul hw)
  exact h.congr fun t => (heq t).symm

private theorem continuous_candidate {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {u dd q f z : ℝ → H} {r : ℝ → ℝ} (c : ℝ)
    (hu : Continuous u) (hdd : Continuous dd) (hq : Continuous q) (hf : Continuous f)
    (hr : Continuous r) (heq : ∀ t, z t = f t + dd t - c^2 • u t - r t • q t) :
    Continuous z := by
  have h : Continuous (fun t => f t + dd t - c^2 • u t - r t • q t) :=
    (((hf.add hdd).sub (continuous_const.smul hu)).sub (hr.smul hq))
  exact h.congr fun t => (heq t).symm

private theorem conformal_second_continuous {N : ℕ} (u : CoreCurve N)
    (hu : Continuous u.second) (c : ℝ) : Continuous (u.conformal c).second := by
  have ha : Continuous (fun t : ℝ => Real.exp (-c*t)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hb : Continuous (fun t : ℝ => 2*(-c*Real.exp (-c*t))) :=
    continuous_const.mul (continuous_const.mul ha)
  have hd : Continuous (fun t : ℝ => c^2*Real.exp (-c*t)) := continuous_const.mul ha
  exact continuous_three_smul ha hb hd hu (first_continuous u) (ambient_continuous u)
    (u.conformal_second c)

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (O : Configuration N) (C : CanonicalSectorCCR photonMeasure)
  (W : ConcreteWeylLaw photonMeasure) (B : StandardWeylGraphC1 W)
  (P : StandardPolarCalculus (Fin N × Fin 3) PhotonFock)
  (G : StandardSphereGradient (Fin N × Fin 3) PhotonFock)
  {s : Set (Configuration N)} (a : SmoothCore s)

theorem curve_ambient_continuous (c : ℝ) :
    Continuous (curve F χ hUV e O C W B P G a c).ambient :=
  ambient_continuous _

theorem curve_first_continuous (c : ℝ) :
    Continuous (curve F χ hUV e O C W B P G a c).firstAmbient :=
  first_continuous _

theorem rawCore_second_continuous :
    Continuous (rawCore F χ hUV e O C W B a P G).second :=
  CompactL2Parameter.sectionLp_continuous
    (logarithmicSecondValue_continuous F χ hUV e O C W B a)

theorem curve_second_continuous (c : ℝ) :
    Continuous (curve F χ hUV e O C W B P G a c).second :=
  conformal_second_continuous _ (rawCore_second_continuous F χ hUV e O C W B P G a) c

theorem radiation_continuous (c : ℝ) : Continuous (radiation F χ e O W a c) := by
  have ha : Continuous (fun t : ℝ => Real.exp (-c*t)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  unfold radiation
  exact ha.smul (rawRadiation_continuous F χ e O W a)

theorem angularCandidate_continuous {f : PhysicalPFReference.WaveSpace (Fin N × Fin 3)}
    (g : CompactSource s f) (c : ℝ) :
    Continuous (angularCandidate F χ hUV e O C W B P G a g c) := by
  have hr : Continuous (fun t : ℝ => Real.exp (-t)^2) :=
    (Real.continuous_exp.comp continuous_neg).pow 2
  exact continuous_candidate c (curve_ambient_continuous F χ hUV e O C W B P G a c)
    (curve_second_continuous F χ hUV e O C W B P G a c)
    (radiation_continuous F χ e O W a c) (source_continuous F χ e O W g c) hr
    (fun _ => by unfold angularCandidate; rfl)

end PfHk.PhysicalCylinderSource
