import PfHk.SphereCoreGradientGraph
import PfHk.CompactL2Parameter

/-! Construction of the actual sphere core from continuous radiation
graph representatives. The curve constructor derives all strong L2
derivatives from fiber derivatives and closed ordinary-gradient calculus. -/

noncomputable section
namespace PfHk.SphereCoreGeometry

open MeasureTheory GptLean GptLean.PhysicalFock PfHk.PolarCalculus
open PfHk.SphereAngularField (Sphere SpherePhoton SphereRadiation)
open scoped ENNReal InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 350000
local instance sphereConstructionPhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _
attribute [local irreducible] radiationGraphInclusion spatialRadiationInclusion

variable {N : ℕ}

def CoreVector.ofContinuousGraph (q : Sphere N → RadiationGraphSpace) (hq : Continuous q)
    (hc : SphereC1 (fun θ => radiationGraphInclusion (q θ)))
    (hg : ∀ j, Continuous (sphereGradient (fun θ => radiationGraphInclusion (q θ)) j)) :
    CoreVector N where
  radiation := (hq.memLp_of_hasCompactSupport (μ := sphereMeasure (Fin N × Fin 3))
    (HasCompactSupport.of_compactSpace q)).toLp q
  gradient j := ((hg j).memLp_of_hasCompactSupport (μ := sphereMeasure (Fin N × Fin 3))
    (HasCompactSupport.of_compactSpace _)).toLp (sphereGradient (fun θ => radiationGraphInclusion (q θ)) j)
  representative θ := radiationGraphInclusion (q θ)
  regularity := hc
  value_ae := ((hq.memLp_of_hasCompactSupport (μ := sphereMeasure (Fin N × Fin 3))
    (HasCompactSupport.of_compactSpace q)).coeFn_toLp).mono fun _ h => congrArg radiationGraphInclusion h
  gradient_ae j := ((hg j).memLp_of_hasCompactSupport (μ := sphereMeasure (Fin N × Fin 3))
    (HasCompactSupport.of_compactSpace _)).coeFn_toLp

def familyCore (Q : ℝ × Sphere N → RadiationGraphSpace) (hQ : Continuous Q)
    (hc : ∀ t, SphereC1 (fun θ => radiationGraphInclusion (Q (t, θ))))
    (hg : ∀ j, Continuous (fun p : ℝ × Sphere N =>
      sphereGradient (fun θ => radiationGraphInclusion (Q (p.1, θ))) j p.2)) (t : ℝ) : CoreVector N :=
  CoreVector.ofContinuousGraph (fun θ => Q (t, θ))
    (hQ.comp (continuous_const.prodMk continuous_id)) (hc t)
    (fun j => (hg j).comp (continuous_const.prodMk continuous_id))

theorem familyCore_radiation (Q : ℝ × Sphere N → RadiationGraphSpace) (hQ : Continuous Q)
    (hc : ∀ t, SphereC1 (fun θ => radiationGraphInclusion (Q (t, θ))))
    (hg : ∀ j, Continuous (fun p : ℝ × Sphere N =>
      sphereGradient (fun θ => radiationGraphInclusion (Q (p.1, θ))) j p.2)) (t : ℝ) :
    (familyCore Q hQ hc hg t).radiation =
      CompactL2Parameter.sectionLp (μ := sphereMeasure (Fin N × Fin 3)) Q hQ t := rfl

theorem familyCore_radiation_ae (Q : ℝ × Sphere N → RadiationGraphSpace) (hQ : Continuous Q)
    (hc : ∀ t, SphereC1 (fun θ => radiationGraphInclusion (Q (t, θ))))
    (hg : ∀ j, Continuous (fun p : ℝ × Sphere N =>
      sphereGradient (fun θ => radiationGraphInclusion (Q (p.1, θ))) j p.2)) (t : ℝ) :
    (familyCore Q hQ hc hg t).radiation =ᵐ[sphereMeasure (Fin N × Fin 3)] fun θ => Q (t, θ) :=
  (CompactL2Parameter.section_memLp hQ t).coeFn_toLp

theorem familyCore_gradient (Q : ℝ × Sphere N → RadiationGraphSpace) (hQ : Continuous Q)
    (hc : ∀ t, SphereC1 (fun θ => radiationGraphInclusion (Q (t, θ))))
    (hg : ∀ j, Continuous (fun p : ℝ × Sphere N =>
      sphereGradient (fun θ => radiationGraphInclusion (Q (p.1, θ))) j p.2)) (j : Fin N × Fin 3) (t : ℝ) :
    (familyCore Q hQ hc hg t).gradient j =
      CompactL2Parameter.sectionLp (μ := sphereMeasure (Fin N × Fin 3))
        (fun p : ℝ × Sphere N => sphereGradient (fun θ => radiationGraphInclusion (Q (p.1, θ))) j p.2)
        (hg j) t := rfl

theorem familyCore_ambient (Q : ℝ × Sphere N → RadiationGraphSpace) (hQ : Continuous Q)
    (hc : ∀ t, SphereC1 (fun θ => radiationGraphInclusion (Q (t, θ))))
    (hg : ∀ j, Continuous (fun p : ℝ × Sphere N =>
      sphereGradient (fun θ => radiationGraphInclusion (Q (p.1, θ))) j p.2)) (t : ℝ) :
    (familyCore Q hQ hc hg t).ambient =
      CompactL2Parameter.sectionLp (μ := sphereMeasure (Fin N × Fin 3))
        (fun p => radiationGraphInclusion (Q p)) (radiationGraphInclusion.continuous.comp hQ) t := by
  apply Lp.ext
  exact (familyCore Q hQ hc hg t).ambient_ae.trans
    (CompactL2Parameter.section_memLp (radiationGraphInclusion.continuous.comp hQ) t).coeFn_toLp.symm

/-- Construction from ordinary graph-valued representative calculus.
No angular or radiation form-product identity is a premise. -/
def CoreCurve.ofContinuousGraphFamily
    (P : StandardSphereGradient (Fin N × Fin 3) PhotonFock)
    (Q D : ℝ × Sphere N → RadiationGraphSpace) (S : ℝ × Sphere N → PhotonFock)
    (hQ : Continuous Q) (hD : Continuous D) (hS : Continuous S)
    (hq : ∀ θ t, HasDerivAt (fun s => Q (s, θ)) (D (t, θ)) t)
    (hd : ∀ θ t, HasDerivAt (fun s => radiationGraphInclusion (D (s, θ))) (S (t, θ)) t)
    (hQc : ∀ t, SphereC1 (fun θ => radiationGraphInclusion (Q (t, θ))))
    (hDc : ∀ t, SphereC1 (fun θ => radiationGraphInclusion (D (t, θ))))
    (hQg : ∀ j, Continuous (fun p : ℝ × Sphere N =>
      sphereGradient (fun θ => radiationGraphInclusion (Q (p.1, θ))) j p.2))
    (hDg : ∀ j, Continuous (fun p : ℝ × Sphere N =>
      sphereGradient (fun θ => radiationGraphInclusion (D (p.1, θ))) j p.2)) : CoreCurve N where
  value := familyCore Q hQ hQc hQg
  first := familyCore D hD hDc hDg
  second := CompactL2Parameter.sectionLp S hS
  radiation_hasDerivAt t := by
    simp only [familyCore_radiation]
    exact CompactL2Parameter.sectionLp_hasDerivAt hQ hD hq t
  gradient_hasDerivAt j t := by
    apply PfHk.SphereCoreGeometry.gradient_hasDerivAt P
      (familyCore Q hQ hQc hQg) (familyCore D hD hDc hDg)
    · intro s
      simp only [familyCore_ambient]
      apply CompactL2Parameter.sectionLp_hasDerivAt
        (radiationGraphInclusion.continuous.comp hQ) (radiationGraphInclusion.continuous.comp hD)
      intro θ v
      exact (radiationGraphInclusion.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt v (hq θ v)
    · simp only [familyCore_ambient]
      exact CompactL2Parameter.sectionLp_continuous (radiationGraphInclusion.continuous.comp hD)
    · apply continuous_pi
      intro i
      simp only [familyCore_gradient]
      exact CompactL2Parameter.sectionLp_continuous (hDg i)
  first_hasDerivAt t := by
    simp only [familyCore_ambient]
    exact CompactL2Parameter.sectionLp_hasDerivAt (radiationGraphInclusion.continuous.comp hD) hS hd t

end PfHk.SphereCoreGeometry
