import PfHk.SphereCoreForms

/-! Continuity of the actual angular and radiation pairings against a
fixed sphere test, derived from the proved moving field derivatives. -/

noncomputable section
namespace PfHk.SphereCoreGeometry

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.SymmetricLift GptLean.Representability PfHk.PhysicalFieldRegularity
  PfHk.PolarCalculus
open PfHk.SphereAngularField (Sphere SpherePhoton SphereRadiation)
open scoped InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000
local instance corePairPhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _
local instance corePairAnalysisRealInner : InnerProductSpace ℝ (lp (fun _ : ℕ => PhotonFock) 2) :=
  InnerProductSpace.rclikeToReal ℂ _
attribute [local irreducible] CenteredSphereAngularField.angularVector
  CenteredSphereRadiationEnergy.analysis

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (O : Configuration N) (C : CanonicalSectorCCR photonMeasure)

theorem CoreCurve.angularVector_continuous (u : CoreCurve N) (j : Fin N × Fin 3) :
    Continuous (fun t => CenteredSphereAngularField.angularVector F χ hUV e O C
      (u.value t).gradient (u.value t).radiation j t) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hd := (u.gradient_hasDerivAt j t).add
    ((CenteredSphereAngularField.field_moving_hasDerivAt F χ hUV e O C j
      (u.radiation_hasDerivAt t)).const_smul Complex.I)
  convert! hd.continuousAt using 1
  funext s
  unfold CenteredSphereAngularField.angularVector
  rfl

theorem angularPair_continuous (v : CoreVector N) (u : CoreCurve N) :
    Continuous (fun t => angularPair F χ hUV e O C t v (u.value t)) := by
  apply continuous_finsetSum
  intro j _
  have hv : Continuous (fun t => CenteredSphereAngularField.angularVector
      F χ hUV e O C v.gradient v.radiation j t) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hd := ((CenteredSphereAngularField.field_hasDerivAt F χ hUV e O C j t v.radiation).const_smul
      Complex.I).const_add (v.gradient j)
    convert! hd.continuousAt using 1
    funext s
    unfold CenteredSphereAngularField.angularVector
    rfl
  exact hv.inner (u.angularVector_continuous F χ hUV e O C j)

theorem CoreCurve.analysis_continuous (u : CoreCurve N) :
    Continuous (fun t => CenteredSphereRadiationEnergy.analysis F χ hUV e O t (u.value t).radiation) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (CenteredSphereRadiationEnergy.analysis_moving_hasDerivAt F χ hUV e O
    (u.radiation_hasDerivAt t)).continuousAt

theorem radiationPair_continuous (v : CoreVector N) (u : CoreCurve N) :
    Continuous (fun t => radiationPair F χ hUV e O t v (u.value t)) := by
  have hv : Continuous (fun t => CenteredSphereRadiationEnergy.analysis F χ hUV e O t v.radiation) :=
    continuous_iff_continuousAt.mpr fun t =>
      (CenteredSphereRadiationEnergy.analysis_hasDerivAt F χ hUV e O t v.radiation).continuousAt
  have he : (fun t => radiationPair F χ hUV e O t v (u.value t)) =
      fun t => 2 * inner ℝ (CenteredSphereRadiationEnergy.analysis F χ hUV e O t v.radiation)
        (CenteredSphereRadiationEnergy.analysis F χ hUV e O t (u.value t).radiation) :=
    funext fun t => (CenteredSphereRadiationEnergy.analysis_pair_eq_integral
      F χ hUV e O t v.radiation (u.value t).radiation).symm
  rw [he]
  exact continuous_const.mul (hv.inner (u.analysis_continuous F χ hUV e O))

end PfHk.SphereCoreGeometry
