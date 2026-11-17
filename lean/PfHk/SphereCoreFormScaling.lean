import PfHk.SphereCoreAlgebra
import PfHk.SphereCoreForms

/-! Scalar weights commute with the genuine angular and radiation form
representatives. The claim follows from their actual linear fields. -/

noncomputable section
namespace PfHk.SphereCoreGeometry

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.SymmetricLift GptLean.Representability PfHk.PhysicalFieldRegularity
  PfHk.PolarCalculus
open PfHk.SphereAngularField (SpherePhoton)
open scoped ENNReal InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 100000
local instance coreFormScalingPhotonRealInner : InnerProductSpace ℝ PhotonFock := InnerProductSpace.rclikeToReal ℂ _
local instance coreFormScalingAnalysisRealInner : InnerProductSpace ℝ CenteredSphereRadiationEnergy.AnalysisSpace :=
  InnerProductSpace.rclikeToReal ℂ _
attribute [local irreducible] CenteredSphereAngularField.field
  CenteredSphereRadiationEnergy.analysis

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (O : Configuration N) (C : CanonicalSectorCCR photonMeasure)

private theorem photon_inner_scale (a : ℝ) (u v : SpherePhoton N) :
    inner ℝ u (a • v) = a * inner ℝ u v := by
  convert! real_inner_smul_right u v a using 1

private theorem analysis_inner_scale (a : ℝ) (u v : CenteredSphereRadiationEnergy.SphereAnalysis N) :
    inner ℝ u (a • v) = a * inner ℝ u v := by
  convert! real_inner_smul_right u v a using 1

theorem angularVector_scale (a t : ℝ) (u : CoreVector N) (j : Fin N × Fin 3) :
    CenteredSphereAngularField.angularVector F χ hUV e O C
      (u.scale a).gradient (u.scale a).radiation j t =
      a • CenteredSphereAngularField.angularVector F χ hUV e O C
        u.gradient u.radiation j t := by
  unfold CenteredSphereAngularField.angularVector CoreVector.scale
  calc
    _ = a • u.gradient j + Complex.I • (a • CenteredSphereAngularField.field F χ hUV e O C j t u.radiation) :=
      congrArg (fun z : SpherePhoton N => a • u.gradient j + Complex.I • z)
        (LinearMapClass.map_smul_of_tower _ a u.radiation)
    _ = a • u.gradient j + a • (Complex.I • CenteredSphereAngularField.field F χ hUV e O C j t u.radiation) :=
      congrArg (fun z : SpherePhoton N => a • u.gradient j + z) (smul_comm Complex.I a _)
    _ = _ := (smul_add a _ _).symm

theorem angularPair_scale_right (a t : ℝ) (v u : CoreVector N) :
    angularPair F χ hUV e O C t v (u.scale a) = a * angularPair F χ hUV e O C t v u := by
  unfold angularPair
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact (congrArg (fun z : SpherePhoton N => inner ℝ
    (CenteredSphereAngularField.angularVector F χ hUV e O C v.gradient v.radiation j t) z)
    (angularVector_scale F χ hUV e O C a t u j)).trans (photon_inner_scale a _ _)

theorem radiationPair_eq_analysis (t : ℝ) (v u : CoreVector N) :
    radiationPair F χ hUV e O t v u = 2 * inner ℝ
      (CenteredSphereRadiationEnergy.analysis F χ hUV e O t v.radiation)
      (CenteredSphereRadiationEnergy.analysis F χ hUV e O t u.radiation) :=
  (CenteredSphereRadiationEnergy.analysis_pair_eq_integral F χ hUV e O t v.radiation u.radiation).symm

theorem radiationPair_scale_right (a t : ℝ) (v u : CoreVector N) :
    radiationPair F χ hUV e O t v (u.scale a) = a * radiationPair F χ hUV e O t v u := by
  let B := CenteredSphereRadiationEnergy.analysis F χ hUV e O t
  have he : B (u.scale a).radiation = a • B u.radiation :=
    (congrArg (fun q => B q) (CoreVector.scale_radiation a u)).trans
      (LinearMapClass.map_smul_of_tower B a u.radiation)
  calc
    _ = 2 * inner ℝ (B v.radiation) (B (u.scale a).radiation) := radiationPair_eq_analysis F χ hUV e O t v (u.scale a)
    _ = 2 * (a * inner ℝ (B v.radiation) (B u.radiation)) :=
      congrArg (fun x : ℝ => 2*x) ((congrArg (fun z => inner ℝ (B v.radiation) z) he).trans
        (analysis_inner_scale a _ _))
    _ = a * (2 * inner ℝ (B v.radiation) (B u.radiation)) := by ring
    _ = _ := congrArg (fun x : ℝ => a*x) (radiationPair_eq_analysis F χ hUV e O t v u).symm

theorem IsAngularRepresentative.scale {t : ℝ} {u : CoreVector N} {k : SpherePhoton N}
    (hk : IsAngularRepresentative F χ hUV e O C t u k) (a : ℝ) :
    IsAngularRepresentative F χ hUV e O C t (u.scale a) (a • k) := by
  intro v
  exact (photon_inner_scale a _ _).trans ((congrArg (fun x : ℝ => a*x) (hk v)).trans
    (angularPair_scale_right F χ hUV e O C a t v u).symm)

theorem IsRadiationRepresentative.scale {t : ℝ} {u : CoreVector N} {h : SpherePhoton N}
    (hh : IsRadiationRepresentative F χ hUV e O t u h) (a : ℝ) :
    IsRadiationRepresentative F χ hUV e O t (u.scale a) (a • h) := by
  intro v
  exact (photon_inner_scale a _ _).trans ((congrArg (fun x : ℝ => a*x) (hh v)).trans
    (radiationPair_scale_right F χ hUV e O a t v u).symm)

end PfHk.SphereCoreGeometry
