import PfHk.SphereCoreGeometry
import PfHk.CenteredSphereFormProductRules
import PfHk.CenteredSphereRadiationEnergy
import PfHk.CenteredSphereRadiationProduct

/-!
The genuine centered angular and radiation forms on the ordinary sphere
core. Operator representatives are defined by weak form pairing. The
moving angular product identity is then proved from strong graph and
gradient differentiation and the already proved physical field derivative.
-/

noncomputable section
namespace PfHk.SphereCoreGeometry

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.SymmetricLift GptLean.Representability PfHk.PhysicalFieldRegularity
  PfHk.PolarCalculus
open PfHk.SphereAngularField (Sphere SpherePhoton SphereRadiation)
open scoped ENNReal InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000

local instance : InnerProductSpace ℝ PhotonFock := InnerProductSpace.rclikeToReal ℂ _
local instance : InnerProductSpace ℝ (lp (fun _ : ℕ => PhotonFock) 2) :=
  InnerProductSpace.rclikeToReal ℂ _

attribute [local irreducible] radiationGraphInclusion radiationGraphDerivative
  RadialGaugeRadiation.displacedAnalysis CenteredSphereAngularField.angularVector

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (O : Configuration N) (C : CanonicalSectorCCR photonMeasure)

def angularPair (t : ℝ) (v u : CoreVector N) : ℝ :=
  ∑ j, inner ℝ
    (CenteredSphereAngularField.angularVector F χ hUV e O C v.gradient v.radiation j t)
    (CenteredSphereAngularField.angularVector F χ hUV e O C u.gradient u.radiation j t)

def radiationPair (t : ℝ) (v u : CoreVector N) : ℝ :=
  ∫ θ : Sphere N, 2 * inner ℝ
    (RadialGaugeRadiation.displacedAnalysis
      (CenteredSphereRadiationEnergy.label F χ hUV e O t θ) (v.radiation θ))
    (RadialGaugeRadiation.displacedAnalysis
      (CenteredSphereRadiationEnergy.label F χ hUV e O t θ) (u.radiation θ))
    ∂sphereMeasure (Fin N × Fin 3)

theorem angularPair_symm (t : ℝ) (v u : CoreVector N) :
    angularPair F χ hUV e O C t v u = angularPair F χ hUV e O C t u v := by
  unfold angularPair
  exact Finset.sum_congr rfl fun j _ => real_inner_comm _ _

theorem angularPair_self (t : ℝ) (u : CoreVector N) :
    angularPair F χ hUV e O C t u u =
      CenteredSphereAngularField.energy F χ hUV e O C u.gradient u.radiation t := by
  unfold angularPair CenteredSphereAngularField.energy
  simp only [real_inner_self_eq_norm_sq]

theorem radiationPair_symm (t : ℝ) (v u : CoreVector N) :
    radiationPair F χ hUV e O t v u = radiationPair F χ hUV e O t u v := by
  unfold radiationPair
  apply integral_congr_ae
  exact ae_of_all _ fun θ => congrArg (fun a : ℝ => 2 * a) (real_inner_comm _ _)

theorem radiationPair_self (t : ℝ) (u : CoreVector N) :
    radiationPair F χ hUV e O t u u =
      CenteredSphereRadiationEnergy.energy F χ hUV e O u.radiation t := by
  unfold radiationPair CenteredSphereRadiationEnergy.energy
    CenteredRadialGauge.radiationForm RadialGaugeRadiation.energy
  apply integral_congr_ae
  exact ae_of_all _ fun θ => by
    dsimp only
    rw [real_inner_self_eq_norm_sq]
    rfl

/-- The weak angular operator domain, using the genuine sphere gradient. -/
def IsAngularRepresentative (t : ℝ) (u : CoreVector N) (k : SpherePhoton N) : Prop :=
  ∀ v : CoreVector N, inner ℝ v.ambient k = angularPair F χ hUV e O C t v u

/-- The weak radiation operator domain, using the actual displaced
radiation analysis form. -/
def IsRadiationRepresentative (t : ℝ) (u : CoreVector N) (h : SpherePhoton N) : Prop :=
  ∀ v : CoreVector N, inner ℝ v.ambient h = radiationPair F χ hUV e O t v u

theorem IsAngularRepresentative.diagonal {t : ℝ} {u : CoreVector N} {k : SpherePhoton N}
    (hk : IsAngularRepresentative F χ hUV e O C t u k) :
    inner ℝ u.ambient k =
      CenteredSphereAngularField.energy F χ hUV e O C u.gradient u.radiation t :=
  (hk u).trans (angularPair_self F χ hUV e O C t u)

theorem IsRadiationRepresentative.diagonal {t : ℝ} {u : CoreVector N} {h : SpherePhoton N}
    (hh : IsRadiationRepresentative F χ hUV e O t u h) :
    inner ℝ u.ambient h =
      CenteredSphereRadiationEnergy.energy F χ hUV e O u.radiation t :=
  (hh u).trans (radiationPair_self F χ hUV e O t u)

/-- The angular quadratic-form product rule required in the cylinder
commutator, derived from actual moving L2 fields and weak representatives. -/
theorem angular_product_rule (u : CoreCurve N) (k : ℝ → SpherePhoton N)
    (hk : ∀ t, IsAngularRepresentative F χ hUV e O C t (u.value t) (k t)) (t : ℝ) :
    HasDerivAt (fun s => inner ℝ (u.ambient s) (k s))
      (2 * inner ℝ (u.firstAmbient t) (k t) +
        CenteredSphereAngularField.formDerivative F χ hUV e O C
          (u.value t).gradient (u.value t).radiation t) t := by
  have he : (fun s => inner ℝ (u.ambient s) (k s)) =
      fun s => CenteredSphereAngularField.energy F χ hUV e O C
        (u.value s).gradient (u.value s).radiation s :=
    funext fun s => (hk s).diagonal F χ hUV e O C
  rw [he]
  have hd := CenteredSphereAngularField.energy_moving_hasDerivAt F χ hUV e O C
    (u.radiation_hasDerivAt t) (fun j => u.gradient_hasDerivAt j t)
  have hc : (∑ j, inner ℝ
      (CenteredSphereAngularField.angularVector F χ hUV e O C
        (u.value t).gradient (u.value t).radiation j t)
      (CenteredSphereAngularField.angularVector F χ hUV e O C
        (u.first t).gradient (u.first t).radiation j t)) =
      inner ℝ (u.firstAmbient t) (k t) :=
    (angularPair_symm F χ hUV e O C t (u.value t) (u.first t)).trans
      (hk t (u.first t)).symm
  rw [hc] at hd
  exact hd

/-- The radiation quadratic-form product rule required in the cylinder
commutator, derived on the actual graph L2 curve. -/
theorem radiation_product_rule (u : CoreCurve N) (h : ℝ → SpherePhoton N)
    (hh : ∀ t, IsRadiationRepresentative F χ hUV e O t (u.value t) (h t)) (t : ℝ) :
    HasDerivAt (fun s => inner ℝ (u.ambient s) (h s))
      (2 * inner ℝ (u.firstAmbient t) (h t) +
        CenteredSphereRadiationEnergy.formDerivative F χ hUV e O (u.value t).radiation t) t := by
  have he : (fun s => inner ℝ (u.ambient s) (h s)) =
      fun s => CenteredSphereRadiationEnergy.energy F χ hUV e O (u.value s).radiation s :=
    funext fun s => (hh s).diagonal F χ hUV e O
  rw [he]
  have hd := CenteredSphereRadiationEnergy.energy_moving_hasDerivAt F χ hUV e O
    (u.radiation_hasDerivAt t)
  have hc : radiationPair F χ hUV e O t (u.value t) (u.first t) =
      inner ℝ (u.firstAmbient t) (h t) :=
    (radiationPair_symm F χ hUV e O t (u.value t) (u.first t)).trans
      (hh t (u.first t)).symm
  change HasDerivAt _ (2 * radiationPair F χ hUV e O t (u.value t) (u.first t) + _) t at hd
  rw [hc] at hd
  exact hd

end PfHk.SphereCoreGeometry
