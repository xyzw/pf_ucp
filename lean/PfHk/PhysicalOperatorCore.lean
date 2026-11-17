import PfHk.C1ReferenceCore
import GptLean.WeylRadiationOperator

/-! A concrete electronic smooth core valued in the actual radiation
operator graph. Smoothness is in the graph norm, so electronic derivatives
retain the radiation operator domain. Only the original vectors have a
finite photon-number cutoff. No differentiability of a radial gauge is
part of this definition. -/

noncomputable section
namespace PfHk.PhysicalOperatorDomain

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalWeyl
  GptLean.PhysicalPFReference GptLean.Representability
open scoped Topology

set_option backward.isDefEq.respectTransparency.types true
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option Elab.async false

private theorem graph_contDiff_comp {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G]
    [IsScalarTower ℝ ℂ G]
    (T : F →L[ℂ] G) (f : E → F) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => T (f x)) :=
  (T.restrictScalars ℝ).contDiff.comp hf

attribute [local irreducible] PhysicalPFReference.inclusion PhysicalPFReference.ordinary
  PhysicalPFReference.radiation PhysicalPFReference.potential

/-- The full radiation graph, retaining its square-root graph coordinate. -/
def fullRadiationSubmodule : Submodule ℂ (RadiationGraphSpace × PhotonFock) :=
  radiationHamiltonian.graph.comap
    (radiationGraphInclusion.toLinearMap.prodMap (LinearMap.id : PhotonFock →ₗ[ℂ] PhotonFock))

abbrev FullRadiationGraph := ↥fullRadiationSubmodule

instance fullRadiationComplexNormedSpace : NormedSpace ℂ FullRadiationGraph :=
  fullRadiationSubmodule.normedSpace

instance fullRadiationRealNormedSpace : NormedSpace ℝ FullRadiationGraph :=
  NormedSpace.restrictScalars ℝ ℂ FullRadiationGraph

def fullRootProjection : FullRadiationGraph →L[ℂ] RadiationGraphSpace :=
  (ContinuousLinearMap.fst ℂ RadiationGraphSpace PhotonFock).comp fullRadiationSubmodule.subtypeL

def fullRadiationOutput : FullRadiationGraph →L[ℂ] PhotonFock :=
  (ContinuousLinearMap.snd ℂ RadiationGraphSpace PhotonFock).comp fullRadiationSubmodule.subtypeL

def fullRadiationInclusion : FullRadiationGraph →L[ℂ] PhotonFock :=
  radiationGraphInclusion.comp fullRootProjection

theorem fullRadiation_graph (q : FullRadiationGraph) :
    (fullRadiationInclusion q, fullRadiationOutput q) ∈ radiationHamiltonian.graph :=
  q.property

attribute [local irreducible] radiationGraphInclusion radiationGraphDerivative
  fullRootProjection fullRadiationOutput fullRadiationInclusion fullRadiationSubmodule ContDiff

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Ordinary compact electronic smoothness in the full radiation graph,
with a uniform finite photon-number cutoff before any gauge change. -/
structure SmoothCore (s : Set (Position I)) where
  representative : Position I → FullRadiationGraph
  smooth : ContDiff ℝ (⊤ : ℕ∞) representative
  compact : HasCompactSupport representative
  support : tsupport representative ⊆ s
  photonCutoff : ℕ
  photonFinite : ∀ x, FiniteNumberSupport photonMeasure photonCutoff
    (fullRadiationInclusion (representative x))

namespace SmoothCore

variable {s : Set (Position I)} (a : SmoothCore s)

def rootWave (x : Position I) : RadiationGraphSpace := fullRootProjection (a.representative x)

theorem rootWave_smooth : ContDiff ℝ (⊤ : ℕ∞) a.rootWave := by
  exact graph_contDiff_comp fullRootProjection a.representative a.smooth

theorem rootWave_compact : HasCompactSupport a.rootWave :=
  a.compact.comp_left (map_zero fullRootProjection)

theorem rootWave_memLp : MemLp a.rootWave 2 volume :=
  a.rootWave_smooth.continuous.memLp_of_hasCompactSupport a.rootWave_compact

theorem value_smooth : ContDiff ℝ (1 : ℕ∞) (C1ReferenceCore.valueFunction a.rootWave) := by
  unfold C1ReferenceCore.valueFunction
  exact ((radiationGraphInclusion.restrictScalars ℝ).contDiff.comp
    a.rootWave_smooth).of_le (by simp)

theorem value_compact : HasCompactSupport (C1ReferenceCore.valueFunction a.rootWave) :=
  a.rootWave_compact.comp_left (map_zero radiationGraphInclusion)

def reference : Reference I (fun _ => 0) :=
  C1ReferenceCore.reference a.rootWave a.rootWave_memLp a.value_smooth a.value_compact

attribute [local irreducible] reference

theorem reference_value_ae :
    inclusion I (fun _ => 0) a.reference =ᵐ[volume]
      fun x => fullRadiationInclusion (a.representative x) := by
  have he := C1ReferenceCore.reference_value a.rootWave a.rootWave_memLp
    a.value_smooth a.value_compact
  have ha := (C1ReferenceCore.value_memLp a.rootWave a.rootWave_memLp).coeFn_toLp
  have h := (Filter.EventuallyEq.of_eq
    (congrArg (fun z : WaveSpace I => ⇑z) he)).trans ha
  unfold reference
  apply h.trans
  apply Filter.EventuallyEq.of_eq
  funext x
  unfold C1ReferenceCore.valueFunction rootWave fullRadiationInclusion
  rfl

theorem reference_ordinary_ae (i : I) :
    ordinary I (fun _ => 0) i a.reference =ᵐ[volume]
      fun x => fderiv ℝ (fun y => fullRadiationInclusion (a.representative y)) x
        (EuclideanSpace.single i 1) := by
  have he := C1ReferenceCore.reference_ordinary a.rootWave a.rootWave_memLp
    a.value_smooth a.value_compact i
  have ha := (C1ReferenceCore.derivative_memLp a.rootWave a.value_smooth a.value_compact i).coeFn_toLp
  have h := (Filter.EventuallyEq.of_eq
    (congrArg (fun z : WaveSpace I => ⇑z) he)).trans ha
  unfold reference
  apply h.trans
  apply Filter.EventuallyEq.of_eq
  funext x
  unfold C1ReferenceCore.derivativeFunction C1ReferenceCore.valueFunction rootWave fullRadiationInclusion
  rfl

theorem supported : ∀ᵐ x ∂volume, x ∉ s → inclusion I (fun _ => 0) a.reference x = 0 := by
  filter_upwards [a.reference_value_ae] with x hx
  intro hxs
  have hz : a.representative x = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => hxs (a.support h))
  exact hx.trans ((congrArg (fun q : FullRadiationGraph => fullRadiationInclusion q) hz).trans
    (map_zero fullRadiationInclusion))

theorem radiation_graph (x : Position I) :
    (fullRadiationInclusion (a.representative x), fullRadiationOutput (a.representative x)) ∈
      radiationHamiltonian.graph := fullRadiation_graph _

/-- Every electronic graph derivative is still in the actual radiation
operator graph. The graph has not been replaced by a numerical bound. -/
theorem derivative_radiation_graph (x v : Position I) :
    (fullRadiationInclusion (fderiv ℝ a.representative x v),
      fullRadiationOutput (fderiv ℝ a.representative x v)) ∈ radiationHamiltonian.graph :=
  fullRadiation_graph _

end SmoothCore

end PfHk.PhysicalOperatorDomain
