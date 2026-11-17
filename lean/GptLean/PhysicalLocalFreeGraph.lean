import GptLean.PhysicalLocalSupport

/-!
The local free graph on the actual supported domain. Its inclusion takes
values directly in the physical wave space. Every supported finite-energy
cut vector has a graph representative with the exact free form norm.
No density of smooth functions on an arbitrary support set, common local
Hilbert type, or local spectrum is assumed.
-/

noncomputable section
namespace GptLean.PhysicalLocalFreeGraph

open MeasureTheory Filter Topology PhysicalFock PhotonLocalization
  PhysicalLocalSupport SymmetricLift
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 200000
set_option Elab.async false

variable (N : ℕ) (r : ℝ) (L M : ℕ)

def domainSubspace : Submodule ℂ (PhysicalFreeHilbert.Space (Fin N × Fin 3)) :=
  (localSupport N r L M).comap (PhysicalFreeHilbert.inclusion (Fin N × Fin 3)).toLinearMap

abbrev Domain := ↥(domainSubspace N r L M)

instance domainComplete : CompleteSpace (Domain N r L M) :=
  ((localSupport_closed N r L M).preimage
    (PhysicalFreeHilbert.inclusion (Fin N × Fin 3)).continuous).completeSpace_coe

abbrev Space := ↥(localSupport N r L M)

instance spaceComplete : CompleteSpace (Space N r L M) :=
  (localSupport_closed N r L M).completeSpace_coe

def supportValue : Domain N r L M →L[ℂ] PhysicalFreeForm.WaveSpace (Fin N × Fin 3) :=
  (PhysicalFreeHilbert.inclusion (Fin N × Fin 3)).comp (domainSubspace N r L M).subtypeL

def inclusion : Domain N r L M →L[ℂ] Space N r L M :=
  (supportValue N r L M).codRestrict (localSupport N r L M) (fun u => u.property)

def embedding : Space N r L M →ₗᵢ[ℂ] PhysicalFreeForm.WaveSpace (Fin N × Fin 3) :=
  (localSupport N r L M).subtypeₗᵢ

theorem value_mem_support (u : Space N r L M) :
    embedding N r L M u ∈ localSupport N r L M :=
  u.property

/-- The finite-sector coordinate map applies to every vector in this local closure. -/
def finiteInclusion : Space N r L M →ₗᵢ[ℂ]
    PhysicalFiniteSectorCoordinates.numberSubspace (Sector photonMeasure)
      (volume : Measure (Configuration N)) M where
  toFun u := ⟨embedding N r L M u,
    numberSupport_le_finite N M (value_mem_support N r L M u).2⟩
  map_add' u v := Subtype.ext ((embedding N r L M).map_add u v)
  map_smul' c u := Subtype.ext ((embedding N r L M).map_smul c u)
  norm_map' u := (embedding N r L M).norm_map u

theorem inclusion_norm_le (u : Domain N r L M) :
    ‖inclusion N r L M u‖ ≤ ‖u‖ :=
  PhysicalFreeHilbert.inclusion_norm_le (Fin N × Fin 3) u.val

theorem inclusion_injective : Function.Injective (inclusion N r L M) :=
  fun _ _ h => Subtype.ext (PhysicalFreeHilbert.inclusion_injective (Fin N × Fin 3)
    (congrArg Subtype.val h))

def vector (u : Domain N r L M) : SpatialFreeVector (I := Fin N × Fin 3) radiationRoot :=
  PhysicalFreeHilbert.vector (Fin N × Fin 3) u.val

theorem vector_value (u : Domain N r L M) :
    (vector N r L M u).value = supportValue N r L M u := rfl

theorem vector_form (u : Domain N r L M) :
    (vector N r L M u).form = ‖u‖ ^ 2 :=
  PhysicalFreeHilbert.vector_form (Fin N × Fin 3) u.val

def cutVector (u : SpatialFreeVector (I := Fin N × Fin 3) radiationRoot) :
    SpatialFreeVector (I := Fin N × Fin 3) radiationRoot :=
  (physicalElectronicFamily L).cutVector (cutoff (Sector photonMeasure) M)
    (cutoff_radiation_graph M) u

theorem cutVector_value (u : SpatialFreeVector (I := Fin N × Fin 3) radiationRoot) :
    (cutVector N L M u).value = (physicalElectronicFamily L).operator
      ((cutoff (Sector photonMeasure) M).compLpL 2 volume u.value) := rfl

/-- The local graph source is obtained from the actual free graph realization. -/
def cutSource (u : SpatialFreeVector (I := Fin N × Fin 3) radiationRoot)
    (hu : u.value ∈ photonSupport N r) : Domain N r L M := by
  let v := cutVector N L M u
  let q := (PhysicalFreeHilbert.covers (Fin N × Fin 3) v).choose
  have hq := (PhysicalFreeHilbert.covers (Fin N × Fin 3) v).choose_spec
  refine ⟨q, ?_⟩
  change PhysicalFreeHilbert.inclusion (Fin N × Fin 3) q ∈ localSupport N r L M
  rw [hq.1]
  exact cut_mem N r L M u.value hu

theorem cutSource_value (u : SpatialFreeVector (I := Fin N × Fin 3) radiationRoot)
    (hu : u.value ∈ photonSupport N r) :
    PhysicalFreeHilbert.inclusion (Fin N × Fin 3) (cutSource N r L M u hu).val =
      (cutVector N L M u).value :=
  (PhysicalFreeHilbert.covers (Fin N × Fin 3) (cutVector N L M u)).choose_spec.1

theorem supportValue_cutSource (u : SpatialFreeVector (I := Fin N × Fin 3) radiationRoot)
    (hu : u.value ∈ photonSupport N r) :
    supportValue N r L M (cutSource N r L M u hu) =
      (physicalElectronicFamily L).operator
        ((cutoff (Sector photonMeasure) M).compLpL 2 volume u.value) :=
  cutSource_value N r L M u hu

theorem cutSource_norm_sq (u : SpatialFreeVector (I := Fin N × Fin 3) radiationRoot)
    (hu : u.value ∈ photonSupport N r) :
    ‖cutSource N r L M u hu‖ ^ 2 = (cutVector N L M u).form :=
  (PhysicalFreeHilbert.covers (Fin N × Fin 3) (cutVector N L M u)).choose_spec.2

def localVector (u : SpatialFreeVector (I := Fin N × Fin 3) radiationRoot)
    (hu : u.value ∈ photonSupport N r) : Space N r L M :=
  inclusion N r L M (cutSource N r L M u hu)

theorem localVector_identity (u : SpatialFreeVector (I := Fin N × Fin 3) radiationRoot)
    (hu : u.value ∈ photonSupport N r) :
    embedding N r L M (localVector N r L M u hu) =
      (physicalElectronicFamily L).operator
        ((cutoff (Sector photonMeasure) M).compLpL 2 volume u.value) :=
  cutSource_value N r L M u hu

theorem cutSource_norm_sq_le (u : SpatialFreeVector (I := Fin N × Fin 3) radiationRoot)
    (hu : u.value ∈ photonSupport N r) :
    ‖cutSource N r L M u hu‖ ^ 2 ≤ 2 * u.form +
      (2 * Fintype.card (Fin N × Fin 3) *
        (physicalElectronicFamily (N := N) L).derivativeBound ^ 2) * ‖u.value‖ ^ 2 := by
  rw [cutSource_norm_sq]
  exact (physicalElectronicFamily L).cutVector_form_le (cutoff (Sector photonMeasure) M)
    (projection_norm_le _ (numberSectorCutoff_projection (photonSector photonMeasure)
      (photonSector_isStarProjection photonMeasure) (photonSector_orthogonal photonMeasure) M))
    (cutoff_radiation_graph M) u

end GptLean.PhysicalLocalFreeGraph
