import GptLean.PhysicalFullVacuumVectors
import GptLean.PhysicalPFFormEvaluation
import GptLean.PhysicalFermionicSeed

/-!
The scalar electronic H1 graph is inserted directly into the common PF
reference graph.  Its radiation coordinate is the actual vacuum graph,
and its potential coordinate is the transported multiplication graph.
-/

noncomputable section
namespace GptLean.PhysicalElectronicReference

open MeasureTheory PhysicalFock PhysicalPFReference ElectronicH1Complex
  PhysicalFullVacuum
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

local instance radiationNormedSpace : NormedSpace ℂ RadiationGraphSpace :=
  radiationRoot.graph.normedSpace

variable (I : Type) [Fintype I] [DecidableEq I]

abbrev ScalarWave := Lp ℂ 2 (volume : Measure (Position I))
abbrev ScalarH1 := ComplexH1 ℂ I

/-- Insertion commutes with the actual distributional derivatives. -/
def electronicInsertion : ScalarH1 I →L[ℂ] ElectronicGraph I :=
  ElectronicH1Map.map fiberInsertion.toContinuousLinearMap

theorem insertion_value (u : ScalarH1 I) :
    value (electronicInsertion I u) = insertion volume (value u) := rfl

theorem insertion_derivative (u : ScalarH1 I) (i : I) :
    derivative i (electronicInsertion I u) = insertion volume (derivative i u) := rfl

private def vacuumGraphInsertion : ℂ →L[ℂ] RadiationGraphSpace :=
  (ContinuousLinearMap.id ℂ ℂ).smulRight PhysicalFermionicSeed.vacuumGraph

private def radiationInsertion : ScalarWave I →L[ℂ] RadiationGraph I :=
  vacuumGraphInsertion.compLpL 2 volume

set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] PhysicalFullVacuum.insertion radiationRoot

private theorem zero_compLpL {X E H : Type} [MeasurableSpace X]
    (μ : Measure X) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup H] [NormedSpace ℂ H] (u : Lp E 2 μ) :
    (0 : E →L[ℂ] H).compLpL 2 μ u = 0 := by
  apply Lp.ext
  filter_upwards [(0 : E →L[ℂ] H).coeFn_compLpL u, Lp.coeFn_zero H 2 μ]
    with x hu hz
  exact hu.trans hz.symm

private theorem map_scalar_relation {X H : Type} [MeasurableSpace X]
    (μ : Measure X) [NormedAddCommGroup H] [NormedSpace ℂ H]
    (L : ℂ →L[ℂ] H) (u p : Lp ℂ 2 μ) (a : X → ℂ)
    (hp : ∀ᵐ x ∂μ, p x = a x • u x) :
    ∀ᵐ x ∂μ, L.compLpL 2 μ p x = a x • L.compLpL 2 μ u x := by
  filter_upwards [L.coeFn_compLpL p, L.coeFn_compLpL u, hp] with x ho hi hx
  exact ho.trans ((congrArg L hx).trans ((L.map_smul (a x) (u x)).trans
    (congrArg (a x • ·) hi.symm)))

private theorem vacuumGraphInsertion_value :
    radiationGraphInclusion.comp vacuumGraphInsertion = fiberInsertion.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro z
  change radiationGraphInclusion (z • PhysicalFermionicSeed.vacuumGraph) = z • vacuum
  exact radiationGraphInclusion.map_smul z PhysicalFermionicSeed.vacuumGraph

private theorem vacuumGraphInsertion_derivative :
    radiationGraphDerivative.comp vacuumGraphInsertion = 0 := by
  apply ContinuousLinearMap.ext
  intro z
  change radiationGraphDerivative (z • PhysicalFermionicSeed.vacuumGraph) = 0
  exact (radiationGraphDerivative.map_smul z PhysicalFermionicSeed.vacuumGraph).trans
    (smul_zero z)

omit [DecidableEq I] in
private theorem radiationInsertion_value (u : ScalarWave I) :
    spatialRadiationInclusion volume (radiationInsertion I u) = insertion volume u := by
  exact (ElectronicH1Map.compLpL_comp radiationGraphInclusion vacuumGraphInsertion u).trans
    ((congrArg (fun L : ℂ →L[ℂ] PhotonFock => L.compLpL 2 volume u)
      vacuumGraphInsertion_value).trans (by unfold insertion; rfl))

omit [DecidableEq I] in
private theorem radiationInsertion_derivative (u : ScalarWave I) :
    spatialRadiationDerivative volume (radiationInsertion I u) = 0 := by
  exact (ElectronicH1Map.compLpL_comp radiationGraphDerivative vacuumGraphInsertion u).trans
    ((congrArg (fun L : ℂ →L[ℂ] PhotonFock => L.compLpL 2 volume u)
      vacuumGraphInsertion_derivative).trans (zero_compLpL volume u))

variable (V : Position I → ℝ)

/-- The scalar potential graph is transported to the PF reference. -/
def reference (u : ScalarH1 I) (p : ScalarWave I)
    (hp : ∀ᵐ x ∂volume, p x = (Real.sqrt (V x) : ℂ) • value u x) : Reference I V :=
  ⟨(electronicInsertion I u, radiationInsertion I (value u),
    ⟨(insertion volume (value u), insertion volume p), by
      unfold insertion
      exact map_scalar_relation volume fiberInsertion.toContinuousLinearMap
        (value u) p (fun x => (Real.sqrt (V x) : ℂ)) hp⟩),
    Prod.ext
      (sub_eq_zero.mpr ((insertion_value I u).trans
        (radiationInsertion_value I (value u)).symm))
      (sub_eq_zero.mpr (insertion_value I u))⟩

theorem reference_value (u : ScalarH1 I) (p : ScalarWave I) (hp) :
    inclusion I V (reference I V u p hp) = insertion volume (value u) := insertion_value I u

theorem reference_ordinary (u : ScalarH1 I) (p : ScalarWave I) (hp) (i : I) :
    ordinary I V i (reference I V u p hp) = insertion volume (derivative i u) :=
  insertion_derivative I u i

theorem reference_radiation (u : ScalarH1 I) (p : ScalarWave I) (hp) :
    radiation I V (reference I V u p hp) = 0 :=
  radiationInsertion_derivative I (value u)

theorem reference_potential (u : ScalarH1 I) (p : ScalarWave I) (hp) :
    potential I V (reference I V u p hp) = insertion volume p := rfl

end GptLean.PhysicalElectronicReference
