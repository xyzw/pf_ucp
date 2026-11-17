import GptLean.PhysicalPFReference
import GptLean.ElectronicH1Map

/-!
Bounded fiber maps on the common Pauli--Fierz reference domain.

Let `L` be a bounded operator on the photon Fock space and `L_g` a bounded
operator on the radiation graph that lifts it, `ι (L_g q) = L (ι q)` for the
graph inclusion `ι`. Applying `L` at every configuration point to the
electronic and Coulomb graph coordinates, and `L_g` to the radiation
coordinate, maps the reference domain into itself:

`(L Ψ)(x) = L Ψ(x)`, `∂ᵢ (L Ψ) = L ∂ᵢ Ψ`, `√V (L Ψ) = L (√V Ψ)`.
-/

noncomputable section

namespace GptLean.PhysicalPFFiberMap

open MeasureTheory PhysicalFock PhysicalPFReference

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

variable {I : Type} [Fintype I] [DecidableEq I] (V : Position I → ℝ)
  (L : PhotonFock →L[ℂ] PhotonFock)

omit [DecidableEq I] in
theorem potentialMap_mem (p : PotentialGraph I V) :
    ((L.compLpL 2 volume p.val.1, L.compLpL 2 volume p.val.2) : WaveSpace I × WaveSpace I) ∈
      PhysicalMultiplicationGraph.graph volume (H := PhotonFock)
        (fun x => (Real.sqrt (V x) : ℂ)) := by
  have hp : ∀ᵐ x ∂volume, p.val.2 x = (Real.sqrt (V x) : ℂ) • p.val.1 x := p.property
  change ∀ᵐ x ∂volume, L.compLpL 2 volume p.val.2 x =
    (Real.sqrt (V x) : ℂ) • L.compLpL 2 volume p.val.1 x
  filter_upwards [hp, L.coeFn_compLpL p.val.1, L.coeFn_compLpL p.val.2] with x hx h₁ h₂
  exact h₂.trans ((congrArg L hx).trans ((L.map_smul _ _).trans
    (congrArg (fun z : PhotonFock => (Real.sqrt (V x) : ℂ) • z) h₁.symm)))

/-- The fiber map on the Coulomb graph. -/
def potentialMap : PotentialGraph I V →L[ℂ] PotentialGraph I V :=
  (((L.compLpL 2 volume).prodMap (L.compLpL 2 volume)).comp
    (PhysicalMultiplicationGraph.graph volume (H := PhotonFock)
      (fun x => (Real.sqrt (V x) : ℂ))).subtypeL).codRestrict _ (potentialMap_mem V L)

variable (Lg : RadiationGraphSpace →L[ℂ] RadiationGraphSpace)
  (hcomm : ∀ q, radiationGraphInclusion (Lg q) = L (radiationGraphInclusion q))

omit [DecidableEq I] in
include hcomm in
theorem inclusion_radiation (r : RadiationGraph I) :
    spatialRadiationInclusion volume (Lg.compLpL 2 volume r) =
      L.compLpL 2 volume (spatialRadiationInclusion volume r) :=
  (ElectronicH1Map.compLpL_comp radiationGraphInclusion Lg r).trans
    ((congrArg (fun K : RadiationGraphSpace →L[ℂ] PhotonFock => K.compLpL 2 volume r)
      (ContinuousLinearMap.ext hcomm)).trans
      (ElectronicH1Map.compLpL_comp L radiationGraphInclusion r).symm)

include hcomm in
theorem ambient_mem (u : Reference I V) :
    ((ElectronicH1Map.map L (electronic I V u),
      Lg.compLpL 2 volume (radiationSource I V u),
      potentialMap V L (potentialSource I V u)) : Ambient I V) ∈ referenceSubspace I V := by
  change (ElectronicH1Complex.value (ElectronicH1Map.map L (electronic I V u)) -
      spatialRadiationInclusion volume (Lg.compLpL 2 volume (radiationSource I V u)),
    ElectronicH1Complex.value (ElectronicH1Map.map L (electronic I V u)) -
      (potentialMap V L (potentialSource I V u)).val.1) = (0, 0)
  apply Prod.ext
  · exact sub_eq_zero.mpr ((congrArg (L.compLpL 2 volume) (radiation_matches I V u).symm).trans
      (inclusion_radiation L Lg hcomm (radiationSource I V u)).symm)
  · exact sub_eq_zero.mpr (congrArg (L.compLpL 2 volume) (potential_matches I V u).symm)

/-- **The fiber map on the reference domain.** -/
def map : Reference I V →L[ℂ] Reference I V :=
  (((ElectronicH1Map.map L).comp (electronic I V)).prod
    (((Lg.compLpL 2 volume).comp (radiationSource I V)).prod
      ((potentialMap V L).comp (potentialSource I V)))).codRestrict (referenceSubspace I V)
    (ambient_mem V L Lg hcomm)

theorem electronic_map (u : Reference I V) :
    electronic I V (map V L Lg hcomm u) = ElectronicH1Map.map L (electronic I V u) := rfl

theorem inclusion_map (u : Reference I V) :
    inclusion I V (map V L Lg hcomm u) = L.compLpL 2 volume (inclusion I V u) := rfl

theorem ordinary_map (i : I) (u : Reference I V) :
    ordinary I V i (map V L Lg hcomm u) = L.compLpL 2 volume (ordinary I V i u) := rfl

theorem radiationSource_map (u : Reference I V) :
    radiationSource I V (map V L Lg hcomm u) = Lg.compLpL 2 volume (radiationSource I V u) := rfl

theorem potential_map (u : Reference I V) :
    potential I V (map V L Lg hcomm u) = L.compLpL 2 volume (potential I V u) := rfl

end GptLean.PhysicalPFFiberMap
