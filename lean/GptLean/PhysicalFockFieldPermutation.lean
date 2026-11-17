import GptLean.PhysicalFockFourierField
import GptLean.PhysicalElectronicFermions
import GptLean.SymmetricLift.PermutationMetric

/-!
Permutation covariance of the actual electronic-position field.

The radiation graph has an injective physical-value coordinate. Hence
a fermionic physical wave function has the same sign character in its
radiation-graph representative. The field acts on that representative
at the actual particle position, so its covariance follows from the
particle permutation law and complex linearity in the wave function.
-/

noncomputable section

namespace GptLean.PhysicalFock

open MeasureTheory SymmetricLift
open scoped ENNReal

set_option maxHeartbeats 1000000

theorem radiationGraphInclusion_injective : Function.Injective radiationGraphInclusion := by
  intro u v h
  have hz : (u - v).val.1 = 0 := sub_eq_zero.mpr h
  have ho := radiationRoot.graph_fst_eq_zero_snd (u - v).property hz
  apply Subtype.ext
  exact Prod.ext h (sub_eq_zero.mp ho)

variable {N : ℕ}

theorem spatialRadiationGraph_character (u : SpatialRadiationGraph
    (volume : Measure (Configuration N)))
    (hu : spatialRadiationInclusion volume u ∈
      PhysicalElectronicFermions.fermionicSubspace N PhotonFock)
    (π : Equiv.Perm (Fin N)) :
    ∀ᵐ x ∂volume, u (permuteConfiguration π x) =
      PhysicalElectronicFermions.signCharacter N π • u x := by
  have hI : spatialRadiationInclusion volume u =ᵐ[volume]
      fun x => radiationGraphInclusion (u x) := radiationGraphInclusion.coeFn_compLpL u
  have hp : ∀ᵐ x ∂volume,
      (spatialRadiationInclusion volume u) (permuteConfiguration π x) =
        radiationGraphInclusion (u (permuteConfiguration π x)) :=
    (permuteConfiguration π).measurePreserving.quasiMeasurePreserving.ae hI
  have hs := (PhysicalElectronicFermions.mem_fermionicSubspace_iff N PhotonFock
    (spatialRadiationInclusion volume u)).mp hu π
  filter_upwards [hp, hI, hs] with x hp hv hs
  apply radiationGraphInclusion_injective
  calc
    _ = (spatialRadiationInclusion volume u) (permuteConfiguration π x) := hp.symm
    _ = PhysicalElectronicFermions.signCharacter N π • (spatialRadiationInclusion volume u) x := hs
    _ = PhysicalElectronicFermions.signCharacter N π • radiationGraphInclusion (u x) :=
      congrArg (fun v : PhotonFock => PhysicalElectronicFermions.signCharacter N π • v) hv
    _ = _ := (map_smul radiationGraphInclusion (PhysicalElectronicFermions.signCharacter N π) (u x)).symm


variable (C : CanonicalSectorCCR photonMeasure)
  (κ : Fin 3 × Gaussian.FieldSpace → WeightedPhotonKernel) (hκ : Continuous κ)
  (M : ℝ) (hb : ∀ z, ‖κ z‖ ≤ M)

def particleField (i : Fin N) (a : Fin 3) :
    SpatialRadiationGraph (volume : Measure (Configuration N)) →L[ℂ]
      SpatialPhotonSpace (volume : Measure (Configuration N)) :=
  spatialField volume C (fun x => κ (a, particle x i))
    ((hκ.comp (continuous_const.prodMk (particleLinear i).continuous_of_finiteDimensional)).aestronglyMeasurable)
    M (ae_of_all _ fun x => hb (a, particle x i))

theorem particleField_ae (i : Fin N) (a : Fin 3)
    (u : SpatialRadiationGraph (volume : Measure (Configuration N))) :
    particleField C κ hκ M hb i a u =ᵐ[volume]
      fun x => kernelField C (κ (a, particle x i)) (u x) :=
  spatialField_ae volume C _ _ _ _ u

/-- This is the field part of the covariant-current permutation law. -/
theorem particleField_covariance
    (u : SpatialRadiationGraph (volume : Measure (Configuration N)))
    (hu : spatialRadiationInclusion volume u ∈
      PhysicalElectronicFermions.fermionicSubspace N PhotonFock)
    (π : Equiv.Perm (Fin N)) (i : Fin N) (a : Fin 3) :
    ∀ᵐ x ∂volume, (particleField C κ hκ M hb i a u) (permuteConfiguration π x) =
      PhysicalElectronicFermions.signCharacter N π •
        (particleField C κ hκ M hb (π.symm i) a u) x := by
  have hp : ∀ᵐ x ∂volume,
      (particleField C κ hκ M hb i a u) (permuteConfiguration π x) =
        kernelField C (κ (a, particle (permuteConfiguration π x) i)) (u (permuteConfiguration π x)) :=
    (permuteConfiguration π).measurePreserving.quasiMeasurePreserving.ae
      (particleField_ae C κ hκ M hb i a u)
  filter_upwards [hp, particleField_ae C κ hκ M hb (π.symm i) a u,
    spatialRadiationGraph_character u hu π] with x hp hf hu
  have hK : κ (a, particle (permuteConfiguration π x) i) = κ (a, particle x (π.symm i)) :=
    congrArg (fun y => κ (a, y)) (particle_permute π x i)
  calc
    _ = kernelField C (κ (a, particle (permuteConfiguration π x) i))
        (u (permuteConfiguration π x)) := hp
    _ = kernelField C (κ (a, particle x (π.symm i)))
        (PhysicalElectronicFermions.signCharacter N π • u x) :=
      congrArg₂ (fun k q => kernelField C k q) hK hu
    _ = PhysicalElectronicFermions.signCharacter N π •
        kernelField C (κ (a, particle x (π.symm i))) (u x) := map_smul _ _ _
    _ = _ := congrArg (fun v : PhotonFock => PhysicalElectronicFermions.signCharacter N π • v) hf.symm


end GptLean.PhysicalFock
