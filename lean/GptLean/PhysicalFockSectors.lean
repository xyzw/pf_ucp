import GptLean.PhysicalFockSpace
import GptLean.Gaussian.FieldMoments
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
The symmetric photon sectors as closed subspaces of concrete product L².

Coordinate permutations preserve the product measure. Their actual L²
pullbacks define a closed fixed subspace, which is the n-photon sector.
The bosonic Fock space is the Hilbert direct sum of these subspaces.
No sector projections, orthogonality or completeness identities are
assumed. The direct-sum construction supplies them on this same model.
-/

noncomputable section

namespace GptLean.PhysicalFock

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]

abbrev SectorMeasure (n : ℕ) : Measure (Fin n → Ω) := Measure.pi (fun _ => μ)

abbrev FullSector (n : ℕ) := Lp ℂ 2 (SectorMeasure μ n)

def permutation (n : ℕ) (π : Equiv.Perm (Fin n)) : FullSector μ n →ₗᵢ[ℂ] FullSector μ n :=
  Lp.compMeasurePreservingₗᵢ ℂ (MeasurableEquiv.piCongrLeft (fun _ : Fin n => Ω) π)
    (measurePreserving_piCongrLeft (fun _ : Fin n => μ) π)

theorem permutation_ae (n : ℕ) (π : Equiv.Perm (Fin n)) (u : FullSector μ n) :
    permutation μ n π u =ᵐ[SectorMeasure μ n]
      u ∘ MeasurableEquiv.piCongrLeft (fun _ : Fin n => Ω) π :=
  Lp.coeFn_compMeasurePreserving u
    (measurePreserving_piCongrLeft (fun _ : Fin n => μ) π)

def symmetricSubspace (n : ℕ) : Submodule ℂ (FullSector μ n) where
  carrier := {u | ∀ π, permutation μ n π u = u}
  zero_mem' := fun π => map_zero _
  add_mem' hu hv π := by rw [map_add, hu π, hv π]
  smul_mem' c u hu π := by rw [map_smul, hu π]

theorem symmetricSubspace_closed (n : ℕ) :
    IsClosed (symmetricSubspace μ n : Set (FullSector μ n)) := by
  change IsClosed {u : FullSector μ n | ∀ π, permutation μ n π u = u}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun π => isClosed_eq (permutation μ n π).continuous continuous_id

abbrev Sector (n : ℕ) := ↥(symmetricSubspace μ n)

instance sectorCompleteSpace (n : ℕ) : CompleteSpace (Sector μ n) :=
  (symmetricSubspace_closed μ n).isComplete.completeSpace_coe

/-- The sector inclusion is an isometry into the actual product L² space. -/
def sectorInclusion (n : ℕ) : Sector μ n →ₗᵢ[ℂ] FullSector μ n :=
  (symmetricSubspace μ n).subtypeₗᵢ

theorem symmetric_ae (n : ℕ) (u : Sector μ n) (π : Equiv.Perm (Fin n)) :
    (u.val : (Fin n → Ω) → ℂ) =ᵐ[SectorMeasure μ n]
      u.val ∘ MeasurableEquiv.piCongrLeft (fun _ : Fin n => Ω) π := by
  have h := permutation_ae μ n π u.val
  rw [u.property π] at h
  exact h

/-- The canonical Hilbert projection onto symmetric wave functions. -/
def symmetrizer (n : ℕ) : FullSector μ n →L[ℂ] FullSector μ n :=
  (symmetricSubspace μ n).starProjection

theorem symmetrizer_isStarProjection (n : ℕ) : IsStarProjection (symmetrizer μ n) :=
  isStarProjection_starProjection

theorem symmetrizer_eq_self (n : ℕ) (u : FullSector μ n) :
    symmetrizer μ n u = u ↔ ∀ π, permutation μ n π u = u :=
  (symmetricSubspace μ n).starProjection_eq_self_iff

abbrev Fock := Space (Sector μ)

/-- The actual bosonic number-sector projection. -/
def photonSector (n : ℕ) : Fock μ →L[ℂ] Fock μ := sector (Sector μ) n

theorem photonSector_isStarProjection (n : ℕ) : IsStarProjection (photonSector μ n) :=
  sector_isStarProjection (Sector μ) n

theorem photonSector_orthogonal (n m : ℕ) (h : n ≠ m) :
    photonSector μ n * photonSector μ m = 0 := sector_orthogonal (Sector μ) n m h

theorem photonSector_hasSum (u : Fock μ) : HasSum (fun n => photonSector μ n u) u :=
  sector_hasSum (Sector μ) u

theorem photonCutoff_tendsto (u : Fock μ) :
    Tendsto (fun M => cutoff (Sector μ) M u) atTop (𝓝 u) :=
  cutoff_tendsto (Sector μ) u

def photonNumberForm : Fock μ → ℝ≥0∞ := numberForm (Sector μ)

theorem photonNumber_sector (n : ℕ) (u : Fock μ) :
    photonNumberForm μ (photonSector μ n u) =
      ENNReal.ofReal ((n : ℝ) * ‖photonSector μ n u‖ ^ 2) :=
  numberForm_sector (Sector μ) n u

/-- Momentum and the two transverse polarization labels. -/
abbrev PhotonMode := Gaussian.FieldSpace × Fin 2

def photonMeasure : Measure PhotonMode := volume.prod Measure.count

instance photonMeasureSigmaFinite : SigmaFinite photonMeasure := by
  unfold photonMeasure
  infer_instance

/-- One fixed physical bosonic model used by the sector operators above. -/
abbrev PhotonFock := Fock photonMeasure

end GptLean.PhysicalFock
