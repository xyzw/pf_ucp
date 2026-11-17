import GptLean.PhysicalSectorCoordinates
import GptLean.PhysicalL2FourierTransport
import GptLean.SymmetricLift.PermutationGeometry

/-!
Full position-sector coordinates and their individual polarization
components. The actual momentum permutation becomes the matching
orthogonal position permutation under inverse Fourier transform.
-/

noncomputable section
namespace GptLean.PhysicalSectorCoordinates

open MeasureTheory PhysicalFock PhysicalSectorMeasures
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 200000

/-- Evaluation at a polarization is continuous on the finite coefficient space. -/
def evaluation (m : ℕ) (p : Polarization m) : Coefficient m →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun u := u p
      map_add' u v := Measure.ae_count_iff.mp (Lp.coeFn_add u v) p
      map_smul' c u := Measure.ae_count_iff.mp (Lp.coeFn_smul c u) p }

@[simp] theorem evaluation_apply (m : ℕ) (p : Polarization m) (u : Coefficient m) :
    evaluation m p u = u p := rfl

/-- Position coordinates before restricting to the symmetric sector. -/
def fullPosition (m : ℕ) : FullSector photonMeasure m →ₗᵢ[ℂ]
    Lp (Coefficient m) 2 (volume : Measure (Configuration m)) :=
  (Lp.fourierTransformₗᵢ (Configuration m) (Coefficient m)).symm.toLinearIsometry.comp
    (fullMomentum m)

theorem sectorPosition_eq_fullPosition (m : ℕ) (u : Sector photonMeasure m) :
    sectorPosition m u = fullPosition m u.val := rfl

def momentumComponent (m : ℕ) (u : FullSector photonMeasure m) (p : Polarization m) :
    Lp ℂ 2 (volume : Measure (Configuration m)) :=
  (evaluation m p).compLpL 2 volume (fullMomentum m u)

def positionComponent (m : ℕ) (u : FullSector photonMeasure m) (p : Polarization m) :
    Lp ℂ 2 (volume : Measure (Configuration m)) :=
  (evaluation m p).compLpL 2 volume (fullPosition m u)

theorem momentumComponent_represents_ae (m : ℕ)
    (u : FullSector photonMeasure m) (p : Polarization m) :
    momentumComponent m u p =ᵐ[volume]
      fun k => u ((modeEquiv m).symm (k, p)) := by
  filter_upwards [(evaluation m p).coeFn_compLpL (fullMomentum m u),
    fullMomentum_represents_ae m u] with k hk hu
  exact hk.trans (hu p)

theorem positionComponent_ae (m : ℕ) (u : FullSector photonMeasure m)
    (p : Polarization m) :
    positionComponent m u p =ᵐ[volume] fun x => fullPosition m u x p :=
  (evaluation m p).coeFn_compLpL (fullPosition m u)

theorem positionComponent_fourierInv (m : ℕ) (u : FullSector photonMeasure m)
    (p : Polarization m) :
    positionComponent m u p =
      (Lp.fourierTransformₗᵢ (Configuration m) ℂ).symm (momentumComponent m u p) :=
  (PhysicalL2FourierTransport.fourierInv_compLpL (evaluation m p) (fullMomentum m u)).symm

private theorem modeEquiv_symm_momentum (m : ℕ) (k : Configuration m)
    (p : Polarization m) (i : Fin m) (a : Fin 3) :
    ((modeEquiv m).symm (k, p) i).1 a = k (i, a) := by
  have h := congrArg (fun z : Configuration m × Polarization m => z.1 (i, a))
    ((modeEquiv m).apply_symm_apply (k, p))
  simpa only [modeEquiv_momentum] using h

private theorem modeEquiv_symm_polarization (m : ℕ) (k : Configuration m)
    (p : Polarization m) (i : Fin m) :
    ((modeEquiv m).symm (k, p) i).2 = p i := by
  have h := congrArg (fun z : Configuration m × Polarization m => z.2 i)
    ((modeEquiv m).apply_symm_apply (k, p))
  simpa only [modeEquiv_polarization] using h

theorem momentumComponent_permutation (m : ℕ) (π : Equiv.Perm (Fin m))
    (u : FullSector photonMeasure m) (p : Polarization m) :
    momentumComponent m (permutation photonMeasure m π u) p =
      Lp.compMeasurePreservingₗᵢ ℂ (SymmetricLift.permuteConfiguration π)
        (SymmetricLift.permuteConfiguration π).measurePreserving
        (momentumComponent m u (fun j => p (π.symm j))) := by
  apply Lp.ext
  have hp := Measure.ae_ae_of_ae_prod
    ((mode_measurePreserving m).symm.quasiMeasurePreserving.ae
      (permutation_ae photonMeasure m π u))
  filter_upwards [momentumComponent_represents_ae m (permutation photonMeasure m π u) p,
    hp, Lp.coeFn_compMeasurePreserving (momentumComponent m u (fun j => p (π.symm j)))
      (SymmetricLift.permuteConfiguration π).measurePreserving,
    (SymmetricLift.permuteConfiguration π).measurePreserving.quasiMeasurePreserving.ae
      (momentumComponent_represents_ae m u (fun j => p (π.symm j)))]
    with k hk hpull hcomp hu
  have hperm := Measure.ae_count_iff.mp hpull p
  change momentumComponent m (permutation photonMeasure m π u) p k =
    (Lp.compMeasurePreserving (SymmetricLift.permuteConfiguration π)
      (SymmetricLift.permuteConfiguration π).measurePreserving
      (momentumComponent m u (fun j => p (π.symm j)))) k
  rw [hk, hcomp, Function.comp_apply, hu]
  have he : (MeasurableEquiv.piCongrLeft (fun _ : Fin m => PhotonMode) π)
      ((modeEquiv m).symm (k, p)) =
      (modeEquiv m).symm (SymmetricLift.permuteConfiguration π k,
        fun j => p (π.symm j)) := by
    funext j
    have hj := MeasurableEquiv.piCongrLeft_apply_apply π (β := fun _ => PhotonMode)
      ((modeEquiv m).symm (k, p)) (π.symm j)
    have hj' : (MeasurableEquiv.piCongrLeft (fun _ : Fin m => PhotonMode) π)
        ((modeEquiv m).symm (k, p)) j = (modeEquiv m).symm (k, p) (π.symm j) := by
      simpa only [Equiv.apply_symm_apply] using hj
    apply hj'.trans
    apply Prod.ext
    · ext a
      simp only [modeEquiv_symm_momentum, SymmetricLift.permuteConfiguration_apply]
    · simp only [modeEquiv_symm_polarization]
  exact hperm.trans (congrArg (fun z => u z) he)

/-- Polarizations and spatial coordinates carry the same particle permutation. -/
theorem positionComponent_permutation (m : ℕ) (π : Equiv.Perm (Fin m))
    (u : FullSector photonMeasure m) (p : Polarization m) :
    positionComponent m (permutation photonMeasure m π u) p =
      Lp.compMeasurePreservingₗᵢ ℂ (SymmetricLift.permuteConfiguration π)
        (SymmetricLift.permuteConfiguration π).measurePreserving
        (positionComponent m u (fun j => p (π.symm j))) := by
  rw [positionComponent_fourierInv, momentumComponent_permutation,
    PhysicalL2FourierTransport.fourierInv_pull, positionComponent_fourierInv]

/-- Vanishing of every finite polarization component is exactly vector vanishing. -/
theorem fullPosition_supported_iff (m : ℕ) (u : FullSector photonMeasure m)
    (s : Set (Configuration m)) :
    (∀ᵐ x ∂volume, x ∉ s → fullPosition m u x = 0) ↔
      ∀ p : Polarization m, ∀ᵐ x ∂volume, x ∉ s → positionComponent m u p x = 0 := by
  constructor
  · intro h p
    filter_upwards [h, positionComponent_ae m u p] with x hx hp
    intro hxs
    rw [hp, hx hxs]
    exact Measure.ae_count_iff.mp (Lp.coeFn_zero ℂ 2 (Measure.count : Measure (Polarization m))) p
  · intro h
    filter_upwards [ae_all_iff.mpr h, ae_all_iff.mpr (positionComponent_ae m u)] with x hx hp
    intro hxs
    apply Lp.ext
    apply ae_of_all
    intro p
    exact (hp p).symm.trans ((hx p hxs).trans
      (Measure.ae_count_iff.mp (Lp.coeFn_zero ℂ 2 (Measure.count : Measure (Polarization m))) p).symm)

end GptLean.PhysicalSectorCoordinates
