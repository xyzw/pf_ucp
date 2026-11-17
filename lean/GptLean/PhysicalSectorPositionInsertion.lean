import GptLean.PhysicalSectorPositionComponents
import GptLean.PhysicalSectorHeadCoordinates
import GptLean.PhysicalOnePhotonFourier
import GptLean.PhysicalFourierProduct

/-!
Actual tensor insertion in photon position coordinates. Evaluating the
finite polarization fiber reduces the Fourier identity to the scalar
product theorem on the orthogonal head/tail split.
-/

noncomputable section
namespace GptLean.PhysicalSectorCoordinates

open MeasureTheory PhysicalFock PhysicalSectorMeasures PhysicalSectorHeadCoordinates
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 200000

private def oneEvaluation (p : Fin 2) : PhysicalOnePhotonFourier.Polarization →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun u := u p
      map_add' u v := Measure.ae_count_iff.mp (Lp.coeFn_add u v) p
      map_smul' c u := Measure.ae_count_iff.mp (Lp.coeFn_smul c u) p }

def photonMomentumComponent (f : Lp ℂ 2 photonMeasure) (p : Fin 2) :
    Lp ℂ 2 (volume : Measure Gaussian.FieldSpace) :=
  (oneEvaluation p).compLpL 2 volume (PhysicalSourceFubini.curryEquiv f)

def photonPositionComponent (f : Lp ℂ 2 photonMeasure) (p : Fin 2) :
    Lp ℂ 2 (volume : Measure Gaussian.FieldSpace) :=
  (oneEvaluation p).compLpL 2 volume (PhysicalOnePhotonFourier.fourier.symm f)

theorem photonMomentumComponent_represents_ae (f : Lp ℂ 2 photonMeasure) (p : Fin 2) :
    photonMomentumComponent f p =ᵐ[volume] fun k => f (k, p) := by
  filter_upwards [(oneEvaluation p).coeFn_compLpL (PhysicalSourceFubini.curryEquiv f),
    PhysicalSourceFubini.curryEquiv_represents_ae f] with k hk hf
  exact hk.trans (Measure.ae_count_iff.mp hf p)

theorem photonPositionComponent_ae (f : Lp ℂ 2 photonMeasure) (p : Fin 2) :
    photonPositionComponent f p =ᵐ[volume]
      fun x => PhysicalOnePhotonFourier.fourier.symm f x p :=
  (oneEvaluation p).coeFn_compLpL (PhysicalOnePhotonFourier.fourier.symm f)

theorem photonPositionComponent_fourierInv (f : Lp ℂ 2 photonMeasure) (p : Fin 2) :
    photonPositionComponent f p =
      (Lp.fourierTransformₗᵢ Gaussian.FieldSpace ℂ).symm (photonMomentumComponent f p) :=
  (PhysicalL2FourierTransport.fourierInv_compLpL (oneEvaluation p)
    (PhysicalSourceFubini.curryEquiv f)).symm

theorem momentumComponent_tensorInsertion (n : ℕ) (f : Lp ℂ 2 photonMeasure)
    (u : FullSector photonMeasure n) (p : Polarization (n + 1)) :
    momentumComponent (n + 1) (tensorInsertion photonMeasure n f u) p =
      Lp.compMeasurePreservingₗᵢ ℂ (split n) (split n).measurePreserving
        (PhysicalFourierProduct.product (photonMomentumComponent f (p 0))
          (momentumComponent n u (fun j => p j.succ))) := by
  apply Lp.ext
  have hi := Measure.ae_ae_of_ae_prod
    ((mode_measurePreserving (n + 1)).symm.quasiMeasurePreserving.ae
      (tensorInsertion_ae photonMeasure n f u))
  filter_upwards
    [momentumComponent_represents_ae (n + 1) (tensorInsertion photonMeasure n f u) p,
    hi, Lp.coeFn_compMeasurePreserving
      (PhysicalFourierProduct.product (photonMomentumComponent f (p 0))
        (momentumComponent n u (fun j => p j.succ))) (split n).measurePreserving,
    (split n).measurePreserving.quasiMeasurePreserving.ae
      (PhysicalFourierProduct.product_ae (photonMomentumComponent f (p 0))
        (momentumComponent n u (fun j => p j.succ))),
    (split_measurePreserving n).quasiMeasurePreserving.ae
      ((Measure.quasiMeasurePreserving_fst (ν := (volume : Measure (Configuration n)))).ae
        (photonMomentumComponent_represents_ae f (p 0))),
    (split_measurePreserving n).quasiMeasurePreserving.ae
      ((Measure.quasiMeasurePreserving_snd (μ := (volume : Measure Gaussian.FieldSpace))).ae
        (momentumComponent_represents_ae n u (fun j => p j.succ)))]
    with k hk hins hcomp hp hf hu
  have hi' := Measure.ae_count_iff.mp hins p
  change momentumComponent (n + 1) (tensorInsertion photonMeasure n f u) p k =
    (Lp.compMeasurePreserving (split n) (split n).measurePreserving
      (PhysicalFourierProduct.product (photonMomentumComponent f (p 0))
        (momentumComponent n u (fun j => p j.succ)))) k
  have hf' : photonMomentumComponent f (p 0) (split n k).fst =
      f ((split n k).fst, p 0) := hf
  have hu' : momentumComponent n u (fun j => p j.succ) (split n k).snd =
      u ((modeEquiv n).symm ((split n k).snd, fun j => p j.succ)) := hu
  rw [hk, hi', hcomp, Function.comp_apply, hp, hf', hu']
  rfl

/-- Inverse Fourier sends actual insertion to the head/tail position product. -/
theorem positionComponent_tensorInsertion (n : ℕ) (f : Lp ℂ 2 photonMeasure)
    (u : FullSector photonMeasure n) (p : Polarization (n + 1)) :
    positionComponent (n + 1) (tensorInsertion photonMeasure n f u) p =
      Lp.compMeasurePreservingₗᵢ ℂ (split n) (split n).measurePreserving
        (PhysicalFourierProduct.product (photonPositionComponent f (p 0))
          (positionComponent n u (fun j => p j.succ))) := by
  rw [positionComponent_fourierInv, momentumComponent_tensorInsertion,
    PhysicalL2FourierTransport.fourierInv_pull, PhysicalFourierProduct.fourierInv_productL2,
    photonPositionComponent_fourierInv, positionComponent_fourierInv]

/-- The representative formula used for support of creation words. -/
theorem positionComponent_tensorInsertion_ae (n : ℕ) (f : Lp ℂ 2 photonMeasure)
    (u : FullSector photonMeasure n) (p : Polarization (n + 1)) :
    positionComponent (n + 1) (tensorInsertion photonMeasure n f u) p =ᵐ[volume]
      fun x => PhysicalOnePhotonFourier.fourier.symm f (split n x).fst (p 0) *
        fullPosition n u (split n x).snd (fun j => p j.succ) := by
  rw [positionComponent_tensorInsertion]
  filter_upwards [Lp.coeFn_compMeasurePreserving
      (PhysicalFourierProduct.product (photonPositionComponent f (p 0))
        (positionComponent n u (fun j => p j.succ))) (split n).measurePreserving,
    (split n).measurePreserving.quasiMeasurePreserving.ae
      (PhysicalFourierProduct.product_ae (photonPositionComponent f (p 0))
        (positionComponent n u (fun j => p j.succ))),
    (split_measurePreserving n).quasiMeasurePreserving.ae
      ((Measure.quasiMeasurePreserving_fst (ν := (volume : Measure (Configuration n)))).ae
        (photonPositionComponent_ae f (p 0))),
    (split_measurePreserving n).quasiMeasurePreserving.ae
      ((Measure.quasiMeasurePreserving_snd (μ := (volume : Measure Gaussian.FieldSpace))).ae
        (positionComponent_ae n u (fun j => p j.succ)))] with x hx hp hf hu
  exact hx.trans (hp.trans (congrArg₂ (· * ·) hf hu))

end GptLean.PhysicalSectorCoordinates
