import GptLean.PhysicalSourceFubiniEquiv
import GptLean.PhysicalFockSectors
import GptLean.PhotonLocalizationPhysicalKernelDuality
import Mathlib.Analysis.Fourier.LpSpace

/-!
The physical one-photon Fourier map uses the actual two-dimensional
polarization fiber, Mathlib's spatial L2 Fourier transform, and the proved
L2 Fubini equivalence. It fixes the map shared by photon localization and
finite-sector coordinates.
-/

noncomputable section

namespace GptLean.PhysicalOnePhotonFourier

open MeasureTheory PhysicalFock Gaussian PhotonLocalizationPhysicalKernels
open scoped ENNReal

abbrev Polarization := Lp ℂ 2 (Measure.count : Measure (Fin 2))
private def polarizationEval : Polarization →ₗ[ℂ] (Fin 2 → ℂ) where
  toFun u := u
  map_add' u v := funext (Measure.ae_count_iff.mp (Lp.coeFn_add u v))
  map_smul' c u := funext (Measure.ae_count_iff.mp (Lp.coeFn_smul c u))

instance polarizationFiniteDimensional : FiniteDimensional ℂ Polarization := by
  apply FiniteDimensional.of_injective polarizationEval
  intro u v h
  exact Lp.ext (ae_of_all _ fun x => congrFun h x)

abbrev PositionSpace := Lp Polarization 2 (volume : Measure FieldSpace)

/-- Spatial Fourier transform followed by exact polarization uncurrying. -/
def fourier : PositionSpace ≃ₗᵢ[ℂ] Lp ℂ 2 photonMeasure :=
  (Lp.fourierTransformₗᵢ FieldSpace Polarization).trans
    PhysicalSourceFubini.curryEquiv.symm

/-- The concrete momentum representative in each polarization. -/
theorem fourier_represents_ae (u : PositionSpace) :
    ∀ᵐ k ∂(volume : Measure FieldSpace), ∀ p : Fin 2,
      fourier u (k, p) = Lp.fourierTransformₗᵢ FieldSpace Polarization u k p := by
  have h := PhysicalSourceFubini.curryEquiv_represents_ae (fourier u)
  have he : PhysicalSourceFubini.curryEquiv (fourier u) =
      Lp.fourierTransformₗᵢ FieldSpace Polarization u := by
    exact LinearIsometryEquiv.apply_symm_apply _ _
  rw [he] at h
  filter_upwards [h] with k hk
  exact fun p => (Measure.ae_count_iff.mp hk p).symm

theorem momentum_nonzero : ∀ᵐ p ∂photonMeasure, p.1 ≠ (0 : FieldSpace) := by
  have h : ∀ᵐ k ∂(volume : Measure FieldSpace), k ≠ (0 : FieldSpace) :=
    volume.ae_ne 0
  exact (Measure.quasiMeasurePreserving_fst (ν := (Measure.count : Measure (Fin 2)))).ae h

/-- Only the universal radiation-energy coordinate realization remains a parameter. -/
def coordinates {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (energyFourier : V ≃ₗᵢ[ℂ] Lp ℂ 2 photonMeasure) :
    FourierRadiationCoordinates (E := Polarization) (V := V)
      (μ := (volume : Measure FieldSpace)) (ν := photonMeasure) where
  momentum := Prod.fst
  nonzero := momentum_nonzero
  fourier := fourier
  energyFourier := energyFourier

@[simp] theorem coordinates_fourier {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (energyFourier : V ≃ₗᵢ[ℂ] Lp ℂ 2 photonMeasure) :
    (coordinates energyFourier).fourier = fourier := rfl

@[simp] theorem coordinates_momentum {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (energyFourier : V ≃ₗᵢ[ℂ] Lp ℂ 2 photonMeasure) :
    (coordinates energyFourier).momentum = Prod.fst := rfl

end GptLean.PhysicalOnePhotonFourier
