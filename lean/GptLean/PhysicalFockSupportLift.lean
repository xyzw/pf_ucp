import GptLean.PhysicalFockChannel
import GptLean.PhysicalFockSupportedSubspaces

/-!
The generated photon subspaces on the actual electronic L² model.
The pointwise subspace is the kernel of the lifted complementary Hilbert
projection. Its almost-everywhere characterization proves support of the
constructed electronic Kraus vectors. One-photon Fourier transport uses
the actual image submodule.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory PhotonLocalizationFockChannel PhysicalNormalTrace.StandardNormalTraceBackground
open scoped ENNReal

section Spatial
variable {X H : Type*} [MeasurableSpace X] (μ : Measure X)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (V : Submodule ℂ H) [CompleteSpace V]

def spatialSubspace : Submodule ℂ (Lp H 2 μ) :=
  ((ContinuousLinearMap.id ℂ H - V.starProjection).compLpL 2 μ).ker

theorem mem_spatialSubspace (u : Lp H 2 μ) :
    u ∈ spatialSubspace μ V ↔ ∀ᵐ x ∂μ, u x ∈ V := by
  constructor
  · intro hu
    change (ContinuousLinearMap.id ℂ H - V.starProjection).compLpL 2 μ u = 0 at hu
    have ha := (ContinuousLinearMap.id ℂ H - V.starProjection).coeFn_compLpL u
    rw [hu] at ha
    filter_upwards [ha, Lp.coeFn_zero H 2 μ] with x hx hz
    apply V.starProjection_eq_self_iff.mp
    have he : u x - V.starProjection (u x) = 0 := hx.symm.trans hz
    exact (sub_eq_zero.mp he).symm
  · intro hu
    change (ContinuousLinearMap.id ℂ H - V.starProjection).compLpL 2 μ u = 0
    apply Lp.ext
    filter_upwards [(ContinuousLinearMap.id ℂ H - V.starProjection).coeFn_compLpL u,
      Lp.coeFn_zero H 2 μ, hu] with x hx hz hv
    have hp := V.starProjection_eq_self_iff.mpr hv
    exact hx.trans ((by simp only [sub_apply, ContinuousLinearMap.id_apply,
      hp, sub_self] : (ContinuousLinearMap.id ℂ H - V.starProjection) (u x) = 0).trans hz.symm)
end Spatial

instance generatedFockSubspace_complete (V : Submodule ℂ (Lp ℂ 2 photonMeasure)) :
    CompleteSpace (generatedFockSubspace V) :=
  (Submodule.isClosed_topologicalClosure _).isComplete.completeSpace_coe

variable (BF : StandardSymmetricFockExponential)

section Electronic
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

def electronicFockSubspaces : FockSubspaces (electronicFactorization μ (photonFactorization BF)) where
  fockSubspace V := spatialSubspace μ (generatedFockSubspace V)
  factor_mem j V hV u a := by
    apply (mem_spatialSubspace μ (generatedFockSubspace V) _).mpr
    filter_upwards [electronicFactorization_ae μ (photonFactorization BF) j u a] with x hx
    exact hx.symm ▸ (physicalFockSubspaces BF).factor_mem j V hV (u x) a
end Electronic

section Transport
variable {h k H : Type*} [NormedAddCommGroup h] [InnerProductSpace ℂ h]
  [NormedAddCommGroup k] [InnerProductSpace ℂ k]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def transportFockSubspaces (e : h ≃ₗᵢ[ℂ] k) (F : FockFactorization k H) (S : FockSubspaces F) :
    FockSubspaces (transportFactorization e F) where
  fockSubspace V := S.fockSubspace (V.map e.toLinearEquiv.toLinearMap)
  factor_mem j V hV u a := by
    apply S.factor_mem (transportSplit e j) (V.map e.toLinearEquiv.toLinearMap) _ u a
    intro f
    rw [transportSplit_retained]
    exact Submodule.mem_map_of_mem (hV (e.symm f))
end Transport

variable {h : Type} [NormedAddCommGroup h] [InnerProductSpace ℂ h]
  (e : h ≃ₗᵢ[ℂ] Lp ℂ 2 photonMeasure) (N : ℕ)

/-- The existing full support interface is filled on exactly `fullFactorization`. -/
def fullFockSubspaces : FockSubspaces (fullFactorization BF e N) :=
  transportFockSubspaces e
    (electronicFactorization (volume : Measure (SymmetricLift.Configuration N)) (photonFactorization BF))
    (electronicFockSubspaces BF volume)

end GptLean.PhysicalFock
