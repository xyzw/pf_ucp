import GptLean.PhysicalFockVacuumOperator
import GptLean.PhysicalFockCutoffRoot

/-!
Positivity of the actual vacuum operator for the physical cutoff channel.
The retained cutoff is the square of the constructed scalar root map.
Unitary Fourier transport and the creation-word operator law preserve
this identity on the concrete photon Fock space.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory PhotonLocalizationKernelCutoffs PhotonLocalizationFockChannel
open scoped ENNReal InnerProductSpace

variable {P E : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  [MeasurableSpace P] [BorelSpace P] {μ : Measure P}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [IsScalarTower ℝ ℂ E] [SMulCommClass ℝ ℂ E]
  (BF : StandardSymmetricFockExponential) (C : CanonicalSectorCCR photonMeasure)
  (e : Lp E 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 photonMeasure)

include C in
theorem photonVacuum_positive (r : ℝ) (u : PhotonFock) :
    ‖VacuumOperator.operator photonMeasure (photonExponential BF)
      (transportSplit e (complexOnePhotonIsometry r)) u‖ ^ 2 ≤
        (⟪u, VacuumOperator.operator photonMeasure (photonExponential BF)
          (transportSplit e (complexOnePhotonIsometry r)) u⟫_ℂ).re := by
  apply VacuumOperator.operator_positive_of_square photonMeasure (photonExponential BF) C
    (transportSplit e (complexOnePhotonIsometry r)) (transportSplit e (CutoffRoot.rootSplit r))
  · intro f g
    simp only [transportSplit_retained]
    calc
      _ = ⟪retainedMap (CutoffRoot.rootSplit r) (e.symm f), e.symm g⟫_ℂ := by
        rw [← e.inner_map_map, e.apply_symm_apply]
      _ = ⟪e.symm f, retainedMap (CutoffRoot.rootSplit r) (e.symm g)⟫_ℂ :=
        CutoffRoot.root_selfadjoint r (e.symm f) (e.symm g)
      _ = _ := by rw [← e.inner_map_map, e.apply_symm_apply]
  · intro f
    simp only [transportSplit_retained, e.symm_apply_apply, CutoffRoot.root_square]
    rfl

end GptLean.PhysicalFock
