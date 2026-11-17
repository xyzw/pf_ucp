import PfHk.PhysicalExternalSource
import PfHk.PhysicalRoughMultiplierSums
import PfHk.FiniteHamiltonianSum

/-! Identification of the finite coordinate product sum with the actual
perturbation in the weak Hamiltonian identity. -/

noncomputable section
namespace PfHk.PhysicalExternalSource

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open GptLean.SymmetricLift PfHk.PhysicalLocalEnergy PfHk.PhysicalExternalOperator
open PfHk.PhysicalExternalCoefficients PfHk.PhysicalCoordinateMultipliers PfHk.CoordinateSobolev
open PfHk.FriedrichsDivergenceBackground

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

attribute [local irreducible] inclusion covariant roughMultiply HasMultiplier perturbation total term
  PhysicalPFReference.referenceSubspace

variable {N : ℕ} (a : PfHk.PhysicalExternalCoefficients.Data N) (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Configuration N → WeightedPhotonKernel)
  (hκ : ∀ i : Fin N × Fin 3, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i : Fin N × Fin 3, ∀ᵐ x : Configuration N ∂volume, ‖(κ i x).val‖ ≤ M)
  (e : ℝ) (u : Reference (Fin N × Fin 3) (fun _ => 0))

set_option maxHeartbeats 60000 in
theorem total_eq_five_sums (P : Products a C κ hκ M hbound e u) :
    total a C κ hκ M hbound e u P =
      (∑ i : Fin N × Fin 3, roughMultiply (a.vector i)
        (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hbound e i u) (P.first i)) +
      (1 / 2 : ℂ) • (∑ i : Fin N × Fin 3, roughMultiply (fun x => a.vector i x ^ 2)
        (inclusion (Fin N × Fin 3) (fun _ => 0) u) (P.square i)) +
      (-Complex.I / 2) • (∑ n : Fin N, roughMultiply (coordinateCoefficient n (a.divergenceCoefficient n))
        (inclusion (Fin N × Fin 3) (fun _ => 0) u) (P.divergence n)) +
      ((∑ n : Fin N, roughMultiply (coordinateCoefficient n (a.scalarCoefficient n))
        (inclusion (Fin N × Fin 3) (fun _ => 0) u) (P.scalar n)) +
      roughMultiply a.boundedCoefficient (inclusion (Fin N × Fin 3) (fun _ => 0) u) P.bounded) := by
  have hsum := FiniteHamiltonianSum.sum_eq (H := WaveSpace (Fin N × Fin 3))
    (I := Fin N × Fin 3) (J := Fin N)
    (fun i => roughMultiply (a.vector i)
      (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hbound e i u) (P.first i))
    (fun i => roughMultiply (fun x => a.vector i x ^ 2)
      (inclusion (Fin N × Fin 3) (fun _ => 0) u) (P.square i))
    (fun n => roughMultiply (coordinateCoefficient n (a.divergenceCoefficient n))
      (inclusion (Fin N × Fin 3) (fun _ => 0) u) (P.divergence n))
    (fun n => roughMultiply (coordinateCoefficient n (a.scalarCoefficient n))
      (inclusion (Fin N × Fin 3) (fun _ => 0) u) (P.scalar n))
    (roughMultiply a.boundedCoefficient (inclusion (Fin N × Fin 3) (fun _ => 0) u) P.bounded)
  refine Eq.trans ?_ hsum
  unfold total
  apply Finset.sum_congr rfl
  intro t _
  rcases t with i | i | n | n | t <;>
    simp only [coefficient, term, FiniteHamiltonianSum.term, one_smul]

theorem perturbation_eq_total (P : Products a C κ hκ M hbound e u)
    (hu : OperatorMultipliers (fun _ => 0) C κ hκ M hbound e
      a.vector a.positive a.negative a.divergence u)
    (hscalar : HasMultiplier a.scalar (inclusion (Fin N × Fin 3) (fun _ => 0) u)) :
    perturbation (fun _ => 0) C κ hκ M hbound e a.vector a.positive a.negative a.divergence u hu =
      total a C κ hκ M hbound e u P := by
  have hsum := sum_hasMultiplier Finset.univ
    (fun n => coordinateCoefficient n (a.scalarCoefficient n))
    (inclusion (Fin N × Fin 3) (fun _ => 0) u) (fun n _ => P.scalar n)
  have hdiv := roughMultiply_sum
    (fun n => coordinateCoefficient n (a.divergenceCoefficient n))
    (inclusion (Fin N × Fin 3) (fun _ => 0) u) P.divergence hu.divergence
  have hscalarSum := roughMultiply_sum
    (fun n => coordinateCoefficient n (a.scalarCoefficient n))
    (inclusion (Fin N × Fin 3) (fun _ => 0) u) P.scalar hsum
  have hscalarAdd := roughMultiply_add
    (fun x => ∑ n, coordinateCoefficient n (a.scalarCoefficient n) x) a.boundedCoefficient
    (inclusion (Fin N × Fin 3) (fun _ => 0) u) hsum P.bounded hscalar
  have hsigned := SignedScalarMultiplier.operator_difference (inclusion (Fin N × Fin 3) (fun _ => 0) u)
    a.scalar hscalar hu.positiveSquare hu.negativeSquare
  have hgroup :
      perturbation (fun _ => 0) C κ hκ M hbound e a.vector a.positive a.negative a.divergence u hu =
      (∑ i : Fin N × Fin 3, roughMultiply (a.vector i) (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hbound e i u) (P.first i)) +
      (1 / 2 : ℂ) • (∑ i : Fin N × Fin 3, roughMultiply (fun x => a.vector i x ^ 2)
        (inclusion (Fin N × Fin 3) (fun _ => 0) u) (P.square i)) +
      (-Complex.I / 2) • roughMultiply a.divergence (inclusion (Fin N × Fin 3) (fun _ => 0) u) hu.divergence +
      (roughMultiply (fun x => a.positive x ^ 2) (inclusion (Fin N × Fin 3) (fun _ => 0) u) hu.positiveSquare -
        roughMultiply (fun x => a.negative x ^ 2) (inclusion (Fin N × Fin 3) (fun _ => 0) u) hu.negativeSquare) := by
    unfold perturbation
    exact FiniteHamiltonianSum.group_scalar _ _ _ _ _
  have hscalarFull := hsigned.trans (hscalarAdd.trans
    (congrArg (fun z : WaveSpace (Fin N × Fin 3) => z +
      roughMultiply a.boundedCoefficient (inclusion (Fin N × Fin 3) (fun _ => 0) u) P.bounded)
      hscalarSum))
  have hchange := congrArg₂ (fun (d s : WaveSpace (Fin N × Fin 3)) =>
      (∑ i : Fin N × Fin 3, roughMultiply (a.vector i)
        (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hbound e i u) (P.first i)) +
      (1 / 2 : ℂ) • (∑ i : Fin N × Fin 3, roughMultiply (fun x => a.vector i x ^ 2)
        (inclusion (Fin N × Fin 3) (fun _ => 0) u) (P.square i)) +
      (-Complex.I / 2) • d + s) hdiv hscalarFull
  exact hgroup.trans (hchange.trans (total_eq_five_sums a C κ hκ M hbound e u P).symm)

theorem perturbation_ae_total (P : Products a C κ hκ M hbound e u)
    (hu : OperatorMultipliers (fun _ => 0) C κ hκ M hbound e
      a.vector a.positive a.negative a.divergence u)
    (hscalar : HasMultiplier a.scalar (inclusion (Fin N × Fin 3) (fun _ => 0) u)) :
    (perturbation (fun _ => 0) C κ hκ M hbound e a.vector a.positive a.negative a.divergence u hu :
      Configuration N → PhotonFock) =ᵐ[volume]
      fun X => ∑ t, coefficient t • term a C κ hκ M hbound e u P t X := by
  have heq := perturbation_eq_total a C κ hκ M hbound e u P hu hscalar
  exact (Filter.EventuallyEq.of_eq
    (congrArg (fun z : WaveSpace (Fin N × Fin 3) => (z : Configuration N → PhotonFock)) heq)).trans
      (total_ae a C κ hκ M hbound e u P)

end PfHk.PhysicalExternalSource
