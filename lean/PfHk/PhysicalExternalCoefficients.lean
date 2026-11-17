import PfHk.PhysicalCoordinateMultipliers
import PfHk.PhysicalExternalOperator
import PfHk.FriedrichsDivergenceBackground
import PfHk.SignedScalarMultiplier

/-! Real external coefficients and the actual multiplication domains of
their Hamiltonian expression. Coefficient hypotheses are ordinary Lp and
distributional divergence conditions. -/

noncomputable section
namespace PfHk.PhysicalExternalCoefficients

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.SymmetricLift
  PfHk.PhysicalLocalEnergy PfHk.PhysicalOperatorDomain
  PfHk.PhysicalCoordinateMultipliers PfHk.PhysicalExternalOperator
  PfHk.CoordinateSobolev PfHk.FriedrichsDivergenceBackground
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 40000

attribute [local irreducible] inclusion covariant ordinary radiation field

local instance coefficientPhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _

abbrev ElectronicPosition := GptLean.PhysicalSourceCoordinates.Position

structure Data (N : ℕ) where
  vectorCoefficient : Fin N → Fin 3 → ElectronicPosition → ℝ
  divergenceCoefficient : Fin N → ElectronicPosition → ℝ
  scalarCoefficient : Fin N → ElectronicPosition → ℝ
  boundedCoefficient : Configuration N → ℝ
  divergenceExponent : ℝ
  scalarExponent : ℝ
  divergenceExponent_gt_two : 2 < divergenceExponent
  scalarExponent_gt_two : 2 < scalarExponent
  vector_memLp : ∀ n i, MemLp (vectorCoefficient n i) 6 volume
  divergence_memLp : ∀ n,
    MemLp (divergenceCoefficient n) (ENNReal.ofReal divergenceExponent) volume
  scalar_memLp : ∀ n, MemLp (scalarCoefficient n) (ENNReal.ofReal scalarExponent) volume
  bounded_memLp : MemLp boundedCoefficient ∞ volume
  weakDivergence : ∀ n, WeakDivergence (vectorCoefficient n) (divergenceCoefficient n)

variable {N : ℕ}

def Data.vector (a : Data N) : (Fin N × Fin 3) → Configuration N → ℝ :=
  configurationVector a.vectorCoefficient

def Data.divergence (a : Data N) : Configuration N → ℝ :=
  configurationDivergence a.divergenceCoefficient

def Data.scalar (a : Data N) (x : Configuration N) : ℝ :=
  (∑ n, coordinateCoefficient n (a.scalarCoefficient n) x) + a.boundedCoefficient x

def Data.positive (a : Data N) : Configuration N → ℝ :=
  SignedScalarMultiplier.positiveAmplitude a.scalar

def Data.negative (a : Data N) : Configuration N → ℝ :=
  SignedScalarMultiplier.negativeAmplitude a.scalar

theorem Data.scalar_measurable (a : Data N) : AEStronglyMeasurable a.scalar volume :=
  (Finset.univ.aestronglyMeasurable_fun_sum fun n _ =>
    coordinateCoefficient_measurable n (a.scalar_memLp n).aestronglyMeasurable).add
      a.bounded_memLp.aestronglyMeasurable

theorem Data.scalar_hasMultiplier (a : Data N)
    (S : CoordinateSobolev.Data PhotonFock N)
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    (joint : CoordinateComparisonSpectral.Data spectral)
    (u : Reference (Fin N × Fin 3) (fun _ => 0))
    (hu : ComparisonDomain (fun _ => 0) u) :
    HasMultiplier a.scalar (inclusion (Fin N × Fin 3) (fun _ => 0) u) := by
  have hm (n : Fin N) := scalar_multiplier S spectral joint a.scalarExponent_gt_two
    n (a.scalarCoefficient n) (a.scalar_memLp n) u hu
  have hsum := sum_hasMultiplier Finset.univ
    (fun n => coordinateCoefficient n (a.scalarCoefficient n))
    (inclusion (Fin N × Fin 3) (fun _ => 0) u) (fun n _ => Classical.choose (hm n))
  have hb := bounded_multiplier a.boundedCoefficient a.bounded_memLp
    (inclusion (Fin N × Fin 3) (fun _ => 0) u)
  have hb' := Classical.choose hb
  let c : Bool → Configuration N → ℝ
    | true => fun x => ∑ n, coordinateCoefficient n (a.scalarCoefficient n) x
    | false => a.boundedCoefficient
  have hpair := sum_hasMultiplier (N := N) Finset.univ c
    (inclusion (Fin N × Fin 3) (fun _ => 0) u) (by
      intro j _
      cases j
      · exact hb'
      · exact hsum)
  have heq : (fun x => ∑ j : Bool, c j x) = a.scalar := by
    funext x
    simp only [Fintype.sum_bool, c, Data.scalar]
  exact (congrArg (fun b : Configuration N → ℝ =>
    HasMultiplier b (inclusion (Fin N × Fin 3) (fun _ => 0) u)) heq).mp hpair

/-- Every term in the external operator belongs to L2 on the actual
comparison domain. In particular no multiplication-domain hypothesis is
added to the full Hamiltonian theorem. -/
theorem Data.operatorMultipliers (a : Data N)
    (S : CoordinateSobolev.Data PhotonFock N)
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    (joint : CoordinateComparisonSpectral.Data spectral)
    (C : CanonicalSectorCCR photonMeasure)
    (κ : (Fin N × Fin 3) → Configuration N → WeightedPhotonKernel)
    (hκ : ∀ i : Fin N × Fin 3, AEStronglyMeasurable (κ i) volume)
    (M : ℝ) (hbound : ∀ i : Fin N × Fin 3, ∀ᵐ x : Configuration N ∂volume,
      ‖(κ i x).val‖ ≤ M) (e : ℝ)
    (u : Reference (Fin N × Fin 3) (fun _ => 0))
    (hu : ComparisonDomain (fun _ => 0) u) :
    OperatorMultipliers (fun _ => 0) C κ hκ M hbound e a.vector a.positive a.negative
      a.divergence u := by
  have hA (i : Fin N × Fin 3) := scalar_multiplier S spectral joint
    (show (2 : ℝ) < 6 by norm_num) i.1 (a.vectorCoefficient i.1 i.2)
    (by simpa using a.vector_memLp i.1 i.2) u hu
  have hAD (i : Fin N × Fin 3) := covariant_coordinate_multiplier S spectral joint
    C κ hκ M hbound e i.1 i (a.vectorCoefficient i.1 i.2)
    (a.vector_memLp i.1 i.2) u hu
  have hA₂ (i : Fin N × Fin 3) := scalar_multiplier S spectral joint
    (show (2 : ℝ) < 3 by norm_num) i.1 (fun x => a.vectorCoefficient i.1 i.2 x ^ 2)
    (by simpa using square_memLp_three (a.vector_memLp i.1 i.2)) u hu
  have hd (n : Fin N) := scalar_multiplier S spectral joint a.divergenceExponent_gt_two
    n (a.divergenceCoefficient n) (a.divergence_memLp n) u hu
  have hdiv := sum_hasMultiplier Finset.univ
    (fun n => coordinateCoefficient n (a.divergenceCoefficient n))
    (inclusion (Fin N × Fin 3) (fun _ => 0) u) (fun n _ => Classical.choose (hd n))
  have hscalar := a.scalar_hasMultiplier S spectral joint u hu
  refine {
    domain := {
      vector := fun i => Classical.choose (hA i)
      positive := SignedScalarMultiplier.hasMultiplier_positiveAmplitude _ a.scalar
        a.scalar_measurable hscalar
      negative := SignedScalarMultiplier.hasMultiplier_negativeAmplitude _ a.scalar
        a.scalar_measurable hscalar
    }
    vectorFirst := fun i => Classical.choose (hAD i)
    vectorSquare := ?_
    divergence := hdiv
    positiveSquare := SignedScalarMultiplier.hasMultiplier_positiveSquare _ a.scalar
      a.scalar_measurable hscalar
    negativeSquare := SignedScalarMultiplier.hasMultiplier_negativeSquare _ a.scalar
      a.scalar_measurable hscalar
  }
  intro i
  exact Classical.choose (hA₂ i)

end PfHk.PhysicalExternalCoefficients
