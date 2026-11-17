import GptLean.PhysicalNormalCoordinates
import GptLean.PhysicalPFVacuumInsertion
import GptLean.PhysicalPhotonMarginalMoments

/-!
Countable coordinates of the actual photon marginal. The hard map first
inserts the physical vacuum and then uses the same full photon tests.
Coordinate equality determines positive photon traces, including their
extended number form. No finiteness of photon number is required.
-/

noncomputable section

namespace GptLean.PhysicalRemovalMarginal

open MeasureTheory PhysicalFock PhysicalNormalTrace PhysicalPhotonMarginal
  PhysicalPFVacuumInsertion
open scoped ENNReal InnerProductSpace BoundedContinuousFunction

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

abbrev Marginal := ℕ →ᵇ ℂ

def tests (n : ℕ) : Marginal →L[ℝ] ℂ := BoundedContinuousFunction.evalCLM ℝ n

theorem tests_separate (x y : Marginal) (h : ∀ n, tests n x = tests n y) : x = y := by
  ext n
  exact h n

def prepareMarginal : Marginal →L[ℝ] Marginal := ContinuousLinearMap.id ℝ Marginal

section Generic

variable {X H K : Type} [MeasurableSpace X] (μ : Measure X) [IsSeparable μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (B : StandardNormalTraceBackground)

private def compressedOperator (J : H →ₗᵢ[ℂ] K) (A : K →L[ℂ] K) : H →L[ℂ] H :=
  J.toContinuousLinearMap.adjoint.comp (A.comp J.toContinuousLinearMap)

theorem marginal_rankOne_observable (A : H →L[ℂ] H) (u : Lp H 2 μ) :
    (B.realization H).functional.repr
      (marginal B μ ((B.realization (Lp H 2 μ)).rank.rankOne u)) A =
        ∫ x, inner ℂ (u x) (A (u x)) ∂μ := by
  rw [marginal_evaluation B μ A ((B.realization (Lp H 2 μ)).rank.rankOne_positive u),
    (B.realization (Lp H 2 μ)).functional.rankOne, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [A.coeFn_compLpL u] with x hx
  rw [hx]

omit [IsSeparable μ] in
private theorem compressed_integral (J : H →ₗᵢ[ℂ] K) (A : K →L[ℂ] K) (u : Lp H 2 μ) :
    (∫ x, inner ℂ (spatialLift μ J u x) (A (spatialLift μ J u x)) ∂μ) =
      ∫ x, inner ℂ (u x)
        ((J.toContinuousLinearMap.adjoint.comp (A.comp J.toContinuousLinearMap)) (u x)) ∂μ := by
  apply integral_congr_ae
  filter_upwards [spatialLift_ae μ J u] with x hx
  rw [hx]
  exact (J.toContinuousLinearMap.adjoint_inner_right (u x) (A (J (u x)))).symm

private theorem pushed_marginal_rankOne_observable
    (J : H →ₗᵢ[ℂ] K) (A : K →L[ℂ] K) (u : Lp H 2 μ) :
    (B.realization K).functional.repr
      (B.push J.toContinuousLinearMap
        (marginal B μ ((B.realization (Lp H 2 μ)).rank.rankOne u))) A =
      ∫ x, inner ℂ (u x) (compressedOperator J A (u x)) ∂μ := by
  have he := marginal_rankOne μ B J u
  have htransport := congrArg
    (fun x : B.Trace K => (B.realization K).functional.repr x A) he.symm
  exact htransport.trans
    ((marginal_rankOne_observable μ B A (spatialLift μ J u)).trans
      (compressed_integral μ J A u))

end Generic

variable (B : StandardNormalTraceBackground)

def operators (n : ℕ) : PhotonFock →L[ℂ] PhotonFock :=
  normalOperators (B.realization PhotonFock).functional n

theorem operators_bound (n : ℕ) : ‖operators B n‖ ≤ 1 :=
  normalOperators_bound (B.realization PhotonFock).functional n

def photonCoordinates : B.Trace PhotonFock →L[ℝ] Marginal :=
  observableCoordinates (B.realization PhotonFock).functional (operators B) (operators_bound B)

@[simp] theorem photonCoordinates_apply (x : B.Trace PhotonFock) (n : ℕ) :
    tests n (photonCoordinates B x) = (B.realization PhotonFock).functional.repr x (operators B n) := rfl

theorem photonCoordinates_positive_injective {x y : B.Trace PhotonFock}
    (hx : x ∈ (B.realization PhotonFock).rank.positive)
    (hy : y ∈ (B.realization PhotonFock).rank.positive)
    (h : photonCoordinates B x = photonCoordinates B y) : x = y :=
  normalCoordinates_positive_injective (B.normal (H := PhotonFock))
    (B.realization PhotonFock).functional hx hy h

/-- The full extended photon number as a function of the separating coordinates. -/
def numberFromCoordinates : Marginal → ℝ≥0∞ :=
  positiveCoordinateValue (B.realization PhotonFock).functional
    (NormalPhoton.numberForm (B.normal (H := PhotonFock))
      (B.realization PhotonFock).functional).expectation

theorem numberFromCoordinates_apply {x : B.Trace PhotonFock}
    (hx : x ∈ (B.realization PhotonFock).rank.positive) :
    numberFromCoordinates B (photonCoordinates B x) =
      (NormalPhoton.numberForm (B.normal (H := PhotonFock))
        (B.realization PhotonFock).functional).expectation x :=
  positiveCoordinateValue_apply (B.normal (H := PhotonFock))
    (B.realization PhotonFock).functional _ hx

section Spatial

variable {X : Type} [MeasurableSpace X] (μ : Measure X) [IsSeparable μ]

def fullMarginal : B.Trace (Lp PhotonFock 2 μ) →L[ℝ] Marginal :=
  (photonCoordinates B).comp (marginal B μ)

theorem fullMarginal_rankOne (n : ℕ) (u : Lp PhotonFock 2 μ) :
    tests n (fullMarginal B μ ((B.realization (Lp PhotonFock 2 μ)).rank.rankOne u)) =
      ∫ x, inner ℂ (u x) (operators B n (u x)) ∂μ :=
  marginal_rankOne_observable μ B (operators B n) u

theorem fullMarginal_eq_photonMarginal {x y : B.Trace (Lp PhotonFock 2 μ)}
    (hx : x ∈ (B.realization (Lp PhotonFock 2 μ)).rank.positive)
    (hy : y ∈ (B.realization (Lp PhotonFock 2 μ)).rank.positive)
    (h : fullMarginal B μ x = fullMarginal B μ y) : marginal B μ x = marginal B μ y :=
  photonCoordinates_positive_injective B (marginal_positive B μ hx) (marginal_positive B μ hy) h

theorem numberFromCoordinates_fullMarginal {x : B.Trace (Lp PhotonFock 2 μ)}
    (hx : x ∈ (B.realization (Lp PhotonFock 2 μ)).rank.positive) :
    numberFromCoordinates B (fullMarginal B μ x) =
      (fullForm B μ (NormalPhoton.numberForm (B.normal (H := PhotonFock))
        (B.realization PhotonFock).functional)).expectation x :=
  numberFromCoordinates_apply B (marginal_positive B μ hx)

variable (BF : StandardSymmetricFockExponential) (κ : ℝ)

def hardMarginal : B.Trace (Lp (generatedFockSubspace (hardOnePhoton κ)) 2 μ) →L[ℝ] Marginal :=
  (photonCoordinates B).comp
    ((B.push (hardPhotonVacuumEmbedding BF κ).toContinuousLinearMap).comp (marginal B μ))

def hardOperator (n : ℕ) :
    generatedFockSubspace (hardOnePhoton κ) →L[ℂ] generatedFockSubspace (hardOnePhoton κ) :=
  compressedOperator (H := ↥(generatedFockSubspace (hardOnePhoton κ))) (K := PhotonFock)
    (hardPhotonVacuumEmbedding BF κ) (operators B n)

set_option maxHeartbeats 800000 in
/-- Every bounded photon observable has its actual vacuum-compressed fiber formula. -/
theorem hardMarginal_rankOne_observable (A : PhotonFock →L[ℂ] PhotonFock)
    (v : Lp (generatedFockSubspace (hardOnePhoton κ)) 2 μ) :
    (B.realization PhotonFock).functional.repr
      (B.push (hardPhotonVacuumEmbedding BF κ).toContinuousLinearMap
        (marginal B μ
          ((B.realization (Lp (generatedFockSubspace (hardOnePhoton κ)) 2 μ)).rank.rankOne v)))
      A = ∫ x, inner ℂ (v x)
        (((hardPhotonVacuumEmbedding BF κ).toContinuousLinearMap.adjoint.comp
          (A.comp (hardPhotonVacuumEmbedding BF κ).toContinuousLinearMap)) (v x)) ∂μ := by
  exact pushed_marginal_rankOne_observable
    (H := ↥(generatedFockSubspace (hardOnePhoton κ))) (K := PhotonFock)
    μ B (hardPhotonVacuumEmbedding BF κ) A v

theorem fullMarginal_push {x : B.Trace (Lp (generatedFockSubspace (hardOnePhoton κ)) 2 μ)}
    (hx : x ∈ (B.realization (Lp (generatedFockSubspace (hardOnePhoton κ)) 2 μ)).rank.positive) :
    fullMarginal B μ (B.push (insertion μ BF κ).toContinuousLinearMap x) =
      hardMarginal B μ BF κ x :=
  congrArg (photonCoordinates B) (insertion_marginal μ BF κ B hx)

theorem marginal_vacuum (v : Lp (generatedFockSubspace (hardOnePhoton κ)) 2 μ) :
    fullMarginal B μ
      ((B.realization (Lp PhotonFock 2 μ)).rank.rankOne (insertion μ BF κ v)) =
      prepareMarginal (hardMarginal B μ BF κ
        ((B.realization (Lp (generatedFockSubspace (hardOnePhoton κ)) 2 μ)).rank.rankOne v)) := by
  have h := fullMarginal_push B μ BF κ
    ((B.realization (Lp (generatedFockSubspace (hardOnePhoton κ)) 2 μ)).rank.rankOne_positive v)
  have he := congrArg (fullMarginal B μ)
    (B.push_rankOne (insertion μ BF κ).toContinuousLinearMap v)
  exact he.symm.trans h

theorem hardMarginal_rankOne (n : ℕ)
    (v : Lp (generatedFockSubspace (hardOnePhoton κ)) 2 μ) :
    tests n (prepareMarginal (hardMarginal B μ BF κ
      ((B.realization (Lp (generatedFockSubspace (hardOnePhoton κ)) 2 μ)).rank.rankOne v))) =
      ∫ x, inner ℂ (v x) (hardOperator B BF κ n (v x)) ∂μ := by
  exact hardMarginal_rankOne_observable B μ BF κ (operators B n) v

theorem numberFromCoordinates_hardMarginal
    {x : B.Trace (Lp (generatedFockSubspace (hardOnePhoton κ)) 2 μ)}
    (hx : x ∈ (B.realization (Lp (generatedFockSubspace (hardOnePhoton κ)) 2 μ)).rank.positive) :
    numberFromCoordinates B (hardMarginal B μ BF κ x) =
      (NormalPhoton.numberForm (B.normal (H := PhotonFock))
        (B.realization PhotonFock).functional).expectation
        (B.push (hardPhotonVacuumEmbedding BF κ).toContinuousLinearMap (marginal B μ x)) :=
  numberFromCoordinates_apply B
    (B.push_positive (hardPhotonVacuumEmbedding BF κ).toContinuousLinearMap (marginal_positive B μ hx))

end Spatial

end GptLean.PhysicalRemovalMarginal
