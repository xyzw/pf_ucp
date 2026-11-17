import GptLean.PhysicalFockCreationWords
import GptLean.PhysicalFockTensorCoordinates
import GptLean.PhotonLocalizationFockChannel

/-!
Model matching for the universal bosonic exponential law.

The explicitly named standard background is uniform in the measure space
and in every one-photon isometry. It is specified on finite words of the
actual normalized creation operators. The target is the actual completed
Hilbert tensor product, before any environmental coordinates or trace.
No localization inequality, chosen field error, or output form estimate
is a field of the background.

The physical Kraus isometry is then constructed by the previously proved
environmental coefficient map on the same photon Fock model.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace
open PhotonLocalizationFockChannel

section Words
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]

/-- The discarded component of an arbitrary one-photon isometry. -/
def discardedMap (j : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ)) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (WithLp.sndL 2 ℂ _ _).comp j.toContinuousLinearMap

/-- All retained/discarded assignments of a finite creation word. -/
def splitAssignments (j : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ)) :
    List (Lp ℂ 2 μ) → List (List (Lp ℂ 2 μ) × List (Lp ℂ 2 μ))
  | [] => [([], [])]
  | f :: w =>
      (splitAssignments j w).map (fun p => (retainedMap j f :: p.1, p.2)) ++
      (splitAssignments j w).map (fun p => (p.1, discardedMap μ j f :: p.2))

/-- The concrete tensor polynomial fixed by the bosonic exponential law. -/
def splitCreationTensor
    (j : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ))
    (w : List (Lp ℂ 2 μ)) : TensorCoordinates.TensorSpace (Fock μ) (Fock μ) :=
  ((splitAssignments μ j w).map fun p =>
    TensorCoordinates.tensor (creationWord μ p.1) (creationWord μ p.2)).sum

@[simp] theorem splitCreationTensor_nil
    (j : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ)) :
    splitCreationTensor μ j [] =
      TensorCoordinates.tensor (creationWord μ []) (creationWord μ []) := by
  simp [splitCreationTensor, splitAssignments]

/-- Standard symmetric-tensor density and exponential factorization on
one specified concrete symmetric L² model. The word law fixes the map. -/
structure ConcreteExponentialLaw : Prop where
  words_total : Dense (Submodule.span ℂ (Set.range (creationWord μ)) : Set (Fock μ))
  split_exists : ∀ (j : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ)),
    ∃ U : Fock μ →ₗᵢ[ℂ] TensorCoordinates.TensorSpace (Fock μ) (Fock μ),
      ∀ w, U (creationWord μ w) = splitCreationTensor μ j w

namespace ConcreteExponentialLaw
variable (B : ConcreteExponentialLaw μ)

def split (j : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ)) :
    Fock μ →ₗᵢ[ℂ] TensorCoordinates.TensorSpace (Fock μ) (Fock μ) :=
  (B.split_exists j).choose

theorem split_word (j : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ))
    (w : List (Lp ℂ 2 μ)) : B.split μ j (creationWord μ w) = splitCreationTensor μ j w :=
  (B.split_exists j).choose_spec w

include B in
/-- Equality on creation words fixes every continuous linear operator. -/
theorem ext_words {K : Type*} [NormedAddCommGroup K] [NormedSpace ℂ K]
    (U V : Fock μ →L[ℂ] K) (h : ∀ w, U (creationWord μ w) = V (creationWord μ w)) : U = V := by
  apply ContinuousLinearMap.ext
  have he : (U : Fock μ → K) = V := Continuous.ext_on B.words_total U.continuous V.continuous (by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨w, rfl⟩ := hu
      exact h w
    | zero => simp
    | add u v hu hv hU hV => simp only [map_add, hU, hV]
    | smul c u hu hU => simp only [map_smul, hU])
  exact congrFun he

theorem split_unique
    (j : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ))
    (U : Fock μ →ₗᵢ[ℂ] TensorCoordinates.TensorSpace (Fock μ) (Fock μ))
    (h : ∀ w, U (creationWord μ w) = splitCreationTensor μ j w) : U = B.split μ j := by
  have he := B.ext_words μ U.toContinuousLinearMap (B.split μ j).toContinuousLinearMap
    (fun w => (h w).trans (B.split_word μ j w).symm)
  apply LinearIsometry.ext
  intro u
  exact congrArg (fun A : Fock μ →L[ℂ] TensorCoordinates.TensorSpace (Fock μ) (Fock μ) => A u) he

def factorization
    (W : TensorCoordinates.TensorSpace (Fock μ) (Fock μ) →ₗᵢ[ℂ]
      lp (fun _ : ℕ => Fock μ) 2) : FockFactorization (Lp ℂ 2 μ) (Fock μ) where
  factor j := W.comp (B.split μ j)

theorem factorization_word
    (W : TensorCoordinates.TensorSpace (Fock μ) (Fock μ) →ₗᵢ[ℂ]
      lp (fun _ : ℕ => Fock μ) 2)
    (j : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ))
    (w : List (Lp ℂ 2 μ)) :
    (B.factorization μ W).factor j (creationWord μ w) = W (splitCreationTensor μ j w) :=
  congrArg W (B.split_word μ j w)

end ConcreteExponentialLaw
end Words

/-- The allowed universal symmetric-Fock background is independent of the
physical cutoff family and applies to every sigma-finite scalar L² model. -/
structure StandardSymmetricFockExponential : Prop where
  law : ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ],
    ConcreteExponentialLaw μ

variable (B : StandardSymmetricFockExponential)

include B in
theorem photonExponential : ConcreteExponentialLaw photonMeasure := B.law PhotonMode photonMeasure

/-- The actual photon Kraus factorization, using the fixed environmental basis. -/
def photonFactorization : FockFactorization (Lp ℂ 2 photonMeasure) PhotonFock :=
  (photonExponential B).factorization photonMeasure (environmentalCoordinates PhotonFock)

theorem photonFactorization_word
    (j : Lp ℂ 2 photonMeasure →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 photonMeasure × Lp ℂ 2 photonMeasure))
    (w : List (Lp ℂ 2 photonMeasure)) :
    (photonFactorization B).factor j (creationWord photonMeasure w) =
      environmentalCoordinates PhotonFock (splitCreationTensor photonMeasure j w) :=
  (photonExponential B).factorization_word photonMeasure (environmentalCoordinates PhotonFock) j w

theorem photonFactorization_vacuum
    (j : Lp ℂ 2 photonMeasure →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 photonMeasure × Lp ℂ 2 photonMeasure)) :
    (photonFactorization B).factor j (creationWord photonMeasure []) =
      environmentalCoordinates PhotonFock
        (TensorCoordinates.tensor (creationWord photonMeasure []) (creationWord photonMeasure [])) :=
  (photonFactorization_word B j []).trans
    (congrArg (environmentalCoordinates PhotonFock) (splitCreationTensor_nil photonMeasure j))

end GptLean.PhysicalFock
