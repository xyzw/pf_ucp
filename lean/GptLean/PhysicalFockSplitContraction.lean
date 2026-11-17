import GptLean.PhysicalFockExponential
import GptLean.PhysicalFockWordContraction

/-!
Retained annihilation intertwining on each fixed source number sector.

Kernel deletion commutes with assigning the remaining kernels to the
retained and discarded factors. This finite identity, the actual mixed
CCR and density of creation words prove an equality of bounded operators.
No graph-density or channel-form identity is assumed.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory PhotonLocalizationFockChannel
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types false

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]

section FiniteAlgebra
omit [SigmaFinite μ]
variable {E : Type*} [AddCommMonoid E] [Module ℂ E]

private def contractEval (f : Lp ℂ 2 μ) (w : List (Lp ℂ 2 μ))
    (F : List (Lp ℂ 2 μ) → E) : E :=
  ((wordContractionTerms μ f w).map fun p => p.1 • F p.2).sum

private def splitEval
    (j : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ))
    (w : List (Lp ℂ 2 μ)) (T : List (Lp ℂ 2 μ) × List (Lp ℂ 2 μ) → E) : E :=
  ((splitAssignments μ j w).map T).sum

private theorem contractEval_cons (f g : Lp ℂ 2 μ) (w : List (Lp ℂ 2 μ))
    (F : List (Lp ℂ 2 μ) → E) :
    contractEval μ f (g :: w) F = ⟪f, g⟫_ℂ • F w +
      contractEval μ f w (fun v => F (g :: v)) := by
  simp [contractEval, wordContractionTerms, List.map_map, Function.comp_def]

private theorem contractEval_add (f : Lp ℂ 2 μ) (w : List (Lp ℂ 2 μ))
    (F G : List (Lp ℂ 2 μ) → E) :
    contractEval μ f w (fun v => F v + G v) = contractEval μ f w F + contractEval μ f w G := by
  simp [contractEval, smul_add, List.sum_map_add]

omit [Module ℂ E] in
private theorem splitEval_cons
    (j : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ))
    (g : Lp ℂ 2 μ) (w : List (Lp ℂ 2 μ))
    (T : List (Lp ℂ 2 μ) × List (Lp ℂ 2 μ) → E) :
    splitEval μ j (g :: w) T =
      splitEval μ j w (fun p => T (retainedMap j g :: p.1, p.2)) +
      splitEval μ j w (fun p => T (p.1, discardedMap μ j g :: p.2)) := by
  simp [splitEval, splitAssignments, List.map_map, Function.comp_def]

omit [Module ℂ E] in
private theorem splitEval_add
    (j : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ))
    (w : List (Lp ℂ 2 μ)) (F G : List (Lp ℂ 2 μ) × List (Lp ℂ 2 μ) → E) :
    splitEval μ j w (fun p => F p + G p) = splitEval μ j w F + splitEval μ j w G := by
  simp [splitEval, List.sum_map_add]

private theorem splitEval_smul
    (j : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ))
    (w : List (Lp ℂ 2 μ)) (c : ℂ) (T : List (Lp ℂ 2 μ) × List (Lp ℂ 2 μ) → E) :
    splitEval μ j w (fun p => c • T p) = c • splitEval μ j w T := by
  simp [splitEval, List.smul_sum, List.map_map, Function.comp_def]

private theorem split_contract_eval
    (j : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ))
    (f : Lp ℂ 2 μ) (w : List (Lp ℂ 2 μ))
    (T : List (Lp ℂ 2 μ) × List (Lp ℂ 2 μ) → E) :
    splitEval μ j w (fun p => contractEval μ f p.1 (fun v => T (v, p.2))) =
      contractEval μ ((retainedMap j).adjoint f) w (fun v => splitEval μ j v T) := by
  induction w generalizing T with
  | nil => simp [splitEval, splitAssignments, contractEval, wordContractionTerms]
  | cons g w ih =>
    rw [splitEval_cons, contractEval_cons]
    simp_rw [contractEval_cons, splitEval_cons]
    rw [splitEval_add, splitEval_smul, contractEval_add,
      ih (fun p => T (retainedMap j g :: p.1, p.2)),
      ih (fun p => T (p.1, discardedMap μ j g :: p.2)),
      (retainedMap j).adjoint_inner_left]
    exact add_assoc _ _ _

end FiniteAlgebra

private theorem map_evaluated_list {α H K : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (A : H →L[ℂ] K) (l : List α) (p : α → H) (q : α → K)
    (h : ∀ x ∈ l, A (p x) = q x) :
    A ((l.map p).sum) = (l.map q).sum := by
  rw [map_list_sum]
  apply congrArg List.sum
  simp only [List.map_map]
  exact List.map_congr_left h

private theorem map_wordContraction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : Fock μ →L[ℂ] E) (f : Lp ℂ 2 μ) (w : List (Lp ℂ 2 μ)) :
    A (wordContraction μ f w) = contractEval μ f w (fun v => A (creationWord μ v)) :=
  map_evaluated_list A (wordContractionTerms μ f w)
    (fun p => p.1 • creationWord μ p.2) (fun p => p.1 • A (creationWord μ p.2))
    (fun p _ => A.map_smul p.1 (creationWord μ p.2))

omit [SigmaFinite μ] in
theorem splitAssignments_lengths
    (j : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ))
    (w : List (Lp ℂ 2 μ)) :
    ∀ p ∈ splitAssignments μ j w, p.1.length + p.2.length = w.length := by
  induction w with
  | nil => simp [splitAssignments]
  | cons g w ih =>
    intro p hp
    simp only [splitAssignments, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · simp only [List.length_cons]
      have h := ih q hq
      omega
    · simp only [List.length_cons]
      have h := ih q hq
      omega

variable (C : CanonicalSectorCCR μ) (B : ConcreteExponentialLaw μ)

include C in
set_option maxHeartbeats 400000 in
theorem retained_annihilation_split_word
    (j : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ))
    (M : ℕ) (f : Lp ℂ 2 μ) (w : List (Lp ℂ 2 μ)) (hw : w.length ≤ M) :
    TensorCoordinates.retainedOperator (annihilationFinite μ M f)
        (B.split μ j (creationWord μ w)) =
      B.split μ j (annihilationFinite μ M ((retainedMap j).adjoint f) (creationWord μ w)) := by
  have hleft : TensorCoordinates.retainedOperator (annihilationFinite μ M f)
      (splitCreationTensor μ j w) = splitEval μ j w (fun p =>
        contractEval μ f p.1 (fun v => TensorCoordinates.tensor (creationWord μ v) (creationWord μ p.2))) := by
    apply map_evaluated_list (TensorCoordinates.retainedOperator (annihilationFinite μ M f))
      (splitAssignments μ j w)
      (fun p => TensorCoordinates.tensor (creationWord μ p.1) (creationWord μ p.2))
      (fun p => contractEval μ f p.1 (fun v =>
        TensorCoordinates.tensor (creationWord μ v) (creationWord μ p.2)))
    intro p hp
    have hann := annihilationFinite_word μ C M f p.1 (by
      have hlen := splitAssignments_lengths μ j w p hp
      omega)
    exact (TensorCoordinates.retainedOperator_tensor (annihilationFinite μ M f)
      (creationWord μ p.1) (creationWord μ p.2)).trans
      ((congrArg (TensorCoordinates.tensor.flip (creationWord μ p.2)) hann).trans
        (map_wordContraction μ (TensorCoordinates.tensor.flip (creationWord μ p.2)) f p.1))
  have hright : B.split μ j (wordContraction μ ((retainedMap j).adjoint f) w) =
      contractEval μ ((retainedMap j).adjoint f) w (fun v =>
        splitEval μ j v (fun p => TensorCoordinates.tensor (creationWord μ p.1) (creationWord μ p.2))) := by
    apply map_evaluated_list (B.split μ j).toContinuousLinearMap
      (wordContractionTerms μ ((retainedMap j).adjoint f) w)
      (fun p => p.1 • creationWord μ p.2)
      (fun p => p.1 • splitEval μ j p.2 (fun q =>
        TensorCoordinates.tensor (creationWord μ q.1) (creationWord μ q.2)))
    intro p _
    exact ((B.split μ j).map_smul p.1 (creationWord μ p.2)).trans
      (congrArg (p.1 • ·) (B.split_word μ j p.2))
  calc
    _ = TensorCoordinates.retainedOperator (annihilationFinite μ M f) (splitCreationTensor μ j w) :=
      congrArg (TensorCoordinates.retainedOperator (annihilationFinite μ M f)) (B.split_word μ j w)
    _ = _ := hleft
    _ = _ := split_contract_eval μ j f w
      (fun p => TensorCoordinates.tensor (creationWord μ p.1) (creationWord μ p.2))
    _ = B.split μ j (wordContraction μ ((retainedMap j).adjoint f) w) := hright.symm
    _ = _ := congrArg (B.split μ j)
      (annihilationFinite_word μ C M ((retainedMap j).adjoint f) w hw).symm

include C in
/-- Bounded intertwining after a fixed input-sector projection, obtained by word density. -/
theorem retained_annihilation_split_sector
    (j : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ))
    (M n : ℕ) (hn : n ≤ M) (f : Lp ℂ 2 μ) (u : Fock μ) :
    TensorCoordinates.retainedOperator (annihilationFinite μ M f)
        (B.split μ j (photonSector μ n u)) =
      B.split μ j (annihilationFinite μ M ((retainedMap j).adjoint f) (photonSector μ n u)) := by
  let U := (TensorCoordinates.retainedOperator (annihilationFinite μ M f)).comp
    ((B.split μ j).toContinuousLinearMap.comp (photonSector μ n))
  let V := (B.split μ j).toContinuousLinearMap.comp
    ((annihilationFinite μ M ((retainedMap j).adjoint f)).comp (photonSector μ n))
  have he : U = V := B.ext_words μ U V (by
    intro w
    change TensorCoordinates.retainedOperator (annihilationFinite μ M f)
      (B.split μ j (photonSector μ n (creationWord μ w))) =
      B.split μ j (annihilationFinite μ M ((retainedMap j).adjoint f)
        (photonSector μ n (creationWord μ w)))
    rw [photonSector_word]
    split_ifs with h
    · exact retained_annihilation_split_word μ C B j M f w (h ▸ hn)
    · simp only [map_zero])
  exact congrArg (fun L : Fock μ →L[ℂ] TensorCoordinates.TensorSpace (Fock μ) (Fock μ) => L u) he

include C in
theorem factorization_annihilation_sector
    (W : TensorCoordinates.TensorSpace (Fock μ) (Fock μ) →ₗᵢ[ℂ] lp (fun _ : ℕ => Fock μ) 2)
    (hW : ∀ (A : Fock μ →L[ℂ] Fock μ) (z : TensorCoordinates.TensorSpace (Fock μ) (Fock μ))
      (a : ℕ), W (TensorCoordinates.retainedOperator A z) a = A (W z a))
    (j : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ))
    (M n : ℕ) (hn : n ≤ M) (f : Lp ℂ 2 μ) (u : Fock μ) (a : ℕ) :
    annihilationFinite μ M f ((B.factorization μ W).factor j (photonSector μ n u) a) =
      (B.factorization μ W).factor j
        (annihilationFinite μ M ((retainedMap j).adjoint f) (photonSector μ n u)) a :=
  (hW (annihilationFinite μ M f) (B.split μ j (photonSector μ n u)) a).symm.trans
    (congrArg (fun z => W z a) (retained_annihilation_split_sector μ C B j M n hn f u))

include C in
theorem factorization_annihilation_sector_hasSum
    (W : TensorCoordinates.TensorSpace (Fock μ) (Fock μ) →ₗᵢ[ℂ] lp (fun _ : ℕ => Fock μ) 2)
    (hW : ∀ (A : Fock μ →L[ℂ] Fock μ) (z : TensorCoordinates.TensorSpace (Fock μ) (Fock μ))
      (a : ℕ), W (TensorCoordinates.retainedOperator A z) a = A (W z a))
    (j : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ))
    (M n : ℕ) (hn : n ≤ M) (f : Lp ℂ 2 μ) (u : Fock μ) :
    HasSum (fun a => ‖annihilationFinite μ M f
      ((B.factorization μ W).factor j (photonSector μ n u) a)‖ ^ 2)
      (‖annihilationFinite μ M ((retainedMap j).adjoint f) (photonSector μ n u)‖ ^ 2) := by
  have h := coordinate_mass_hasSum (fun _ : ℕ => Fock μ)
    ((B.factorization μ W).factor j
      (annihilationFinite μ M ((retainedMap j).adjoint f) (photonSector μ n u)))
  rw [((B.factorization μ W).factor j).norm_map] at h
  simpa only [factorization_annihilation_sector μ C B W hW j M n hn f u] using h

/-- The retained annihilation identity on the fixed physical photon channel. -/
theorem photonFactorization_annihilation_sector
    (BF : StandardSymmetricFockExponential) (CCR : CanonicalSectorCCR photonMeasure)
    (j : Lp ℂ 2 photonMeasure →ₗᵢ[ℂ]
      WithLp 2 (Lp ℂ 2 photonMeasure × Lp ℂ 2 photonMeasure))
    (M n : ℕ) (hn : n ≤ M) (f : Lp ℂ 2 photonMeasure) (u : PhotonFock) (a : ℕ) :
    annihilationFinite photonMeasure M f
        ((photonFactorization BF).factor j (photonSector photonMeasure n u) a) =
      (photonFactorization BF).factor j
        (annihilationFinite photonMeasure M ((retainedMap j).adjoint f)
          (photonSector photonMeasure n u)) a :=
  factorization_annihilation_sector photonMeasure CCR (photonExponential BF)
    (environmentalCoordinates PhotonFock) environmentalCoordinates_retainedOperator j M n hn f u a

/-- Exact finite-sector rank-one pullback on the constructed physical channel. -/
theorem photonFactorization_annihilation_sector_hasSum
    (BF : StandardSymmetricFockExponential) (CCR : CanonicalSectorCCR photonMeasure)
    (j : Lp ℂ 2 photonMeasure →ₗᵢ[ℂ]
      WithLp 2 (Lp ℂ 2 photonMeasure × Lp ℂ 2 photonMeasure))
    (M n : ℕ) (hn : n ≤ M) (f : Lp ℂ 2 photonMeasure) (u : PhotonFock) :
    HasSum (fun a => ‖annihilationFinite photonMeasure M f
      ((photonFactorization BF).factor j (photonSector photonMeasure n u) a)‖ ^ 2)
      (‖annihilationFinite photonMeasure M ((retainedMap j).adjoint f)
        (photonSector photonMeasure n u)‖ ^ 2) :=
  factorization_annihilation_sector_hasSum photonMeasure CCR (photonExponential BF)
    (environmentalCoordinates PhotonFock) environmentalCoordinates_retainedOperator j M n hn f u

end GptLean.PhysicalFock
