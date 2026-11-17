import GptLean.PhysicalFockExponential
import GptLean.PhysicalFockWordGram

/-!
The vacuum compression of the actual exponential map.

Its action on creation words, multiplication, and adjoint law are proved
on the same Fock space. Positivity for a retained map that is the square
of a self-adjoint contraction is then an operator identity.
-/

noncomputable section
namespace GptLean.PhysicalFock.VacuumOperator

open MeasureTheory UniformSpace Filter Topology
open PhotonLocalizationFockChannel TensorCoordinates
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]

def insertion : Fock μ →ₗᵢ[ℂ] TensorSpace (Fock μ) (Fock μ) :=
  (tensor.flip (creationWord μ [])).toLinearMap.isometryOfInner (fun u v => by
    change ⟪tensor u (creationWord μ []), tensor v (creationWord μ [])⟫_ℂ = _
    rw [tensor_inner, inner_self_eq_one_of_norm_eq_one (vacuum_norm μ), mul_one])

def contraction : TensorSpace (Fock μ) (Fock μ) →L[ℂ] Fock μ :=
  (insertion μ).toContinuousLinearMap.adjoint

theorem contraction_tensor (u v : Fock μ) :
    contraction μ (tensor u v) = ⟪creationWord μ [], v⟫_ℂ • u := by
  apply ext_inner_left ℂ
  intro z
  have ha := (insertion μ).toContinuousLinearMap.adjoint_inner_right z (tensor u v)
  have ht := tensor_inner z u (creationWord μ []) v
  exact ha.trans (ht.trans (by rw [inner_smul_right]; exact mul_comm _ _))

theorem contraction_norm_le (z : TensorSpace (Fock μ) (Fock μ)) :
    ‖contraction μ z‖ ≤ ‖z‖ := by
  have hn : ‖(insertion μ).toContinuousLinearMap‖ ≤ 1 :=
    (insertion μ).toContinuousLinearMap.opNorm_le_bound (by norm_num)
      (fun u => by simp only [LinearIsometry.coe_toContinuousLinearMap,
        LinearIsometry.norm_map, one_mul, le_refl])
  have ha : ‖contraction μ‖ ≤ 1 := by
    simpa only [contraction, ContinuousLinearMap.adjoint.norm_map] using hn
  exact (contraction μ).le_opNorm z |>.trans (by simpa using mul_le_mul_of_nonneg_right ha (norm_nonneg z))

variable (B : ConcreteExponentialLaw μ)

def operator (j : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ)) :
    Fock μ →L[ℂ] Fock μ := (contraction μ).comp (B.split μ j).toContinuousLinearMap

theorem operator_norm_le
    (j : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ)) (u : Fock μ) :
    ‖operator μ B j u‖ ≤ ‖u‖ :=
  (contraction_norm_le μ (B.split μ j u)).trans_eq ((B.split μ j).norm_map u)

omit [SigmaFinite μ] in
private theorem split_vacuum_eval {E : Type*} [AddCommMonoid E]
    (j : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ))
    (w : List (Lp ℂ 2 μ)) (F : List (Lp ℂ 2 μ) → E) :
    ((splitAssignments μ j w).map (fun p => if p.2 = [] then F p.1 else 0)).sum =
      F (w.map (retainedMap j)) := by
  classical
  induction w generalizing F with
  | nil => simp [splitAssignments]
  | cons f w ih =>
    simpa [splitAssignments, List.map_map, Function.comp_def] using
      ih (fun v => F (retainedMap j f :: v))

theorem operator_word
    (j : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ))
    (w : List (Lp ℂ 2 μ)) :
    operator μ B j (creationWord μ w) = creationWord μ (w.map (retainedMap j)) := by
  change contraction μ (B.split μ j (creationWord μ w)) = _
  rw [B.split_word, splitCreationTensor, map_list_sum]
  simp only [List.map_map, Function.comp_def, contraction_tensor, WordGram.vacuum_word_inner]
  have he (p : List (Lp ℂ 2 μ) × List (Lp ℂ 2 μ)) :
      (if p.2 = [] then (1 : ℂ) else 0) • creationWord μ p.1 =
        if p.2 = [] then creationWord μ p.1 else 0 := by
    split_ifs <;> simp
  simp only [he]
  exact split_vacuum_eval μ j w (creationWord μ)

theorem operator_mul
    (j k l : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ))
    (h : ∀ f, retainedMap j (retainedMap k f) = retainedMap l f) :
    (operator μ B j).comp (operator μ B k) = operator μ B l := by
  apply B.ext_words μ
  intro w
  simp only [ContinuousLinearMap.comp_apply, operator_word, List.map_map, Function.comp_def, h]

include B in
private theorem eq_of_inner_words (u v : Fock μ)
    (h : ∀ w, ⟪u, creationWord μ w⟫_ℂ = ⟪v, creationWord μ w⟫_ℂ) : u = v := by
  apply ext_inner_right ℂ
  intro z
  exact congrArg (fun A : Fock μ →L[ℂ] ℂ => A z)
    (B.ext_words μ (innerSL ℂ u) (innerSL ℂ v) h)

variable (C : CanonicalSectorCCR μ)

include C in
theorem operator_adjoint
    (j k : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ))
    (h : ∀ f g, ⟪retainedMap j f, g⟫_ℂ = ⟪f, retainedMap k g⟫_ℂ) :
    (operator μ B j).adjoint = operator μ B k := by
  apply B.ext_words μ
  intro w
  apply eq_of_inner_words μ B
  intro z
  rw [ContinuousLinearMap.adjoint_inner_left, operator_word, operator_word]
  simpa only [List.map_id] using
    WordGram.word_inner_of_gram μ C (id : Lp ℂ 2 μ → Lp ℂ 2 μ)
      (retainedMap k) (retainedMap j) id (fun f g => by
        change ⟪f, retainedMap j g⟫_ℂ = ⟪retainedMap k f, g⟫_ℂ
        simpa only [inner_conj_symm] using congrArg (starRingEnd ℂ) (h g f)) w z

private theorem selfadjoint_square_inner {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (hT : T.adjoint = T) (u : H) :
    (⟪u, T (T u)⟫_ℂ).re = ‖T u‖ ^ 2 := by
  have h := congrArg (fun A : H →L[ℂ] H => ⟪u, A (T u)⟫_ℂ) hT
  exact (congrArg Complex.re (h.symm.trans (T.adjoint_inner_right u (T u)))).trans
    (by simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow])

include C in
/-- The physical vacuum operator is positive and contractive whenever
the retained one-photon map is the square of a self-adjoint retained map. -/
theorem operator_positive_of_square
    (j k : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ))
    (hself : ∀ f g, ⟪retainedMap k f, g⟫_ℂ = ⟪f, retainedMap k g⟫_ℂ)
    (hsquare : ∀ f, retainedMap k (retainedMap k f) = retainedMap j f)
    (u : Fock μ) : ‖operator μ B j u‖ ^ 2 ≤ (⟪u, operator μ B j u⟫_ℂ).re := by
  have hm := operator_mul μ B k k j hsquare
  have ha := operator_adjoint μ B C k k hself
  have hv := congrArg (fun A : Fock μ →L[ℂ] Fock μ => A u) hm
  have he : (⟪u, operator μ B j u⟫_ℂ).re = ‖operator μ B k u‖ ^ 2 :=
    (congrArg (fun v : Fock μ => (⟪u, v⟫_ℂ).re) hv).symm.trans
      (selfadjoint_square_inner (operator μ B k) ha u)
  have hn := pow_le_pow_left₀ (norm_nonneg (operator μ B k (operator μ B k u)))
    (operator_norm_le μ B k (operator μ B k u)) 2
  exact ((congrArg (fun v : Fock μ => ‖v‖ ^ 2) hv).symm.trans_le hn).trans_eq he.symm

end GptLean.PhysicalFock.VacuumOperator
