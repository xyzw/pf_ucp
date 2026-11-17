import GptLean.PhysicalFockSectors
import GptLean.PhysicalPairIntegrability
import GptLean.RemovalSourceSymmetry
import GptLean.PhotonLocalizationNormalTrace
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.GroupTheory.Perm.Sign

/-!
The actual fermionic subspace of electronic L² with a spectator photon
fiber. Permutation pullbacks preserve volume, and the sign-character
subspace is closed. Its orthogonal projection gives the fermionic
compression on any standard normal trace realization.

Only the universal trace ideal operation is supplied below. No fermionic
projection, spectral support, or repaired-output support is assumed.
-/

noncomputable section

namespace GptLean.PhysicalElectronicFermions

open MeasureTheory Filter Topology SymmetricLift Repair PhotonLocalizationChannel
open scoped ENNReal InnerProductSpace

variable (N : ℕ) (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

abbrev FullSpace := Lp H 2 (volume : Measure (Configuration N))

def signCharacter (π : Equiv.Perm (Fin N)) : ℂ := (Equiv.Perm.sign π : ℤ)

theorem signCharacter_norm (π : Equiv.Perm (Fin N)) : ‖signCharacter N π‖ = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h
  · simp [signCharacter, h]
  · simp [signCharacter, h]

def permutation (π : Equiv.Perm (Fin N)) : FullSpace N H →ₗᵢ[ℂ] FullSpace N H :=
  Lp.compMeasurePreservingₗᵢ ℂ (permuteConfiguration π)
    (permuteConfiguration π).measurePreserving

theorem permutation_ae (π : Equiv.Perm (Fin N)) (u : FullSpace N H) :
    permutation N H π u =ᵐ[volume] fun x => u (permuteConfiguration π x) :=
  Lp.coeFn_compMeasurePreserving u (permuteConfiguration π).measurePreserving

def fermionicSubspace : Submodule ℂ (FullSpace N H) where
  carrier := {u | ∀ π, permutation N H π u = signCharacter N π • u}
  zero_mem' := by simp
  add_mem' := by
    intro u v hu hv π
    rw [map_add, hu π, hv π, smul_add]
  smul_mem' := by
    intro c u hu π
    rw [map_smul, hu π, smul_comm]

theorem fermionicSubspace_closed :
    IsClosed (fermionicSubspace N H : Set (FullSpace N H)) := by
  change IsClosed {u : FullSpace N H | ∀ π, permutation N H π u = signCharacter N π • u}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun π => isClosed_eq (permutation N H π).continuous
    (continuous_id.const_smul (signCharacter N π))

theorem mem_fermionicSubspace_iff (u : FullSpace N H) :
    u ∈ fermionicSubspace N H ↔
      HasElectronicCharacter (fun π => permuteConfiguration π) (signCharacter N) u := by
  constructor
  · intro hu π
    have hp := permutation_ae N H π u
    rw [hu π] at hp
    filter_upwards [hp, Lp.coeFn_smul (signCharacter N π) u] with x hx hs
    exact hx.symm.trans hs
  · intro hu π
    apply Lp.ext
    filter_upwards [permutation_ae N H π u, hu π,
      Lp.coeFn_smul (signCharacter N π) u] with x hp hx hs
    exact hp.trans (hx.trans hs.symm)

abbrev Space := ↥(fermionicSubspace N H)

variable [CompleteSpace H]

instance fermionicCompleteSpace : CompleteSpace (Space N H) :=
  (fermionicSubspace_closed N H).isComplete.completeSpace_coe

def inclusion : Space N H →ₗᵢ[ℂ] FullSpace N H :=
  (fermionicSubspace N H).subtypeₗᵢ

def projection : FullSpace N H →L[ℂ] FullSpace N H :=
  (fermionicSubspace N H).starProjection

theorem projection_isStarProjection : IsStarProjection (projection N H) :=
  isStarProjection_starProjection

theorem projection_eq_self_iff (u : FullSpace N H) :
    projection N H u = u ↔
      HasElectronicCharacter (fun π => permuteConfiguration π) (signCharacter N) u :=
  (fermionicSubspace N H).starProjection_eq_self_iff.trans
    (mem_fermionicSubspace_iff N H u)

theorem projection_character (u : FullSpace N H) :
    HasElectronicCharacter (fun π => permuteConfiguration π) (signCharacter N)
      (projection N H u) := by
  apply (projection_eq_self_iff N H _).mp
  exact congrArg (fun P : FullSpace N H →L[ℂ] FullSpace N H => P u)
    (projection_isStarProjection N H).isIdempotentElem.eq

omit [CompleteSpace H] in
theorem norm_permutation_ae (u : Space N H) (π : Equiv.Perm (Fin N)) :
    (fun x => ‖(u.val : Configuration N → H) (permuteConfiguration π x)‖) =ᵐ[volume]
      fun x => ‖u.val x‖ := by
  filter_upwards [(mem_fermionicSubspace_iff N H u.val).mp u.property π] with x hx
  rw [hx, norm_smul, signCharacter_norm, one_mul]

omit [CompleteSpace H] in
/-- Scalar configuration density is invariant under every electronic
permutation. This applies before taking a one-electron marginal. -/
theorem density_permutation_ae (u : Space N H) (π : Equiv.Perm (Fin N)) :
    (fun x => ‖(u.val : Configuration N → H) (permuteConfiguration π x)‖ ^ 2) =ᵐ[volume]
      fun x => ‖u.val x‖ ^ 2 :=
  (norm_permutation_ae N H u π).fun_comp (fun r : ℝ => r ^ 2)

omit [CompleteSpace H] in
/-- A covariant derivative carries both the sign and the permuted
particle index. Under that operator covariance, the actual current
pairing has precisely the corresponding permutation law. -/
theorem current_permutation_ae (u : Space N H)
    (d : Fin N × Fin 3 → FullSpace N H)
    (hd : ∀ (π : Equiv.Perm (Fin N)) (i : Fin N) (a : Fin 3),
      ∀ᵐ x ∂volume, d (i, a) (permuteConfiguration π x) =
        signCharacter N π • d (π.symm i, a) x)
    (π : Equiv.Perm (Fin N)) (i : Fin N) (a : Fin 3) :
    (fun x => PhysicalPairIntegrability.currentComponent
      (u.val (permuteConfiguration π x)) (d (i, a) (permuteConfiguration π x))) =ᵐ[volume]
      fun x => PhysicalPairIntegrability.currentComponent (u.val x) (d (π.symm i, a) x) := by
  filter_upwards [(mem_fermionicSubspace_iff N H u.val).mp u.property π,
    hd π i a] with x hu hx
  rw [hu, hx]
  unfold PhysicalPairIntegrability.currentComponent
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h
  · simp [signCharacter, h]
  · simp [signCharacter, h]

omit [CompleteSpace H] in
/-- Every particle has the same tested density marginal. The equality
comes from the actual volume-preserving transposition of coordinates. -/
theorem density_particle_integral_eq (u : Space N H) (i j : Fin N)
    (f : EuclideanSpace ℝ (Fin 3) → ℝ) :
    (∫ x, f (particle x i) * ‖u.val x‖ ^ 2) =
      ∫ x, f (particle x j) * ‖u.val x‖ ^ 2 := by
  let π := Equiv.swap i j
  have hp := (permuteConfiguration π).measurePreserving.integral_comp
    (permuteConfiguration π).toMeasurableEquiv.measurableEmbedding
    (fun x => f (particle x i) * ‖u.val x‖ ^ 2)
  rw [← hp]
  apply integral_congr_ae
  filter_upwards [density_permutation_ae N H u π] with x hx
  rw [hx, particle_permute]
  simp [π]

omit [CompleteSpace H] in
theorem density_particle_test_integrable (u : Space N H) (i : Fin N)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : Measurable f)
    {C : ℝ} (hbound : ∀ y, ‖f y‖ ≤ C) :
    Integrable (fun x => f (particle x i) * ‖u.val x‖ ^ 2) := by
  have hu : Integrable (fun x => ‖u.val x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u.val)).mp (Lp.memLp u.val)
  exact hu.bdd_mul
    ((hf.comp (particleLinear i).continuous_of_finiteDimensional.measurable).aestronglyMeasurable)
    (ae_of_all _ fun x => hbound (particle x i))

omit [CompleteSpace H] in
/-- The N-times-one-coordinate density formula, derived from fermionic
symmetry for every bounded measurable physical test. -/
theorem density_sum_integral (u : Space N H) (i₀ : Fin N)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : Measurable f)
    {C : ℝ} (hbound : ∀ y, ‖f y‖ ≤ C) :
    (∫ x, (∑ i : Fin N, f (particle x i)) * ‖u.val x‖ ^ 2) =
      (N : ℝ) * ∫ x, f (particle x i₀) * ‖u.val x‖ ^ 2 := by
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ => density_particle_test_integrable N H u i hf hbound)]
  simp_rw [density_particle_integral_eq N H u _ i₀ f]
  simp

omit [CompleteSpace H] in
theorem current_particle_integral_eq (u : Space N H)
    (d : Fin N × Fin 3 → FullSpace N H)
    (hd : ∀ (π : Equiv.Perm (Fin N)) (i : Fin N) (a : Fin 3),
      ∀ᵐ x ∂volume, d (i, a) (permuteConfiguration π x) =
        signCharacter N π • d (π.symm i, a) x)
    (i j : Fin N) (a : Fin 3) (f : EuclideanSpace ℝ (Fin 3) → ℝ) :
    (∫ x, f (particle x i) * PhysicalPairIntegrability.currentComponent (u.val x) (d (i, a) x)) =
      ∫ x, f (particle x j) * PhysicalPairIntegrability.currentComponent (u.val x) (d (j, a) x) := by
  let π := Equiv.swap i j
  have hp := (permuteConfiguration π).measurePreserving.integral_comp
    (permuteConfiguration π).toMeasurableEquiv.measurableEmbedding
    (fun x => f (particle x i) * PhysicalPairIntegrability.currentComponent (u.val x) (d (i, a) x))
  rw [← hp]
  apply integral_congr_ae
  filter_upwards [current_permutation_ae N H u d hd π i a] with x hx
  rw [hx, particle_permute]
  simp [π]

omit [CompleteSpace H] in
theorem current_particle_test_integrable (u : Space N H)
    (d : Fin N × Fin 3 → FullSpace N H) (i : Fin N) (a : Fin 3)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : Measurable f)
    {C : ℝ} (hbound : ∀ y, ‖f y‖ ≤ C) :
    Integrable (fun x => f (particle x i) *
      PhysicalPairIntegrability.currentComponent (u.val x) (d (i, a) x)) := by
  have hu : MemLp (fun x => PhysicalPairIntegrability.currentComponent
      (u.val x) (d (i, a) x)) 1 :=
    PhysicalPairIntegrability.currentComponent_memLp (Lp.memLp u.val) (Lp.memLp (d (i, a)))
  exact (memLp_one_iff_integrable.mp hu).bdd_mul
    ((hf.comp (particleLinear i).continuous_of_finiteDimensional.measurable).aestronglyMeasurable)
    (ae_of_all _ fun x => hbound (particle x i))

omit [CompleteSpace H] in
theorem current_sum_integral (u : Space N H)
    (d : Fin N × Fin 3 → FullSpace N H)
    (hd : ∀ (π : Equiv.Perm (Fin N)) (i : Fin N) (a : Fin 3),
      ∀ᵐ x ∂volume, d (i, a) (permuteConfiguration π x) =
        signCharacter N π • d (π.symm i, a) x)
    (i₀ : Fin N) (a : Fin 3)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : Measurable f)
    {C : ℝ} (hbound : ∀ y, ‖f y‖ ≤ C) :
    (∫ x, ∑ i : Fin N, f (particle x i) *
      PhysicalPairIntegrability.currentComponent (u.val x) (d (i, a) x)) =
      (N : ℝ) * ∫ x, f (particle x i₀) *
        PhysicalPairIntegrability.currentComponent (u.val x) (d (i₀, a) x) := by
  rw [integral_finsetSum _ (fun i _ => current_particle_test_integrable N H u d i a hf hbound)]
  simp_rw [current_particle_integral_eq N H u d hd _ i₀ a f]
  simp

omit [CompleteSpace H] in
/-- Every bounded operation on the spectator fiber preserves the
electronic sign character. This covers photon Kraus coordinates and
vacuum insertion when written as their pointwise fiber maps. -/
theorem fiberOperator_character {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] (B : H →L[ℂ] K) (u : FullSpace N H)
    (hu : HasElectronicCharacter (fun π => permuteConfiguration π) (signCharacter N) u) :
    HasElectronicCharacter (fun π => permuteConfiguration π) (signCharacter N)
      (B.compLpL 2 volume u) := by
  intro π
  have hb := B.coeFn_compLpL u
  have hp := (permuteConfiguration π).measurePreserving.quasiMeasurePreserving.ae_eq_comp hb
  filter_upwards [hb, hp, hu π] with x hx hp hxchar
  simp only [Function.comp_apply] at hp
  rw [hp, hxchar, map_smul, hx]

abbrev PhotonSpace (N : ℕ) := Space N PhysicalFock.PhotonFock

end GptLean.PhysicalElectronicFermions

namespace GptLean.PhotonLocalizationChannel

variable {H T : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup T] [NormedSpace ℝ T]

/-- The standard two-sided trace-ideal action, quantified over every
bounded Hilbert-space operator. The sole compatibility is its universal
rank-one evaluation. Fermionic support is proved from this operation. -/
structure NormalConjugationData (R : Gaussian.RankOneData H T) where
  conjugate : (H →L[ℂ] H) → T →L[ℝ] T
  rankOne : ∀ B v, conjugate B (R.rankOne v) = R.rankOne (B v)

namespace NormalConjugationData

variable {R : Gaussian.RankOneData H T} (C : NormalConjugationData R)

theorem positive (normal : NormalTraceData R) (B : H →L[ℂ] H)
    {x : T} (hx : x ∈ R.positive) : C.conjugate B x ∈ R.positive := by
  obtain ⟨v, hv⟩ := normal.positive_decomposition x hx
  have hs := (C.conjugate B).hasSum hv
  simp only [C.rankOne] at hs
  apply R.closed_positive.mem_of_tendsto hs
  apply Filter.Eventually.of_forall
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using R.zero_positive
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using R.add_positive (R.rankOne_positive (B (v a))) ih

/-- Every compression-fixed positive state has a countable source
decomposition consisting entirely of projection-fixed vectors. -/
theorem supported_decomposition (normal : NormalTraceData R) (P : H →L[ℂ] H)
    (hP : IsIdempotentElem P) {x : T} (hx : x ∈ R.positive)
    (hfixed : C.conjugate P x = x) :
    ∃ v : ℕ → H, HasSum (fun n => R.rankOne (v n)) x ∧ ∀ n, P (v n) = v n := by
  obtain ⟨v, hv⟩ := normal.positive_decomposition x hx
  refine ⟨fun n => P (v n), ?_, fun n => ?_⟩
  · simpa only [C.rankOne, hfixed] using (C.conjugate P).hasSum hv
  · exact congrArg (fun B : H →L[ℂ] H => B (v n)) hP.eq

theorem fixed_of_supported_decomposition (P : H →L[ℂ] H)
    {v : ℕ → H} {x : T} (hv : HasSum (fun n => R.rankOne (v n)) x)
    (hs : ∀ n, P (v n) = v n) : C.conjugate P x = x := by
  have h := (C.conjugate P).hasSum hv
  simp only [C.rankOne, hs] at h
  exact h.unique hv

end NormalConjugationData
end GptLean.PhotonLocalizationChannel

namespace GptLean.PhysicalElectronicFermions

open PhotonLocalizationChannel MeasureTheory SymmetricLift Repair

variable {N : ℕ} {H T : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup T] [NormedSpace ℝ T]
  {R : Gaussian.RankOneData (FullSpace N H) T}

def compression (C : NormalConjugationData R) : T →L[ℝ] T :=
  C.conjugate (projection N H)

theorem compression_rankOne_of_character (C : NormalConjugationData R)
    (u : FullSpace N H)
    (hu : HasElectronicCharacter (fun π => permuteConfiguration π) (signCharacter N) u) :
    compression C (R.rankOne u) = R.rankOne u := by
  rw [compression, C.rankOne, (projection_eq_self_iff N H u).mpr hu]

theorem compression_fixed_iff (C : NormalConjugationData R) (normal : NormalTraceData R)
    {x : T} (hx : x ∈ R.positive) :
    compression C x = x ↔ ∃ v : ℕ → FullSpace N H,
      HasSum (fun n => R.rankOne (v n)) x ∧ ∀ n,
        HasElectronicCharacter (fun π => permuteConfiguration π) (signCharacter N) (v n) := by
  constructor
  · intro h
    obtain ⟨v, hv, hs⟩ := C.supported_decomposition normal (projection N H)
      (projection_isStarProjection N H).isIdempotentElem hx h
    exact ⟨v, hv, fun n => (projection_eq_self_iff N H (v n)).mp (hs n)⟩
  · rintro ⟨v, hv, hs⟩
    exact C.fixed_of_supported_decomposition (projection N H) hv
      (fun n => (projection_eq_self_iff N H (v n)).mpr (hs n))

/-- The closed common fermionic state set, with its support predicate
identified by the preceding source-decomposition theorem. -/
def states (C : NormalConjugationData R) : Set T :=
  {x | x ∈ R.positive ∧ R.trace x = 1 ∧ compression C x = x}

theorem states_closed (C : NormalConjugationData R) : IsClosed (states C) :=
  R.closed_positive.inter ((isClosed_eq R.trace.continuous continuous_const).inter
    (isClosed_eq (compression C).continuous continuous_id))

end GptLean.PhysicalElectronicFermions
