import GptLean.SymmetricLift.PermutationGeometry
import Mathlib.Logic.Equiv.Sum
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Fintype.Card

/-! Nonduplicated coincidence blocks and the actual finite reindexing used by induction. -/
noncomputable section
namespace GptLean.SymmetricLift
open Set
open WithLp
open scoped BigOperators

/-- One particle's three spatial coordinates. -/
def particlePosition {N : ℕ} (x : Configuration N) (i : Fin N) : Fin 3 → ℝ :=
  fun μ => x (i, μ)

/-- The finite collection of distinct particle positions, so each block occurs once. -/
abbrev PositionClasses {N : ℕ} (x : Configuration N) := Set.range (particlePosition x)

instance positionClassesFintype {N : ℕ} (x : Configuration N) : Fintype (PositionClasses x) :=
  Fintype.ofFinite _

/-- Assign a particle to its unique coincidence class. -/
def particleClass {N : ℕ} (x : Configuration N) (i : Fin N) : PositionClasses x :=
  ⟨particlePosition x i, Set.mem_range_self i⟩

abbrev ClassBlock {N : ℕ} (x : Configuration N) (c : PositionClasses x) :=
  {i : Fin N // particleClass x i = c}

instance classBlockFintype {N : ℕ} (x : Configuration N) (c : PositionClasses x) :
    Fintype (ClassBlock x c) := Fintype.ofFinite _

/-- A canonical equivalence between the disjoint blocks and the original particle indices. -/
def blockReindex {N : ℕ} (x : Configuration N) :
    (Σ c : PositionClasses x, ClassBlock x c) ≃ Fin N :=
  Equiv.sigmaFiberEquiv (particleClass x)

@[simp] theorem blockReindex_apply {N : ℕ} (x : Configuration N)
    (c : PositionClasses x) (i : ClassBlock x c) : blockReindex x ⟨c, i⟩ = i.val := rfl

@[simp] theorem blockReindex_symm_apply {N : ℕ} (x : Configuration N) (i : Fin N) :
    (blockReindex x).symm i = ⟨particleClass x i, i, rfl⟩ := rfl

/-- Each nonduplicated block contains at least one actual particle. -/
instance classBlockNonempty {N : ℕ} (x : Configuration N) (c : PositionClasses x) :
    Nonempty (ClassBlock x c) := by
  obtain ⟨i, hi⟩ := c.property
  exact ⟨⟨i, Subtype.ext hi⟩⟩

theorem classBlock_card_pos {N : ℕ} (x : Configuration N) (c : PositionClasses x) :
    0 < Fintype.card (ClassBlock x c) := Fintype.card_pos

/-- The induction really uses lower particle numbers for every block. -/
theorem classBlock_card_lt {N : ℕ} {x : Configuration N}
    (hx : x ∈ centeredSphere N) (c : PositionClasses x) :
    Fintype.card (ClassBlock x c) < N := by
  have hex : ∃ i : Fin N, particleClass x i ≠ c := by
    by_contra h
    push_neg at h
    obtain ⟨a, b, μ, hab⟩ := sphere_has_distinct_points hx
    have ha := congrArg (fun d : PositionClasses x => d.val μ) (h a)
    have hb := congrArg (fun d : PositionClasses x => d.val μ) (h b)
    exact hab (ha.trans hb.symm)
  obtain ⟨i, hi⟩ := hex
  simpa only [Fintype.card_fin] using Fintype.card_subtype_lt (p := fun j : Fin N => particleClass x j = c) hi

/-- Finite block coordinates available for applying the lower-N induction hypothesis. -/
def blockEnumeration {N : ℕ} (x : Configuration N) (c : PositionClasses x) :
    ClassBlock x c ≃ Fin (Fintype.card (ClassBlock x c)) := Fintype.equivFin _

theorem particleClass_stabilizer {N : ℕ} (π : Equiv.Perm (Fin N))
    (x : Configuration N) (hπ : permuteConfiguration π x = x) (i : Fin N) :
    particleClass x (π i) = particleClass x i := by
  apply Subtype.ext
  funext μ
  exact (permutation_stabilizer_iff π x).mp hπ i μ

/-- A stabilizer acts as an actual permutation of each disjoint block. -/
def classBlockPermutation {N : ℕ} (π : Equiv.Perm (Fin N))
    (x : Configuration N) (hπ : permuteConfiguration π x = x) (c : PositionClasses x) :
    Equiv.Perm (ClassBlock x c) :=
  π.subtypePerm (fun i => by rw [particleClass_stabilizer π x hπ i])

/-- The restricted actions agree exactly with the global permutation under reindexing. -/
theorem blockReindex_permutation {N : ℕ} (π : Equiv.Perm (Fin N))
    (x : Configuration N) (hπ : permuteConfiguration π x = x)
    (c : PositionClasses x) (i : ClassBlock x c) :
    blockReindex x ⟨c, classBlockPermutation π x hπ c i⟩ =
      π (blockReindex x ⟨c, i⟩) := rfl

/-- The block decomposition includes every particle exactly once. -/
theorem sum_block_cards {N : ℕ} (x : Configuration N) :
    (∑ c : PositionClasses x, Fintype.card (ClassBlock x c)) = N := by
  rw [← Fintype.card_sigma]
  simpa only [Fintype.card_fin] using Fintype.card_congr (blockReindex x)

/-- Restrict a configuration to one block, using the chosen finite enumeration. -/
def blockConfigurationLinear {N : ℕ} (x : Configuration N) (c : PositionClasses x) :
    Configuration N →ₗ[ℝ] Configuration (Fintype.card (ClassBlock x c)) where
  toFun y := toLp 2 (fun q => y (((blockEnumeration x c).symm q.1).val, q.2))
  map_add' := by intro y z; ext q; rfl
  map_smul' := by intro a y; ext q; rfl

def blockConfiguration {N : ℕ} (x : Configuration N) (c : PositionClasses x) :
    Configuration N →L[ℝ] Configuration (Fintype.card (ClassBlock x c)) :=
  (blockConfigurationLinear x c).toContinuousLinearMap

@[simp] theorem blockConfiguration_apply {N : ℕ} (x : Configuration N)
    (c : PositionClasses x) (y : Configuration N)
    (i : Fin (Fintype.card (ClassBlock x c))) (μ : Fin 3) :
    blockConfiguration x c y (i, μ) = y (((blockEnumeration x c).symm i).val, μ) := rfl

theorem blockConfiguration_distinct {N : ℕ} (x : Configuration N)
    (c : PositionClasses x) {y : Configuration N} (hy : y ∈ distinctConfigurations N) :
    blockConfiguration x c y ∈ distinctConfigurations (Fintype.card (ClassBlock x c)) := by
  intro i j hij
  simp only [blockConfiguration_apply]
  apply hy
  intro heq
  exact hij ((blockEnumeration x c).symm.injective (Subtype.ext heq))

/-- The block permutation in the standard Fin coordinates of the induction hypothesis. -/
def indexedBlockPermutation {N : ℕ} (π : Equiv.Perm (Fin N))
    (x : Configuration N) (hπ : permuteConfiguration π x = x) (c : PositionClasses x) :
    Equiv.Perm (Fin (Fintype.card (ClassBlock x c))) :=
  (blockEnumeration x c).symm.trans ((classBlockPermutation π x hπ c).trans
    (blockEnumeration x c))

theorem indexedBlockPermutation_symm {N : ℕ} (π : Equiv.Perm (Fin N))
    (x : Configuration N) (hπ : permuteConfiguration π x = x) (c : PositionClasses x)
    (i : Fin (Fintype.card (ClassBlock x c))) :
    ((blockEnumeration x c).symm ((indexedBlockPermutation π x hπ c).symm i)).val =
      π.symm ((blockEnumeration x c).symm i).val := by
  simp only [indexedBlockPermutation, Equiv.symm_trans_apply,
    Equiv.symm_symm, Equiv.symm_apply_apply]
  rfl

/-- Restriction intertwines the actual particle actions. -/
theorem blockConfiguration_permute {N : ℕ} (π : Equiv.Perm (Fin N))
    (x : Configuration N) (hπ : permuteConfiguration π x = x) (c : PositionClasses x)
    (y : Configuration N) :
    blockConfiguration x c (permuteConfiguration π y) =
      permuteConfiguration (indexedBlockPermutation π x hπ c) (blockConfiguration x c y) := by
  ext ⟨i, μ⟩
  simp only [blockConfiguration_apply, permuteConfiguration_apply,
    indexedBlockPermutation_symm]

/-- The injection of a block's coordinate directions into the original coordinates. -/
def blockCoordinateEmbedding {N : ℕ} (x : Configuration N) (c : PositionClasses x) :
    Fin (Fintype.card (ClassBlock x c)) × Fin 3 ↪ Fin N × Fin 3 where
  toFun q := (((blockEnumeration x c).symm q.1).val, q.2)
  inj' := by
    intro p q hpq
    apply Prod.ext
    · apply (blockEnumeration x c).symm.injective
      apply Subtype.ext
      exact congrArg Prod.fst hpq
    · exact congrArg (fun z : Fin N × Fin 3 => z.2) hpq

theorem blockConfiguration_single_in {N : ℕ} (x : Configuration N) (c : PositionClasses x)
    (q : Fin (Fintype.card (ClassBlock x c)) × Fin 3) :
    blockConfiguration x c (EuclideanSpace.single (blockCoordinateEmbedding x c q) 1) =
      EuclideanSpace.single q 1 := by
  classical
  ext ⟨j, ν⟩
  simp only [blockConfiguration_apply, EuclideanSpace.single_apply]
  change (if blockCoordinateEmbedding x c (j, ν) = blockCoordinateEmbedding x c q then (1 : ℝ) else 0) =
    (if (j, ν) = q then 1 else 0)
  simp only [(blockCoordinateEmbedding x c).injective.eq_iff]

theorem blockConfiguration_single_out {N : ℕ} (x : Configuration N) (c : PositionClasses x)
    (q : Fin N × Fin 3) (hq : q ∉ Set.range (blockCoordinateEmbedding x c)) :
    blockConfiguration x c (EuclideanSpace.single q 1) = 0 := by
  classical
  ext ⟨j, ν⟩
  simp only [blockConfiguration_apply, EuclideanSpace.single_apply, PiLp.zero_apply]
  change (if blockCoordinateEmbedding x c (j, ν) = q then (1 : ℝ) else 0) = 0
  exact if_neg (fun h => hq ⟨(j, ν), h⟩)

/-- Restricting to a block preserves exactly the sum over its coordinate derivatives.
Directions outside that block contribute zero. -/
theorem blockConfiguration_coordinate_metric {N : ℕ} (x : Configuration N)
    (c : PositionClasses x) {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (L : Configuration (Fintype.card (ClassBlock x c)) →L[ℝ] K) :
    (∑ q : Fin N × Fin 3,
      ‖L (blockConfiguration x c (EuclideanSpace.single q 1))‖ ^ 2) =
      ∑ q : Fin (Fintype.card (ClassBlock x c)) × Fin 3, ‖L (EuclideanSpace.single q 1)‖ ^ 2 := by
  symm
  apply Fintype.sum_of_injective (blockCoordinateEmbedding x c)
    (blockCoordinateEmbedding x c).injective
  · intro q hq
    rw [blockConfiguration_single_out x c q hq, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  · intro q
    rw [blockConfiguration_single_in]

end GptLean.SymmetricLift
