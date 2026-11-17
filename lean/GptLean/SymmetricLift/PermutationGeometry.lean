import GptLean.SymmetricLift.Configuration
import GptLean.SymmetricLift.Geometry
import GptLean.SymmetricLift.SmoothPartition
import GptLean.SymmetricLift.Normalization

/-! The actual particle-permutation action and smooth atlas of centered configurations. -/
noncomputable section
namespace GptLean.SymmetricLift
open Set WithLp
open scoped BigOperators ContDiff Topology

/-- Permute particles while keeping the spatial coordinate unchanged. -/
def permuteConfiguration {N : ℕ} (π : Equiv.Perm (Fin N)) :
    Configuration N ≃ₗᵢ[ℝ] Configuration N :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.prodCongr π (Equiv.refl (Fin 3)))

@[simp] theorem permuteConfiguration_apply {N : ℕ} (π : Equiv.Perm (Fin N))
    (x : Configuration N) (i : Fin N) (μ : Fin 3) :
    permuteConfiguration π x (i, μ) = x (π.symm i, μ) := rfl

@[simp] theorem permuteConfiguration_one {N : ℕ} (x : Configuration N) :
    permuteConfiguration (1 : Equiv.Perm (Fin N)) x = x := by
  ext i
  rfl

@[simp] theorem permuteConfiguration_mul {N : ℕ} (π σ : Equiv.Perm (Fin N))
    (x : Configuration N) :
    permuteConfiguration (π * σ) x = permuteConfiguration π (permuteConfiguration σ x) := by
  ext i
  rfl

instance permutationMulAction (N : ℕ) : MulAction (Equiv.Perm (Fin N)) (Configuration N) where
  smul π x := permuteConfiguration π x
  one_smul := permuteConfiguration_one
  mul_smul := permuteConfiguration_mul

@[simp] theorem permutation_smul_eq {N : ℕ} (π : Equiv.Perm (Fin N))
    (x : Configuration N) : π • x = permuteConfiguration π x := rfl

def configurationRepresentation (N : ℕ) :
    Equiv.Perm (Fin N) →* (Configuration N ≃L[ℝ] Configuration N) where
  toFun π := (permuteConfiguration π).toContinuousLinearEquiv
  map_one' := by ext x i; rfl
  map_mul' π σ := by ext x i; rfl

theorem permutation_contDiff {N : ℕ} (π : Equiv.Perm (Fin N)) :
    ContDiff ℝ ∞ (fun x : Configuration N => π • x) :=
  (permuteConfiguration π).toContinuousLinearEquiv.contDiff

theorem permutation_isometry {N : ℕ} (π : Equiv.Perm (Fin N)) :
    Isometry (fun x : Configuration N => π • x) :=
  (permuteConfiguration π).isometry

theorem meanCoordinate_permute {N : ℕ} (π : Equiv.Perm (Fin N))
    (x : Configuration N) (μ : Fin 3) :
    meanCoordinate (permuteConfiguration π x) μ = meanCoordinate x μ := by
  unfold meanCoordinate
  simp only [permuteConfiguration_apply]
  congr 1
  exact Fintype.sum_equiv π.symm _ _ (fun _ => rfl)

theorem center_permute {N : ℕ} (π : Equiv.Perm (Fin N)) (x : Configuration N) :
    center N (permuteConfiguration π x) = permuteConfiguration π (center N x) := by
  ext ⟨i, μ⟩
  simp only [center_apply, permuteConfiguration_apply, meanCoordinate_permute]

theorem normalizedCenter_permute {N : ℕ} (π : Equiv.Perm (Fin N))
    (x : Configuration N) :
    normalizedCenter N (permuteConfiguration π x) =
      permuteConfiguration π (normalizedCenter N x) := by
  simp only [normalizedCenter, center_permute, (permuteConfiguration π).norm_map,
    map_smul]

theorem centeredSphere_permute_iff {N : ℕ} (π : Equiv.Perm (Fin N))
    (x : Configuration N) :
    permuteConfiguration π x ∈ centeredSphere N ↔ x ∈ centeredSphere N := by
  simp only [centeredSphere, mem_setOf_eq, center_permute,
    (permuteConfiguration π).norm_map, (permuteConfiguration π).injective.eq_iff]

theorem distinctConfigurations_permute_iff {N : ℕ} (π : Equiv.Perm (Fin N))
    (x : Configuration N) :
    permuteConfiguration π x ∈ distinctConfigurations N ↔ x ∈ distinctConfigurations N := by
  constructor
  · intro hx i j hij
    obtain ⟨μ, hμ⟩ := hx (π i) (π j) (fun h => hij (π.injective h))
    exact ⟨μ, by simpa only [permuteConfiguration_apply, Equiv.symm_apply_apply] using hμ⟩
  · intro hx i j hij
    obtain ⟨μ, hμ⟩ := hx (π.symm i) (π.symm j) (fun h => hij (π.symm.injective h))
    exact ⟨μ, hμ⟩

theorem distinctConfigurations_isOpen (N : ℕ) : IsOpen (distinctConfigurations N) := by
  have heq : distinctConfigurations N =
      ⋂ i : Fin N, ⋂ j : Fin N,
        {x : Configuration N | i = j ∨ ∃ μ : Fin 3, x (i, μ) ≠ x (j, μ)} := by
    ext x
    simp only [distinctConfigurations, mem_setOf_eq, mem_iInter]
    constructor
    · intro h i j
      by_cases hij : i = j
      · exact Or.inl hij
      · exact Or.inr (h i j hij)
    · intro h i j hij
      exact (h i j).resolve_left hij
  rw [heq]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  by_cases hij : i = j
  · simpa only [hij, true_or, setOf_true] using (isOpen_univ : IsOpen (Set.univ : Set (Configuration N)))
  · have hne : IsOpen {x : Configuration N | ∃ μ : Fin 3, x (i, μ) ≠ x (j, μ)} := by
      simp only [setOf_exists]
      exact isOpen_iUnion fun μ => isOpen_ne_fun (PiLp.continuous_apply 2 (fun _ : Fin N × Fin 3 => ℝ) (i, μ))
        (PiLp.continuous_apply 2 (fun _ : Fin N × Fin 3 => ℝ) (j, μ))
    simpa only [hij, false_or] using hne

/-- The coincidence block containing a specified particle. -/
def coincidenceBlock {N : ℕ} (x : Configuration N) (i : Fin N) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun j => ∀ μ : Fin 3, x (j, μ) = x (i, μ))

/-- A stabilizing permutation only permutes particles inside their coincidence blocks. -/
theorem permutation_stabilizer_iff {N : ℕ} (π : Equiv.Perm (Fin N))
    (x : Configuration N) :
    permuteConfiguration π x = x ↔ ∀ i μ, x (π i, μ) = x (i, μ) := by
  constructor
  · intro h i μ
    have he := congrArg (fun y : Configuration N => y (π i, μ)) h
    simpa only [permuteConfiguration_apply, Equiv.symm_apply_apply] using he.symm
  · intro h
    ext ⟨i, μ⟩
    simpa only [permuteConfiguration_apply, Equiv.apply_symm_apply] using
      (h (π.symm i) μ).symm

theorem coincidenceBlock_permute_mem_iff {N : ℕ} (π : Equiv.Perm (Fin N))
    (x : Configuration N) (hπ : permuteConfiguration π x = x) (i j : Fin N) :
    π j ∈ coincidenceBlock x i ↔ j ∈ coincidenceBlock x i := by
  classical
  simp only [coincidenceBlock, Finset.mem_filter, Finset.mem_univ, true_and,
    (permutation_stabilizer_iff π x).mp hπ]

/-- The genuine permutation induced on each proper coincidence block. -/
def blockPermutation {N : ℕ} (π : Equiv.Perm (Fin N)) (x : Configuration N)
    (hπ : permuteConfiguration π x = x) (i : Fin N) :
    Equiv.Perm (coincidenceBlock x i) :=
  π.subtypePerm (coincidenceBlock_permute_mem_iff π x hπ i)

theorem coincidenceBlock_card_lt {N : ℕ} {x : Configuration N}
    (hx : x ∈ centeredSphere N) (i : Fin N) : (coincidenceBlock x i).card < N := by
  classical
  obtain ⟨a, b, μ, hab⟩ := sphere_has_distinct_points hx
  have hex : ∃ j : Fin N, ∃ ν : Fin 3, x (j, ν) ≠ x (i, ν) := by
    by_contra h
    push_neg at h
    exact hab ((h a μ).trans (h b μ).symm)
  obtain ⟨j, ν, hj⟩ := hex
  have hjnot : j ∉ coincidenceBlock x i := by
    simp only [coincidenceBlock, Finset.mem_filter, Finset.mem_univ, true_and]
    intro h
    exact hj (h ν)
  have hssub : coincidenceBlock x i ⊂ Finset.univ := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    intro heq
    exact hjnot (heq ▸ Finset.mem_univ j)
  simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_lt_card hssub

/-- All of the smooth atlas data are constructed on the concrete configuration
sphere. Its centers and radii are independent of the electronic Hilbert space. -/
structure CenteredAtlas (N : ℕ) where
  radius : centeredSphere N → ℝ
  radius_pos : ∀ c, 0 < radius c
  orbit_separated : ∀ (c : centeredSphere N) (π σ : Equiv.Perm (Fin N)),
    π • (c : Configuration N) = σ • (c : Configuration N) ∨
      Disjoint (Metric.ball (π • (c : Configuration N)) (radius c))
        (Metric.ball (σ • (c : Configuration N)) (radius c))
  charts : Finset (centeredSphere N)
  neighborhood : Set (Configuration N)
  isOpen_neighborhood : IsOpen neighborhood
  sphere_subset : centeredSphere N ⊆ neighborhood
  invariant_neighborhood : ∀ (π : Equiv.Perm (Fin N)) x,
    π • x ∈ neighborhood ↔ x ∈ neighborhood
  weights : charts → Configuration N → ℝ
  smooth_weights : ∀ a, ContDiffOn ℝ ∞ (weights a) neighborhood
  invariant_weights : ∀ a (π : Equiv.Perm (Fin N)) x, weights a (π • x) = weights a x
  support_weights : ∀ a, tsupport (weights a) ⊆
    ⋃ π : Equiv.Perm (Fin N), (fun x : Configuration N => π • x) ⁻¹'
      Metric.ball (a.val : Configuration N) (radius a.val)
  compact_weights : ∀ a, HasCompactSupport (weights a)
  square_weights : ∀ x ∈ neighborhood, ∑ a, weights a x ^ 2 = 1
  flat_weights : ∀ x ∈ neighborhood, ∀ v,
    ∑ a, weights a x * fderiv ℝ (weights a) x v = 0
  derivativeConstant : ℝ
  derivativeConstant_nonneg : 0 ≤ derivativeConstant
  derivative_bound : ∀ x ∈ centeredSphere N,
    (∑ a, ‖fderiv ℝ (weights a) x‖ ^ 2) ≤ derivativeConstant

/-- Existence of the actual finite permutation-invariant smooth atlas in Step 1. -/
theorem centeredAtlas_exists (N : ℕ) : Nonempty (CenteredAtlas N) := by
  classical
  choose r hr hsep using fun c : centeredSphere N =>
    finite_orbit_balls (fun π : Equiv.Perm (Fin N) => π • (c : Configuration N))
  let U : centeredSphere N → Set (Configuration N) := fun c => Metric.ball c (r c)
  have hU (c : centeredSphere N) : U c ∈ 𝓝 (c : Configuration N) :=
    Metric.ball_mem_nhds (c : Configuration N) (hr c)
  obtain ⟨s, Ω, χ, A, hΩ, hKΩ, hΩinv, hχsmooth, hχinv, hχsupp, hχcompact,
      hχsq, hχflat, hA, hχbound⟩ :=
    SmoothPartition.exists_invariant_square_partition
      (G := Equiv.Perm (Fin N)) permutation_contDiff
      (centeredSphere_compact N) U hU
  exact ⟨{
    radius := r
    radius_pos := hr
    orbit_separated := hsep
    charts := s
    neighborhood := Ω
    isOpen_neighborhood := hΩ
    sphere_subset := hKΩ
    invariant_neighborhood := hΩinv
    weights := χ
    smooth_weights := hχsmooth
    invariant_weights := hχinv
    support_weights := hχsupp
    compact_weights := hχcompact
    square_weights := hχsq
    flat_weights := hχflat
    derivativeConstant := A
    derivativeConstant_nonneg := hA
    derivative_bound := hχbound }⟩

/-- Choose the atlas once for each particle number. -/
def centeredAtlas (N : ℕ) : CenteredAtlas N := (centeredAtlas_exists N).some

namespace CenteredAtlas
variable {N : ℕ} (A : CenteredAtlas N)

/-- Physical chart obtained by taking the inverse image under the normalized shape. -/
def chartDomain (a : A.charts) : Set (Configuration N) :=
  distinctConfigurations N ∩ (normalizedCenter N) ⁻¹'
    Metric.ball (a.val : Configuration N) (A.radius a.val)

theorem chartDomain_isOpen (hN : 2 ≤ N) (a : A.charts) : IsOpen (A.chartDomain a) := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  have hc : ContinuousAt (normalizedCenter N) y :=
    (Normalization.radial_contDiffAt (center N) (center_ne_zero_of_distinct hN hy.1)).continuousAt
  exact Filter.inter_mem ((distinctConfigurations_isOpen N).mem_nhds hy.1)
    (hc.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds hy.2))

/-- Overlapping physical branches differ by a stabilizer permutation of the center. -/
theorem chartDomain_separated (a : A.charts) (π σ : Equiv.Perm (Fin N))
    (y : Configuration N)
    (hπ : permuteConfiguration π⁻¹ y ∈ A.chartDomain a)
    (hσ : permuteConfiguration σ⁻¹ y ∈ A.chartDomain a) :
    permuteConfiguration (π⁻¹ * σ) (a.val : Configuration N) = a.val := by
  have hball (τ : Equiv.Perm (Fin N))
      (hτ : permuteConfiguration τ⁻¹ y ∈ A.chartDomain a) :
      normalizedCenter N y ∈ Metric.ball (τ • (a.val : Configuration N)) (A.radius a.val) := by
    have hd := (permuteConfiguration τ).isometry.dist_eq
      (normalizedCenter N (permuteConfiguration τ⁻¹ y)) (a.val : Configuration N)
    rw [normalizedCenter_permute, ← permuteConfiguration_mul, mul_inv_cancel,
      permuteConfiguration_one] at hd
    change dist (normalizedCenter N y) (τ • (a.val : Configuration N)) < _
    rw [permutation_smul_eq, hd]
    simpa only [Set.mem_preimage, normalizedCenter_permute, Metric.mem_ball] using hτ.2
  rcases A.orbit_separated a.val π σ with he | hd
  · have hh := congrArg (permuteConfiguration π⁻¹) he
    simp only [permutation_smul_eq, ← permuteConfiguration_mul, inv_mul_cancel,
      permuteConfiguration_one] at hh
    exact hh.symm
  · exact False.elim (Set.disjoint_left.mp hd (hball π hπ) (hball σ hσ))

/-- Pull back the constructed weights to the distinct configurations. -/
def configurationWeights (a : A.charts) (x : Configuration N) : ℝ :=
  A.weights a (normalizedCenter N x)

/-- Support of the pulled-back weight stays in the orbit of its physical chart.
This is a topological-support assertion, so it controls chart boundary points. -/
theorem configurationWeights_support (hN : 2 ≤ N) (a : A.charts) :
    tsupport (A.configurationWeights a) ∩ distinctConfigurations N ⊆
      {y | ∃ π : Equiv.Perm (Fin N), permuteConfiguration π y ∈ A.chartDomain a} := by
  intro y hy
  have hc : ContinuousAt (normalizedCenter N) y :=
    (Normalization.radial_contDiffAt (center N) (center_ne_zero_of_distinct hN hy.2)).continuousAt
  have hs : normalizedCenter N y ∈ tsupport (A.weights a) := by
    by_contra hs
    have hz := notMem_tsupport_iff_eventuallyEq.mp hs
    have hzero : A.configurationWeights a =ᶠ[𝓝 y] 0 := hc.eventually hz
    exact (notMem_tsupport_iff_eventuallyEq.mpr hzero) hy.1
  obtain ⟨π, hπ⟩ := Set.mem_iUnion.mp (A.support_weights a hs)
  refine ⟨π, (distinctConfigurations_permute_iff π y).mpr hy.2, ?_⟩
  simpa only [Set.mem_preimage, permutation_smul_eq, normalizedCenter_permute] using hπ

theorem configurationWeights_square (hN : 2 ≤ N) {x : Configuration N}
    (hx : x ∈ distinctConfigurations N) :
    ∑ a, A.configurationWeights a x ^ 2 = 1 :=
  A.square_weights _ (A.sphere_subset (normalizedCenter_mem_sphere (by omega)
    (center_ne_zero_of_distinct hN hx)))

theorem configurationWeights_invariant (a : A.charts) (π : Equiv.Perm (Fin N))
    (x : Configuration N) :
    A.configurationWeights a (π • x) = A.configurationWeights a x := by
  simp only [configurationWeights, permutation_smul_eq, normalizedCenter_permute]
  exact A.invariant_weights a π (normalizedCenter N x)

theorem configurationWeights_smooth (hN : 2 ≤ N) (a : A.charts) :
    ContDiffOn ℝ ∞ (A.configurationWeights a) (distinctConfigurations N) := by
  apply (A.smooth_weights a).comp (normalizedCenter_smooth_distinct hN)
  intro x hx
  exact A.sphere_subset (normalizedCenter_mem_sphere (by omega)
    (center_ne_zero_of_distinct hN hx))

theorem configurationWeights_flat (hN : 2 ≤ N) {x : Configuration N}
    (hx : x ∈ distinctConfigurations N) (v : Configuration N) :
    ∑ a, A.configurationWeights a x * fderiv ℝ (A.configurationWeights a) x v = 0 := by
  have hcenter := center_ne_zero_of_distinct hN hx
  have hsphere := normalizedCenter_mem_sphere (by omega : 0 < N) hcenter
  have hmem := A.sphere_subset hsphere
  have hd (a : A.charts) : DifferentiableAt ℝ (A.weights a) (normalizedCenter N x) :=
    ((A.smooth_weights a).contDiffAt (A.isOpen_neighborhood.mem_nhds hmem)).differentiableAt
      (by simp)
  have hs : DifferentiableAt ℝ (normalizedCenter N) x :=
    (Normalization.radial_hasFDerivAt (center N) hcenter).differentiableAt
  change (∑ a, A.weights a (normalizedCenter N x) *
    fderiv ℝ (A.weights a ∘ normalizedCenter N) x v) = 0
  simp_rw [fderiv_comp x (hd _) hs, ContinuousLinearMap.comp_apply]
  exact A.flat_weights _ hmem _

/-- The actual inverse-square radial derivative estimate for these weights. -/
theorem configurationWeights_derivative_bound (hN : 2 ≤ N) {x : Configuration N}
    (hx : x ∈ distinctConfigurations N) :
    (∑ a, ‖fderiv ℝ (A.configurationWeights a) x‖ ^ 2) ≤
      (4 * A.derivativeConstant * ‖center N‖ ^ 2) / ‖center N x‖ ^ 2 := by
  have hcenter := center_ne_zero_of_distinct hN hx
  have hsphere := normalizedCenter_mem_sphere (by omega : 0 < N) hcenter
  have hmem := A.sphere_subset hsphere
  exact Normalization.partition_radial_bound A.weights (center N) hcenter
    (fun a => ((A.smooth_weights a).contDiffAt
      (A.isOpen_neighborhood.mem_nhds hmem)).differentiableAt (by simp))
    (A.derivative_bound _ hsphere)

end CenteredAtlas

end GptLean.SymmetricLift
