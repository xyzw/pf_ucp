import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
A smooth square partition for the tensor-lift atlas. Compactness first selects
finitely many genuine smooth compactly supported bumps. Summing their translates
under a finite group makes them invariant. Normalization is smooth on an open
neighborhood of the covered compact set. The differentiated partition identity
uses actual Fréchet derivatives.
-/

noncomputable section
open Set Filter
open scoped BigOperators Topology ContDiff
namespace GptLean.SymmetricLift.SmoothPartition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Compactness turns arbitrary neighborhood charts into a finite smooth bump cover. -/
theorem exists_finite_bump_cover [FiniteDimensional ℝ E]
    {K : Set E} (hK : IsCompact K) (U : K → Set E)
    (hU : ∀ x : K, U x ∈ 𝓝 (x : E)) :
    ∃ (s : Finset K) (f : K → E → ℝ),
      (∀ a, tsupport (f a) ⊆ U a ∧ HasCompactSupport (f a) ∧
        ContDiff ℝ ∞ (f a) ∧ ∀ x, 0 ≤ f a x) ∧
      ∀ x ∈ K, ∃ a ∈ s, 0 < f a x := by
  classical
  choose f hf using fun a : K =>
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (hU a)
  have hopen : ∀ a : K, IsOpen {x : E | 0 < f a x} := fun a =>
    isOpen_lt continuous_const (hf a).2.2.1.continuous
  have hcover : K ⊆ ⋃ a : K, {x : E | 0 < f a x} := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, by
      change 0 < f ⟨x, hx⟩ (↑(⟨x, hx⟩ : K) : E)
      rw [(hf ⟨x, hx⟩).2.2.2.2]
      exact zero_lt_one⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover _ hopen hcover
  refine ⟨s, f, ?_, ?_⟩
  · intro a
    exact ⟨(hf a).1, (hf a).2.1, (hf a).2.2.1,
      fun x => ((hf a).2.2.2.1 (mem_range_self x)).1⟩
  · intro x hx
    simpa only [mem_iUnion, mem_setOf_eq, exists_prop] using hs hx

section Orbit
variable {G : Type*} [Group G] [Fintype G] [MulAction G E]

/-- The unnormalized invariant bump, with no stabilizer choices. -/
def orbitSum (f : E → ℝ) (x : E) : ℝ := ∑ g : G, f (g • x)

theorem orbitSum_invariant (f : E → ℝ) (g : G) (x : E) :
    orbitSum (G := G) f (g • x) = orbitSum (G := G) f x := by
  simp only [orbitSum, ← mul_smul]
  exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun _ => rfl)

theorem orbitSum_contDiff (f : E → ℝ) (hf : ContDiff ℝ ∞ f)
    (hact : ∀ g : G, ContDiff ℝ ∞ (fun x : E => g • x)) :
    ContDiff ℝ ∞ (orbitSum (G := G) f) := by
  exact ContDiff.sum fun g _ => hf.comp (hact g)

theorem orbitSum_nonneg (f : E → ℝ) (hf : ∀ x, 0 ≤ f x) (x : E) :
    0 ≤ orbitSum (G := G) f x := Finset.sum_nonneg fun g _ => hf _

theorem orbitSum_pos (f : E → ℝ) (hf : ∀ x, 0 ≤ f x) {x : E}
    (hx : 0 < f x) : 0 < orbitSum (G := G) f x := by
  apply hx.trans_le
  simpa only [one_smul, orbitSum] using
    (Finset.single_le_sum (fun g (_ : g ∈ Finset.univ) => hf (g • x))
      (Finset.mem_univ (1 : G)))

/-- Averaging enlarges support only to the union of the translated charts. -/
theorem orbitSum_support_subset (f : E → ℝ) (U : Set E)
    (hf : Function.support f ⊆ U) :
    Function.support (orbitSum (G := G) f) ⊆ ⋃ g : G, (fun x : E => g • x) ⁻¹' U := by
  intro x hx
  by_contra h
  have hz : ∀ g : G, f (g • x) = 0 := by
    intro g
    by_contra hn
    exact h (mem_iUnion.mpr ⟨g, hf hn⟩)
  exact hx (by simp [orbitSum, hz])

theorem orbitSum_tsupport_subset (f : E → ℝ) (U : Set E)
    (hf : tsupport f ⊆ U)
    (hact : ∀ g : G, Continuous (fun x : E => g • x)) :
    tsupport (orbitSum (G := G) f) ⊆ ⋃ g : G, (fun x : E => g • x) ⁻¹' U := by
  have hclosed : IsClosed (⋃ g : G, (fun x : E => g • x) ⁻¹' tsupport f) :=
    isClosed_iUnion_of_finite (fun g => isClosed_closure.preimage (hact g))
  have hs := closure_minimal
    (orbitSum_support_subset (G := G) f (tsupport f) (subset_tsupport f)) hclosed
  exact hs.trans (iUnion_mono fun _ => preimage_mono hf)

theorem orbitSum_hasCompactSupport (f : E → ℝ) (hf : HasCompactSupport f)
    (hact : ∀ g : G, Continuous (fun x : E => g • x)) :
    HasCompactSupport (orbitSum (G := G) f) := by
  letI : ContinuousConstSMul G E := ⟨hact⟩
  have hc (g : G) : HasCompactSupport (fun x : E => f (g • x)) :=
    hf.comp_homeomorph (Homeomorph.smul g)
  have heq : orbitSum (G := G) f = ∑ g : G, (fun x : E => f (g • x)) := by
    funext x
    simp [orbitSum]
  rw [heq]
  exact HasCompactSupport.finset_sum (s := Finset.univ) (fun g _ => hc g)

end Orbit

section Normalize
variable {ι : Type*} [Fintype ι]

def squareSum (f : ι → E → ℝ) (x : E) : ℝ := ∑ a, (f a x) ^ 2

def positiveSet (f : ι → E → ℝ) : Set E := {x | 0 < squareSum f x}

def normalize (f : ι → E → ℝ) (a : ι) (x : E) : ℝ :=
  f a x / Real.sqrt (squareSum f x)

theorem squareSum_contDiff (f : ι → E → ℝ) (hf : ∀ a, ContDiff ℝ ∞ (f a)) :
    ContDiff ℝ ∞ (squareSum f) := ContDiff.sum fun a _ => (hf a).pow 2

theorem positiveSet_isOpen (f : ι → E → ℝ) (hf : ∀ a, ContDiff ℝ ∞ (f a)) :
    IsOpen (positiveSet f) :=
  isOpen_lt continuous_const (squareSum_contDiff f hf).continuous

theorem mem_positiveSet (f : ι → E → ℝ) {x : E} (h : ∃ a, f a x ≠ 0) :
    x ∈ positiveSet f := by
  obtain ⟨a, ha⟩ := h
  exact (sq_pos_of_ne_zero ha).trans_le
    (Finset.single_le_sum (fun b (_ : b ∈ Finset.univ) => sq_nonneg (f b x))
      (Finset.mem_univ a))

theorem normalize_contDiffOn (f : ι → E → ℝ) (hf : ∀ a, ContDiff ℝ ∞ (f a))
    (a : ι) : ContDiffOn ℝ ∞ (normalize f a) (positiveSet f) := by
  apply (hf a).contDiffOn.div
    ((squareSum_contDiff f hf).contDiffOn.sqrt (fun x hx => ne_of_gt hx))
  exact fun x hx => ne_of_gt (Real.sqrt_pos.mpr hx)

theorem normalize_square_sum (f : ι → E → ℝ) {x : E} (hx : x ∈ positiveSet f) :
    (∑ a, normalize f a x ^ 2) = 1 := by
  simp only [normalize, div_pow, ← Finset.sum_div]
  rw [Real.sq_sqrt (le_of_lt hx)]
  exact div_self (ne_of_gt hx)

theorem normalize_support_subset (f : ι → E → ℝ) (a : ι) :
    Function.support (normalize f a) ⊆ Function.support (f a) := by
  intro x hx hzero
  exact hx (by simp [normalize, hzero])

/-- The connection identity comes from differentiating the square partition. -/
theorem square_partition_fderiv_zero (χ : ι → E → ℝ) {Ω : Set E}
    (hΩ : IsOpen Ω) (hχ : ∀ a, ContDiffOn ℝ ∞ (χ a) Ω)
    (hsq : ∀ x ∈ Ω, ∑ a, χ a x ^ 2 = 1) {x : E} (hx : x ∈ Ω) (v : E) :
    ∑ a, χ a x * fderiv ℝ (χ a) x v = 0 := by
  have hd (a : ι) : DifferentiableAt ℝ (χ a) x :=
    ((hχ a).contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)
  have heq : (fun y => ∑ a, χ a y ^ 2) =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) :=
    Filter.eventually_of_mem (hΩ.mem_nhds hx) (fun y hy => hsq y hy)
  have hzero : fderiv ℝ (fun y => ∑ a, χ a y ^ 2) x = 0 := by
    rw [heq.fderiv_eq]
    exact fderiv_const_apply (1 : ℝ)
  have hsum := (HasFDerivAt.fun_sum
    (fun a (_ : a ∈ Finset.univ) => (hd a).hasFDerivAt.pow 2)).fderiv
  rw [hzero] at hsum
  have hval := congrArg (fun L : E →L[ℝ] ℝ => L v) hsum
  simp only [ContinuousLinearMap.zero_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, Nat.reduceSub, pow_one, nsmul_eq_mul,
    Nat.cast_ofNat, smul_eq_mul] at hval
  have hfactor : (∑ a, 2 * χ a x * fderiv ℝ (χ a) x v) =
      2 * ∑ a, χ a x * fderiv ℝ (χ a) x v := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hfactor] at hval
  linarith

theorem normalize_fderiv_zero (f : ι → E → ℝ) (hf : ∀ a, ContDiff ℝ ∞ (f a))
    {x : E} (hx : x ∈ positiveSet f) (v : E) :
    ∑ a, normalize f a x * fderiv ℝ (normalize f a) x v = 0 :=
  square_partition_fderiv_zero (normalize f) (positiveSet_isOpen f hf)
    (normalize_contDiffOn f hf) (fun _ hx => normalize_square_sum f hx) hx v

/-- Smoothness gives a finite derivative constant on the compact centered sphere. -/
theorem exists_compact_derivative_bound (χ : ι → E → ℝ) {Ω K : Set E}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hχ : ∀ a, ContDiffOn ℝ ∞ (χ a) Ω) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x ∈ K, (∑ a, ‖fderiv ℝ (χ a) x‖ ^ 2) ≤ A := by
  have hc : ContinuousOn (fun x => ∑ a, ‖fderiv ℝ (χ a) x‖ ^ 2) K := by
    apply continuousOn_finset_sum
    intro a _
    exact (((hχ a).continuousOn_fderiv_of_isOpen hΩ (by simp)).norm.pow 2).mono hKΩ
  obtain ⟨A, hA⟩ := hK.bddAbove_image hc
  refine ⟨max A 0, le_max_right _ _, ?_⟩
  intro x hx
  exact (hA (mem_image_of_mem _ hx)).trans (le_max_left _ _)

/-- Pullback by the centered radial normalization transfers the compact
derivative bound. Substituting `L = C / r` gives the stated inverse-square
radial estimate without assuming derivatives of the partition as data. -/
theorem pullback_derivative_bound
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (χ : ι → E → ℝ) (s : F → E) {x : F} {A L : ℝ}
    (hχ : ∀ a, DifferentiableAt ℝ (χ a) (s x))
    (hs : DifferentiableAt ℝ s x) (hL : ‖fderiv ℝ s x‖ ≤ L)
    (hA : (∑ a, ‖fderiv ℝ (χ a) (s x)‖ ^ 2) ≤ A) :
    (∑ a, ‖fderiv ℝ (χ a ∘ s) x‖ ^ 2) ≤ A * L ^ 2 := by
  have hL0 : 0 ≤ L := (norm_nonneg _).trans hL
  calc
    (∑ a, ‖fderiv ℝ (χ a ∘ s) x‖ ^ 2) ≤
        ∑ a, ‖fderiv ℝ (χ a) (s x)‖ ^ 2 * L ^ 2 := by
      apply Finset.sum_le_sum
      intro a _
      rw [fderiv_comp x (hχ a) hs]
      have hb : ‖(fderiv ℝ (χ a) (s x)).comp (fderiv ℝ s x)‖ ≤
          ‖fderiv ℝ (χ a) (s x)‖ * L :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left hL (norm_nonneg _))
      calc
        _ ≤ (‖fderiv ℝ (χ a) (s x)‖ * L) ^ 2 :=
          (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) hL0)).mpr hb
        _ = _ := mul_pow _ _ _
    _ = (∑ a, ‖fderiv ℝ (χ a) (s x)‖ ^ 2) * L ^ 2 :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ A * L ^ 2 := mul_le_mul_of_nonneg_right hA (sq_nonneg L)

end Normalize

/-- Complete construction of the invariant smooth square partition used by Step 1.
The input consists of neighborhood charts, not of a pre-existing partition.
The partition is smooth on an explicitly constructed invariant open neighborhood
of the compact set and has controlled topological support and derivatives. -/
theorem exists_invariant_square_partition [FiniteDimensional ℝ E]
    {G : Type*} [Group G] [Fintype G] [MulAction G E]
    (hact : ∀ g : G, ContDiff ℝ ∞ (fun x : E => g • x))
    {K : Set E} (hK : IsCompact K) (U : K → Set E)
    (hU : ∀ x : K, U x ∈ 𝓝 (x : E)) :
    ∃ (s : Finset K) (Ω : Set E) (χ : s → E → ℝ) (A : ℝ),
      IsOpen Ω ∧ K ⊆ Ω ∧
      (∀ (g : G) x, g • x ∈ Ω ↔ x ∈ Ω) ∧
      (∀ a, ContDiffOn ℝ ∞ (χ a) Ω) ∧
      (∀ a (g : G) x, χ a (g • x) = χ a x) ∧
      (∀ a, tsupport (χ a) ⊆ ⋃ g : G, (fun x : E => g • x) ⁻¹' U a.val) ∧
      (∀ a, HasCompactSupport (χ a)) ∧
      (∀ x ∈ Ω, ∑ a, χ a x ^ 2 = 1) ∧
      (∀ x ∈ Ω, ∀ v, ∑ a, χ a x * fderiv ℝ (χ a) x v = 0) ∧
      0 ≤ A ∧ ∀ x ∈ K, (∑ a, ‖fderiv ℝ (χ a) x‖ ^ 2) ≤ A := by
  classical
  obtain ⟨s, f, hf, hcover⟩ := exists_finite_bump_cover hK U hU
  let F : s → E → ℝ := fun a => orbitSum (G := G) (f a.val)
  have hF (a : s) : ContDiff ℝ ∞ (F a) :=
    orbitSum_contDiff (f a.val) (hf a.val).2.2.1 hact
  have hFK : K ⊆ positiveSet F := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := hcover x hx
    apply mem_positiveSet F
    exact ⟨⟨a, ha⟩, ne_of_gt (orbitSum_pos (f a) (hf a).2.2.2 hax)⟩
  have hinv (a : s) (g : G) (x : E) : F a (g • x) = F a x :=
    orbitSum_invariant (f a.val) g x
  have hΩ := positiveSet_isOpen F hF
  have hχ := normalize_contDiffOn F hF
  obtain ⟨A, hA, hbound⟩ := exists_compact_derivative_bound (normalize F) hΩ hK hFK hχ
  refine ⟨s, positiveSet F, normalize F, A, hΩ, hFK, ?_, hχ, ?_, ?_, ?_,
    (fun _ hx => normalize_square_sum F hx),
    (fun _ hx v => normalize_fderiv_zero F hF hx v), hA, hbound⟩
  · intro g x
    simp only [positiveSet, mem_setOf_eq, squareSum, hinv]
  · intro a g x
    simp only [normalize, squareSum, hinv]
  · intro a
    exact (closure_mono (normalize_support_subset F a)).trans
      (orbitSum_tsupport_subset (f a.val) (U a.val) (hf a.val).1
        (fun g => (hact g).continuous))
  · intro a
    exact (orbitSum_hasCompactSupport (f a.val) (hf a.val).2.1
      (fun g => (hact g).continuous)).mono (normalize_support_subset F a)

end GptLean.SymmetricLift.SmoothPartition
