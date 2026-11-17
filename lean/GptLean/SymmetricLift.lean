import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
The symmetric-tensor appendix, `lem-flat-symmetric-isometries` and
`lem-symmetric-tensor-lift`.

This file constructs the finite Hilbert direct-sum map used in Step 3 and
proves its isometry, fixed-subspace and flatness properties from local chart
data. It also proves the exact metric formula used in Step 4. The smooth
equivariant atlas, its partition of unity, the inductive tensor-product
local maps, and the Sobolev extension across collision diagonals are not
constructed here. Their precise pointwise inputs remain hypotheses.

The final composition lemmas `connection_eq`, `metric_eq`, `lift_constant`
and `fermionic_repair_constant` are adapted from
`claude_lean/QEDFT/Repair/TensorLift.lean`. The direct-sum construction and
its gluing and induction estimates are new in this module.
-/

noncomputable section

namespace GptLean.SymmetricLift

open ComplexConjugate WithLp
open scoped BigOperators

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
variable {ι : Type*} [Fintype ι]

/-- The orthogonal Hilbert sum of the fixed part and the local chart targets. -/
abbrev GlueTarget (H K ι : Type*) := WithLp 2 (H × PiLp 2 (fun _ : ι => K))

/-- Step 3, with `P` the symmetric projection and real partition weights. -/
def glue (P : H →ₗ[ℂ] H) (χ : ι → ℝ) (V : ι → H →ₗ[ℂ] K) (x : H) :
    GlueTarget H K ι :=
  toLp 2 (P x, toLp 2 (fun a => (χ a : ℂ) • V a (x - P x)))

/-- The glued map is a complex-linear map, before imposing the metric conditions. -/
def glueLinear (P : H →ₗ[ℂ] H) (χ : ι → ℝ) (V : ι → H →ₗ[ℂ] K) :
    H →ₗ[ℂ] GlueTarget H K ι where
  toFun := glue P χ V
  map_add' x y := by
    apply (WithLp.ext_iff 2).mpr
    apply Prod.ext
    · exact P.map_add x y
    · apply (WithLp.ext_iff 2).mpr
      funext a
      simp [glue, add_sub_add_comm, smul_add]
  map_smul' c x := by
    apply (WithLp.ext_iff 2).mpr
    apply Prod.ext
    · exact P.map_smul c x
    · apply (WithLp.ext_iff 2).mpr
      funext a
      change (χ a : ℂ) • V a (c • x - P (c • x)) =
        c • ((χ a : ℂ) • V a (x - P x))
      rw [P.map_smul, ← smul_sub, (V a).map_smul]
      exact smul_comm _ _ _

/-- The value of one derivative, with the local product rule made explicit. -/
def glueDerivative (P : H →ₗ[ℂ] H) (χ dχ : ι → ℝ)
    (V dV : ι → H →ₗ[ℂ] K) (x : H) : GlueTarget H K ι :=
  toLp 2 (0, toLp 2 (fun a =>
    (dχ a : ℂ) • V a (x - P x) + (χ a : ℂ) • dV a (x - P x)))

/-- The standard orthogonal-projection decomposition, using only orthogonality. -/
theorem projection_split_inner (P : H →ₗ[ℂ] H)
    (horth : ∀ x y, inner ℂ (P x) (y - P y) = 0) (x y : H) :
    inner ℂ (P x) (P y) + inner ℂ (x - P x) (y - P y) = inner ℂ x y := by
  have hreverse : inner ℂ (x - P x) (P y) = 0 := by
    rw [← inner_conj_symm, horth, map_zero]
  have hx : P x + (x - P x) = x := by abel
  have hy : P y + (y - P y) = y := by abel
  conv_rhs => rw [← hx, ← hy]
  simp only [inner_add_left, inner_add_right, horth, hreverse, add_zero, zero_add]

/-- Gluing isometries with a real square partition preserves the inner product. -/
theorem glue_inner (P : H →ₗ[ℂ] H) (χ : ι → ℝ) (V : ι → H →ₗ[ℂ] K)
    (horth : ∀ x y, inner ℂ (P x) (y - P y) = 0)
    (hpartition : ∑ a, χ a ^ 2 = 1)
    (hiso : ∀ a x y, inner ℂ (V a x) (V a y) = inner ℂ x y) (x y : H) :
    inner ℂ (glue P χ V x) (glue P χ V y) = inner ℂ x y := by
  have hc : ∑ a, (χ a : ℂ) ^ 2 = 1 := by exact_mod_cast hpartition
  simp only [glue, WithLp.prod_inner_apply, PiLp.inner_apply,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal, hiso]
  simp_rw [← mul_assoc, ← pow_two]
  rw [← Finset.sum_mul, hc, one_mul]
  exact projection_split_inner P horth x y

theorem glue_norm (P : H →ₗ[ℂ] H) (χ : ι → ℝ) (V : ι → H →ₗ[ℂ] K)
    (horth : ∀ x y, inner ℂ (P x) (y - P y) = 0)
    (hpartition : ∑ a, χ a ^ 2 = 1)
    (hiso : ∀ a x y, inner ℂ (V a x) (V a y) = inner ℂ x y) (x : H) :
    ‖glue P χ V x‖ = ‖x‖ := by
  have h : ‖glue P χ V x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ),
      glue_inner P χ V horth hpartition hiso]
  nlinarith [norm_nonneg (glue P χ V x), norm_nonneg x]

/-- A genuine linear isometry constructed from the finite local gluing data. -/
def glueIsometry (P : H →ₗ[ℂ] H) (χ : ι → ℝ) (V : ι → H →ₗ[ℂ] K)
    (horth : ∀ x y, inner ℂ (P x) (y - P y) = 0)
    (hpartition : ∑ a, χ a ^ 2 = 1)
    (hiso : ∀ a x y, inner ℂ (V a x) (V a y) = inner ℂ x y) :
    H →ₗᵢ[ℂ] GlueTarget H K ι where
  toLinearMap := glueLinear P χ V
  norm_map' := glue_norm P χ V horth hpartition hiso

omit [Fintype ι] in
/-- The entire symmetric subspace is embedded independently of the local maps. -/
theorem glue_fixed (P : H →ₗ[ℂ] H) (χ : ι → ℝ) (V : ι → H →ₗ[ℂ] K)
    (hP : ∀ x, P (P x) = P x) (x : H) :
    glue P χ V (P x) = toLp 2 (P x, (0 : PiLp 2 (fun _ : ι => K))) := by
  simp [glue, hP]
  rfl

omit [Fintype ι] in
theorem glueDerivative_fixed (P : H →ₗ[ℂ] H) (χ dχ : ι → ℝ)
    (V dV : ι → H →ₗ[ℂ] K) (hP : ∀ x, P (P x) = P x) (x : H) :
    glueDerivative P χ dχ V dV (P x) = 0 := by
  simp [glueDerivative, hP]
  rfl

/-- Flat local maps and the differentiated square partition give a flat glued map. -/
theorem glue_flat (P : H →ₗ[ℂ] H) (χ dχ : ι → ℝ)
    (V dV : ι → H →ₗ[ℂ] K)
    (hpartition : ∑ a, χ a * dχ a = 0)
    (hiso : ∀ a x y, inner ℂ (V a x) (V a y) = inner ℂ x y)
    (hflat : ∀ a x y, inner ℂ (V a x) (dV a y) = 0) (x y : H) :
    inner ℂ (glue P χ V x) (glueDerivative P χ dχ V dV y) = 0 := by
  have hc : ∑ a, (χ a : ℂ) * (dχ a : ℂ) = 0 := by exact_mod_cast hpartition
  simp only [glue, glueDerivative, WithLp.prod_inner_apply,
    inner_zero_right, zero_add, PiLp.inner_apply,
    inner_smul_left, inner_add_right, inner_smul_right, Complex.conj_ofReal,
    hiso, hflat, mul_zero, add_zero]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  rw [show (∑ a, (dχ a : ℂ) * (χ a : ℂ)) = 0 by simpa only [mul_comm] using hc]
  rw [zero_mul]

/-- If a chart map fixes the symmetric part, its derivative ignores that part. -/
theorem derivative_on_remainder (P : H →ₗ[ℂ] H) (dV : H →ₗ[ℂ] K)
    (hfixed : ∀ x, dV (P x) = 0) (x : H) :
    dV (x - P x) = dV x := by simp [hfixed]

/-- The local cross term is exactly zero, without a loss in the constant. -/
theorem scaled_orthogonal_norm (a b : ℝ) (u v : K)
    (horth : inner ℂ u v = 0) :
    ‖(a : ℂ) • u + (b : ℂ) • v‖ ^ 2 = a ^ 2 * ‖u‖ ^ 2 + b ^ 2 * ‖v‖ ^ 2 := by
  have hcross : inner ℂ ((a : ℂ) • u) ((b : ℂ) • v) = 0 := by
    simp only [inner_smul_left, inner_smul_right, horth, mul_zero]
  rw [norm_add_sq (𝕜 := ℂ), hcross]
  simp [norm_smul, Real.norm_eq_abs, mul_pow]

/-- Step 4's exact derivative identity for one coordinate direction. -/
theorem glueDerivative_metric (P : H →ₗ[ℂ] H) (χ dχ : ι → ℝ)
    (V dV : ι → H →ₗ[ℂ] K)
    (hiso : ∀ a x, ‖V a x‖ = ‖x‖)
    (hflat : ∀ a x y, inner ℂ (V a x) (dV a y) = 0)
    (hfixed : ∀ a x, dV a (P x) = 0) (x : H) :
    ‖glueDerivative P χ dχ V dV x‖ ^ 2 =
      (∑ a, dχ a ^ 2) * ‖x - P x‖ ^ 2 + ∑ a, χ a ^ 2 * ‖dV a x‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp only [glueDerivative, WithLp.fst, WithLp.snd, ofLp_toLp, norm_zero,
    zero_pow (by decide : 2 ≠ 0), zero_add, PiLp.norm_sq_eq_of_L2]
  simp_rw [scaled_orthogonal_norm _ _ _ _ (hflat _ _ _), hiso,
    derivative_on_remainder P _ (hfixed _) x]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]

/-- The same formula summed over all particle-coordinate directions. -/
theorem glueDerivative_total_metric {δ : Type*} [Fintype δ]
    (P : H →ₗ[ℂ] H) (χ : ι → ℝ) (dχ : δ → ι → ℝ)
    (V : ι → H →ₗ[ℂ] K) (dV : δ → ι → H →ₗ[ℂ] K)
    (hiso : ∀ a x, ‖V a x‖ = ‖x‖)
    (hflat : ∀ d a x y, inner ℂ (V a x) (dV d a y) = 0)
    (hfixed : ∀ d a x, dV d a (P x) = 0) (x : H) :
    (∑ d, ‖glueDerivative P χ (dχ d) V (dV d) x‖ ^ 2) =
      (∑ d, ∑ a, dχ d a ^ 2) * ‖x - P x‖ ^ 2 +
        ∑ a, χ a ^ 2 * ∑ d, ‖dV d a x‖ ^ 2 := by
  simp_rw [glueDerivative_metric P χ _ V _ hiso (hflat _) (hfixed _) x]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum]

omit [Fintype ι] in
/-- Permutation absorption is preserved by the actual direct-sum construction. -/
theorem glue_equivariant (P R : H →ₗ[ℂ] H) (χ χ' : ι → ℝ)
    (V V' : ι → H →ₗ[ℂ] K) (hχ : χ' = χ)
    (hPR : ∀ x, P (R x) = P x) (hRP : ∀ x, R (P x) = P x)
    (hV : ∀ a x, V' a (R x) = V a x) (x : H) :
    glue P χ' V' (R x) = glue P χ V x := by
  subst χ'
  have hrem : R x - P x = R (x - P x) := by simp [hRP]
  simp only [glue, hPR, hrem, hV]

/-- The geometric remainder estimate takes the minimum of the two controls. -/
theorem remainder_min_bound {q rSq p LSq N R : ℝ}
    (hq : 0 ≤ q)
    (hrecip : q * rSq = 1) (hunit : R ≤ 1)
    (hnear : R ≤ N * rSq * LSq) (hpair : q ≤ N * p) :
    q * R ≤ N * min p LSq := by
  have hp : q * R ≤ N * p :=
    (mul_le_mul_of_nonneg_left hunit hq).trans (by simpa using hpair)
  have hl : q * R ≤ N * LSq := by
    calc
      q * R ≤ q * (N * rSq * LSq) := mul_le_mul_of_nonneg_left hnear hq
      _ = N * LSq := by calc
        q * (N * rSq * LSq) = N * (q * rSq) * LSq := by ring
        _ = N * LSq := by rw [hrecip, mul_one]
  rcases le_total p LSq with h | h
  · simpa only [min_eq_left h] using hp
  · simpa only [min_eq_right h] using hl

/-- Summing local estimates with a square partition loses no chart-count factor. -/
theorem weighted_local_bound (χ E : ι → ℝ) {B m : ℝ}
    (hpartition : ∑ a, χ a ^ 2 = 1) (hE : ∀ a, E a ≤ B * m) :
    (∑ a, χ a ^ 2 * E a) ≤ B * m := by
  calc
    (∑ a, χ a ^ 2 * E a) ≤ ∑ a, χ a ^ 2 * (B * m) :=
      Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hE a) (sq_nonneg _)
    _ = B * m := by rw [← Finset.sum_mul, hpartition, one_mul]

/-- Block pair sums are sub-sums of the full pair sum, so induction uses the same minimum. -/
theorem block_metric_bound (b pairBlock E : ι → ℝ) {pairTotal LSq : ℝ}
    (hb : ∀ j, 0 ≤ b j) (hp : ∀ j, pairBlock j ≤ pairTotal)
    (hE : ∀ j, E j ≤ b j * min (pairBlock j) LSq) :
    (∑ j, E j) ≤ (∑ j, b j) * min pairTotal LSq := by
  calc
    (∑ j, E j) ≤ ∑ j, b j * min pairTotal LSq := by
      apply Finset.sum_le_sum
      intro j _
      exact (hE j).trans (mul_le_mul_of_nonneg_left (min_le_min_right LSq (hp j)) (hb j))
    _ = (∑ j, b j) * min pairTotal LSq := (Finset.sum_mul _ _ _).symm

/-- Step 4's induction constant, with a uniform majorant on all block sums. -/
theorem induction_metric_bound (χ E : ι → ℝ) {A q R N B m : ℝ}
    (hA : 0 ≤ A) (hR : 0 ≤ R) (hpartition : ∑ a, χ a ^ 2 = 1)
    {partitionEnergy : ℝ} (hpartitionEnergy : partitionEnergy ≤ A * q)
    (hremainder : q * R ≤ N * m) (hE : ∀ a, E a ≤ B * m) :
    partitionEnergy * R + (∑ a, χ a ^ 2 * E a) ≤ (N * A + B) * m := by
  have h1 := mul_le_mul_of_nonneg_right hpartitionEnergy hR
  have h2 := mul_le_mul_of_nonneg_left hremainder hA
  have h3 := weighted_local_bound χ E hpartition hE
  nlinarith

/-- The normalized local bumps form a square partition. -/
theorem normalized_partition (f : ι → ℝ) {s : ℝ} (hs : s ≠ 0)
    (hsum : ∑ a, f a ^ 2 = s ^ 2) :
    ∑ a, (f a / s) ^ 2 = 1 := by
  simp_rw [div_pow]
  rw [← Finset.sum_div, hsum, div_self (pow_ne_zero _ hs)]

/-- Differentiating the normalization produces zero partition connection. -/
theorem normalized_partition_flat (f df : ι → ℝ) {s : ℝ} (hs : s ≠ 0)
    (hsum : ∑ a, f a ^ 2 = s ^ 2) :
    (∑ a, (f a / s) * (df a / s - f a * (∑ b, f b * df b) / s ^ 3)) = 0 := by
  have hterm (a : ι) :
      (f a / s) * (df a / s - f a * (∑ b, f b * df b) / s ^ 3) =
        (f a * df a) / s ^ 2 - f a ^ 2 * (∑ b, f b * df b) / s ^ 4 := by
    field_simp
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div,
    ← Finset.sum_mul, hsum]
  field_simp
  ring

/-- Composition with a flat isometry preserves the tensor connection.
Adapted from `QEDFT.TensorLift.connection_eq`. -/
theorem connection_eq (U U' : H →ₗ[ℂ] K) (T T' : H)
    (hiso : ∀ x y, inner ℂ (U x) (U y) = inner ℂ x y)
    (hflat : ∀ x y, inner ℂ (U x) (U' y) = 0) :
    inner ℂ (U T) (U' T + U T') = inner ℂ T T' := by
  rw [inner_add_right, hflat, hiso, zero_add]

/-- The two derivative terms are orthogonal.
Adapted from `QEDFT.TensorLift.metric_eq`. -/
theorem metric_eq (U U' : H →ₗ[ℂ] K) (T T' : H)
    (hiso : ∀ x y, inner ℂ (U x) (U y) = inner ℂ x y)
    (hflat : ∀ x y, inner ℂ (U x) (U' y) = 0) :
    ‖U' T + U T'‖ ^ 2 = ‖T'‖ ^ 2 + ‖U' T‖ ^ 2 := by
  have hcross : inner ℂ (U' T) (U T') = 0 := by
    rw [← inner_conj_symm, hflat, map_zero]
  have hU : ‖U T'‖ ^ 2 = ‖T'‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), hiso]
  rw [norm_add_sq (𝕜 := ℂ), hcross, hU]
  simp only [map_zero, mul_zero, add_zero]
  ring

/-- The Lipschitz constant `C_N = N + b_N`.
Adapted from `QEDFT.TensorLift.lift_constant`. -/
theorem lift_constant {n b ℓ t u : ℝ} (ht : t ≤ n * ℓ ^ 2) (hu : u ≤ b * ℓ ^ 2) :
    t + u ≤ (n + b) * ℓ ^ 2 := by linarith

/-- The repair constant derived from the symmetric lift.
Adapted from `QEDFT.TensorLift.fermionic_repair_constant`. -/
theorem fermionic_repair_constant {C V M g S : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hg : g ≤ 36 * V ^ 2 + 2 * M) (hS : S ≤ C * g) :
    1 / 2 * S ≤ 18 * C * (V ^ 2 + M) := by
  have h1 := mul_le_mul_of_nonneg_left hg hC
  have h2 : 0 ≤ C * M := mul_nonneg hC hM
  nlinarith

end GptLean.SymmetricLift
