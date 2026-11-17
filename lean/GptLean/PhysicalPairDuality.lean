import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.HahnBanach
import GptLean.PhysicalPairSpace
import GptLean.DFT

/-!
Integral duality for the density and current intersection spaces.  The
measure-theoretic part below is independent of the physical state model.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace GptLean.PhysicalPairDuality

section IntegralPairing

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {μ : Measure α}
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q]

/-- The actual integral pairing of conjugate real Hilbert-valued Lp spaces. -/
def lpInner : Lp E p μ →L[ℝ] Lp E q μ →L[ℝ] ℝ :=
  (innerSL ℝ (E := E)).lpPairing μ p q

theorem lpInner_eq_integral (u : Lp E p μ) (f : Lp E q μ) :
    lpInner u f = ∫ x, inner ℝ (u x) (f x) ∂μ :=
  (innerSL ℝ (E := E)).lpPairing_eq_integral u f

theorem norm_lpInner_le (u : Lp E p μ) (f : Lp E q μ) :
    ‖lpInner u f‖ ≤ ‖u‖ * ‖f‖ := by
  have heq : lpInner u f = L1.integral ((innerSL ℝ (E := E)).holder 1 u f) := by
    rw [lpInner_eq_integral, L1.integral_eq_integral]
    exact integral_congr_ae ((innerSL ℝ (E := E)).coeFn_holder u f).symm
  rw [heq]
  apply (L1.norm_integral_le _).trans
  apply ((innerSL ℝ (E := E)).norm_holder_apply_apply_le u f).trans
  calc
    ‖innerSL ℝ (E := E)‖ * ‖u‖ * ‖f‖ ≤ 1 * ‖u‖ * ‖f‖ := by
      gcongr
      exact norm_innerSL_le ℝ
    _ = ‖u‖ * ‖f‖ := by ring

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] in
theorem integrable_inner (u : Lp E p μ) (f : Lp E q μ) :
    Integrable (fun x => inner ℝ (u x) (f x)) μ :=
  memLp_one_iff_integrable.mp
    ((innerSL ℝ (E := E)).memLp_of_bilin 1 (Lp.memLp u) (Lp.memLp f))

end IntegralPairing

section BoundedSeparation

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {μ : Measure α}

private theorem normalized_norm_le (v : E) : ‖(‖v‖⁻¹ : ℝ) • v‖ ≤ 1 := by
  by_cases hv : v = 0
  · simp [hv]
  · simp [norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

private theorem normalized_inner (v : E) :
    inner ℝ ((‖v‖⁻¹ : ℝ) • v) v = ‖v‖ := by
  by_cases hv : v = 0
  · simp [hv]
  · rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp

/-- A measurable bounded polar test detects the full L1 norm. -/
def normingTest (f : Lp E 1 μ) : Lp E ∞ μ :=
  (memLp_top_of_bound ((Lp.aestronglyMeasurable f).norm.inv₀.smul
    (Lp.aestronglyMeasurable f)) 1
    (Filter.Eventually.of_forall fun x => normalized_norm_le (f x))).toLp
      (fun x => (‖f x‖⁻¹ : ℝ) • f x)

theorem normingTest_ae (f : Lp E 1 μ) :
    (normingTest f : α → E) =ᵐ[μ] fun x => (‖f x‖⁻¹ : ℝ) • f x :=
  MemLp.coeFn_toLp _

theorem normingTest_pairing (f : Lp E 1 μ) :
    lpInner (normingTest f) f = ∫ x, ‖f x‖ ∂μ := by
  rw [lpInner_eq_integral]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (memLp_top_of_bound
    ((Lp.aestronglyMeasurable f).norm.inv₀.smul (Lp.aestronglyMeasurable f)) 1
    (Filter.Eventually.of_forall fun x => normalized_norm_le (f x)))] with x hx
  rw [show normingTest f x = (‖f x‖⁻¹ : ℝ) • f x from hx]
  exact normalized_inner (f x)

/-- Bounded measurable tests separate L1 functions, without a duality axiom. -/
theorem eq_zero_of_bounded_tests (f : Lp E 1 μ)
    (h : ∀ u : Lp E ∞ μ, lpInner u f = 0) : f = 0 := by
  have hn : ∫ x, ‖f x‖ ∂μ = 0 := by
    rw [← normingTest_pairing]
    exact h _
  have hzero : (fun x => ‖f x‖) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun _ => norm_nonneg _)
      (memLp_one_iff_integrable.mp (Lp.memLp f)).norm).mp hn
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [hzero] with x hx
  exact norm_eq_zero.mp hx

theorem eq_of_bounded_tests (f g : Lp E 1 μ)
    (h : ∀ u : Lp E ∞ μ, lpInner u f = lpInner u g) : f = g := by
  apply sub_eq_zero.mp
  apply eq_zero_of_bounded_tests
  intro u
  rw [map_sub, h u, sub_self]

/-- Bounded tests in an exhausting measurable family already separate L1.
Only almost-everywhere support is relevant to equivalence classes. -/
theorem eq_zero_of_bounded_supported_tests (f : Lp E 1 μ)
    (s : ℕ → Set α) (hs : ∀ n, MeasurableSet (s n)) (hcover : ⋃ n, s n = Set.univ)
    (h : ∀ n (u : Lp E ∞ μ),
      (∀ᵐ x ∂μ, x ∉ s n → u x = 0) → lpInner u f = 0) : f = 0 := by
  have hzero (n : ℕ) : ∀ᵐ x ∂μ.restrict (s n), f x = 0 := by
    let hm := (Lp.memLp (normingTest f)).indicator (hs n)
    let u : Lp E ∞ μ := hm.toLp ((s n).indicator (normingTest f))
    have hu : (u : α → E) =ᵐ[μ] (s n).indicator (normingTest f) :=
      MemLp.coeFn_toLp hm
    have hus : ∀ᵐ x ∂μ, x ∉ s n → u x = 0 := by
      filter_upwards [hu] with x hx hxs
      simpa only [Set.indicator_of_notMem hxs] using hx
    have heq : lpInner u f = ∫ x in s n, ‖f x‖ ∂μ := by
      rw [lpInner_eq_integral, ← integral_indicator (hs n)]
      apply integral_congr_ae
      filter_upwards [hu, normingTest_ae f] with x hx hn
      by_cases hxs : x ∈ s n
      · simp only [Set.indicator_of_mem hxs] at hx ⊢
        rw [hx, hn, normalized_inner]
      · simp only [Set.indicator_of_notMem hxs] at hx ⊢
        rw [hx, inner_zero_left]
    have hn : ∫ x in s n, ‖f x‖ ∂μ = 0 := heq.symm.trans (h n u hus)
    have hz := (integral_eq_zero_iff_of_nonneg (fun x => norm_nonneg (f x))
      (memLp_one_iff_integrable.mp (Lp.memLp f)).norm.integrableOn).mp hn
    filter_upwards [hz] with x hx
    exact norm_eq_zero.mp hx
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  have hall := (ae_restrict_iUnion_iff s (fun x => f x = 0)).mpr hzero
  simpa only [hcover, Measure.restrict_univ, Filter.EventuallyEq, Pi.zero_apply] using hall

theorem eq_of_bounded_supported_tests (f g : Lp E 1 μ)
    (s : ℕ → Set α) (hs : ∀ n, MeasurableSet (s n)) (hcover : ⋃ n, s n = Set.univ)
    (h : ∀ n (u : Lp E ∞ μ),
      (∀ᵐ x ∂μ, x ∉ s n → u x = 0) → lpInner u f = lpInner u g) : f = g := by
  apply sub_eq_zero.mp
  apply eq_zero_of_bounded_supported_tests (f - g) s hs hcover
  intro n u hu
  rw [map_sub, h n u hu, sub_self]

end BoundedSeparation

section SumClasses

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {q : ℝ≥0∞} {μ : Measure α}

/-- The sum of the two equivalence classes, in the space of measurable classes. -/
def sumLp : Lp E ∞ μ × Lp E q μ →ₗ[ℝ] (α →ₘ[μ] E) where
  toFun u := u.1.val + u.2.val
  map_add' u v := by
    change (u.1.val + v.1.val) + (u.2.val + v.2.val) =
      (u.1.val + u.2.val) + (v.1.val + v.2.val)
    abel
  map_smul' c u := by
    change c • u.1.val + c • u.2.val = c • (u.1.val + u.2.val)
    exact (smul_add c u.1.val u.2.val).symm

/-- Actual L∞ + Lq potentials, with equal almost-everywhere sums identified. -/
abbrev LpSum (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (q : ℝ≥0∞) (μ : Measure α) :=
  LinearMap.range (sumLp (E := E) (q := q) (μ := μ))

def ofParts (a : Lp E ∞ μ) (b : Lp E q μ) : LpSum E q μ :=
  ⟨sumLp (a, b), ⟨(a, b), rfl⟩⟩

def parts (u : LpSum E q μ) : Lp E ∞ μ × Lp E q μ :=
  Classical.choose u.property

theorem parts_spec (u : LpSum E q μ) : sumLp (parts u) = u.val :=
  Classical.choose_spec u.property

theorem ofParts_eq_iff (a a' : Lp E ∞ μ) (b b' : Lp E q μ) :
    ofParts a b = ofParts a' b' ↔
      (fun x => a x + b x) =ᵐ[μ] (fun x => a' x + b' x) := by
  rw [Subtype.ext_iff]
  change a.val + b.val = a'.val + b'.val ↔ _
  rw [AEEqFun.ext_iff]
  exact ⟨fun h => (AEEqFun.coeFn_add a.val b.val).symm.trans
    (h.trans (AEEqFun.coeFn_add a'.val b'.val)),
    fun h => (AEEqFun.coeFn_add a.val b.val).trans
      (h.trans (AEEqFun.coeFn_add a'.val b'.val).symm)⟩

end SumClasses

section IntersectionPairing

open PhysicalPairSpace

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {μ : Measure α}
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate q p]

/-- A decomposition yields a continuous functional on the intersection. -/
def partsPairing (a : Lp E ∞ μ) (b : Lp E q μ) :
    LpIntersection E 1 p μ →L[ℝ] ℝ :=
  (lpInner a).comp fst + (lpInner b).comp snd

theorem partsPairing_eq_integral (a : Lp E ∞ μ) (b : Lp E q μ)
    (f : LpIntersection E 1 p μ) :
    partsPairing a b f = ∫ x, inner ℝ (sumLp (a, b) x) (fst f x) ∂μ := by
  change lpInner a (fst f) + lpInner b (snd f) = _
  rw [lpInner_eq_integral, lpInner_eq_integral,
    ← integral_add (integrable_inner a (fst f)) (integrable_inner b (snd f))]
  apply integral_congr_ae
  filter_upwards [compatible f, AEEqFun.coeFn_add a.val b.val] with x hf hs
  change inner ℝ (a x) (fst f x) + inner ℝ (b x) (snd f x) =
    inner ℝ ((a.val + b.val) x) (fst f x)
  simp only [hs, Pi.add_apply, inner_add_left, hf]

theorem partsPairing_eq_of_sum_eq (a a' : Lp E ∞ μ) (b b' : Lp E q μ)
    (h : sumLp (a, b) = sumLp (a', b')) :
    partsPairing (p := p) a b = partsPairing a' b' := by
  ext f
  rw [partsPairing_eq_integral, partsPairing_eq_integral, h]

theorem norm_partsPairing_apply_le (a : Lp E ∞ μ) (b : Lp E q μ)
    (f : LpIntersection E 1 p μ) :
    ‖partsPairing a b f‖ ≤ (‖a‖ + ‖b‖) * ‖f‖ := by
  change ‖lpInner a (fst f) + lpInner b (snd f)‖ ≤ _
  calc
    _ ≤ ‖lpInner a (fst f)‖ + ‖lpInner b (snd f)‖ := norm_add_le _ _
    _ ≤ ‖a‖ * ‖fst f‖ + ‖b‖ * ‖snd f‖ :=
      add_le_add (norm_lpInner_le _ _) (norm_lpInner_le _ _)
    _ ≤ ‖a‖ * ‖f‖ + ‖b‖ * ‖f‖ := by
      gcongr
      · exact norm_fst_le f
      · exact norm_snd_le f
    _ = (‖a‖ + ‖b‖) * ‖f‖ := by ring

theorem norm_partsPairing_le (a : Lp E ∞ μ) (b : Lp E q μ) :
    ‖partsPairing (p := p) a b‖ ≤ ‖a‖ + ‖b‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (norm_partsPairing_apply_le a b)

/-- A potential class acts independently of its chosen L∞ + Lq decomposition. -/
def pairing (u : LpSum E q μ) : LpIntersection E 1 p μ →L[ℝ] ℝ :=
  partsPairing (parts u).1 (parts u).2

theorem pairing_eq_of_parts (u : LpSum E q μ) (a : Lp E ∞ μ) (b : Lp E q μ)
    (h : sumLp (a, b) = u.val) : pairing (p := p) u = partsPairing a b := by
  apply partsPairing_eq_of_sum_eq
  exact (parts_spec u).trans h.symm

@[simp] theorem pairing_ofParts (a : Lp E ∞ μ) (b : Lp E q μ) :
    pairing (p := p) (ofParts a b) = partsPairing a b :=
  pairing_eq_of_parts _ a b rfl

theorem pairing_eq_integral (u : LpSum E q μ) (f : LpIntersection E 1 p μ) :
    pairing u f = ∫ x, inner ℝ (u.val x) (fst f x) ∂μ := by
  unfold pairing
  rw [partsPairing_eq_integral]
  change (∫ x, inner ℝ (sumLp (parts u) x) (fst f x) ∂μ) = _
  rw [parts_spec]

theorem pairing_continuous (u : LpSum E q μ) :
    Continuous (pairing (p := p) u) := (pairing u).continuous

theorem norm_pairing_le_decomposition (u : LpSum E q μ)
    (a : Lp E ∞ μ) (b : Lp E q μ) (h : sumLp (a, b) = u.val) :
    ‖pairing (p := p) u‖ ≤ ‖a‖ + ‖b‖ := by
  rw [pairing_eq_of_parts u a b h]
  exact norm_partsPairing_le a b

/-- Bounded measurable potentials already separate the whole intersection. -/
theorem intersection_eq_of_bounded_tests (f g : LpIntersection E 1 p μ)
    (h : ∀ a : Lp E ∞ μ,
      pairing (p := p) (ofParts a (0 : Lp E q μ)) f =
      pairing (p := p) (ofParts a (0 : Lp E q μ)) g) : f = g := by
  apply fst_injective
  apply eq_of_bounded_tests
  intro a
  simpa [pairing_ofParts, partsPairing] using h a

end IntersectionPairing

section SumNorm

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {q : ℝ≥0∞} [Fact (1 ≤ q)] {μ : Measure α}

/-- The article's infimum over all L∞ + Lq decompositions. -/
def sumNorm (u : LpSum E q μ) : ℝ :=
  sInf {c : ℝ | ∃ a : Lp E ∞ μ, ∃ b : Lp E q μ,
    sumLp (a, b) = u.val ∧ c = ‖a‖ + ‖b‖}

theorem sumNorm_nonneg (u : LpSum E q μ) : 0 ≤ sumNorm u := by
  apply le_csInf
  · exact ⟨‖(parts u).1‖ + ‖(parts u).2‖, (parts u).1, (parts u).2, parts_spec u, rfl⟩
  · rintro c ⟨a, b, _, rfl⟩
    positivity

theorem sumNorm_le (u : LpSum E q μ) (a : Lp E ∞ μ) (b : Lp E q μ)
    (h : sumLp (a, b) = u.val) : sumNorm u ≤ ‖a‖ + ‖b‖ := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro c ⟨a', b', _, rfl⟩
    positivity
  · exact ⟨a, b, h, rfl⟩

theorem norm_pairing_le_sumNorm {p : ℝ≥0∞} [Fact (1 ≤ p)]
    [ENNReal.HolderConjugate q p] (u : LpSum E q μ) :
    ‖pairing (p := p) u‖ ≤ sumNorm u := by
  apply le_csInf
  · exact ⟨‖(parts u).1‖ + ‖(parts u).2‖, (parts u).1, (parts u).2, parts_spec u, rfl⟩
  · rintro c ⟨a, b, hab, rfl⟩
    exact norm_pairing_le_decomposition u a b hab

end SumNorm

section DualRepresentation

open PhysicalPairSpace

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {μ : Measure α}
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate q p]

/-- The standard representation theorem for one ordinary Lp space.
This universal measure-theoretic background is kept separate from the
intersection-space theorem and from all physical state data. -/
def LpDualRepresentation (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate q p] (μ : Measure α) : Prop :=
  Function.Surjective (lpInner (E := E) (p := q) (q := p) (μ := μ))

/-- Hahn–Banach proves the intersection-dual assertion from the two
ordinary Lp representation theorems. -/
theorem pairing_surjective
    (h1 : LpDualRepresentation E 1 ∞ μ)
    (hp : LpDualRepresentation E p q μ) :
    Function.Surjective (pairing (E := E) (p := p) (q := q) (μ := μ)) := by
  intro l
  obtain ⟨L, hL, _⟩ := exists_extension_norm_eq (compatibleSubmodule E 1 p μ) l
  obtain ⟨a, ha⟩ := h1 (L.comp (ContinuousLinearMap.inl ℝ (Lp E 1 μ) (Lp E p μ)))
  obtain ⟨b, hb⟩ := hp (L.comp (ContinuousLinearMap.inr ℝ (Lp E 1 μ) (Lp E p μ)))
  refine ⟨ofParts a b, ?_⟩
  ext f
  rw [pairing_ofParts]
  change lpInner a (fst f) + lpInner b (snd f) = l f
  rw [ha, hb]
  change L (fst f, 0) + L (0, snd f) = l f
  rw [← map_add]
  simpa only [Prod.mk_add_mk, add_zero, zero_add, fst_apply, snd_apply, Prod.eta] using hL f

end DualRepresentation

section Physical

open PhysicalPairSpace

instance holder_three_halves_three : ENNReal.HolderConjugate (3 / 2) 3 :=
  ⟨by
    rw [inv_one]
    rw [ENNReal.inv_div (Or.inl (by norm_num)) (Or.inl (by norm_num)), div_eq_mul_inv,
      two_mul]
    exact ENNReal.inv_three_add_inv_three⟩

/-- Scalar potentials L∞(R³) + L^(3/2)(R³). -/
abbrev ScalarPotential := LpSum ℝ (3 / 2) (volume : Measure Position)

/-- Vector potentials L∞(R³,R³) + L³(R³,R³). -/
abbrev VectorPotential := LpSum Vector 3 (volume : Measure Position)

abbrev Potential := ScalarPotential × VectorPotential

/-- The article's scalar-density plus vector-current dual pairing. -/
def pairPotential (u : Potential) : Pair →L[ℝ] ℝ :=
  (pairing u.1).comp (ContinuousLinearMap.fst ℝ Density Current) +
    (pairing u.2).comp (ContinuousLinearMap.snd ℝ Density Current)

theorem pairPotential_eq_integral (u : Potential) (f : Pair) :
    pairPotential u f =
      (∫ x, u.1.val x * densityL1 f x) +
      ∫ x, inner ℝ (u.2.val x) (currentL1 f x) := by
  change pairing u.1 f.1 + pairing u.2 f.2 = _
  rw [pairing_eq_integral, pairing_eq_integral]
  simp only [Real.inner_apply]
  rfl

theorem pairPotential_continuous (u : Potential) : Continuous (pairPotential u) :=
  (pairPotential u).continuous

theorem norm_pairPotential_apply_le (u : Potential) (f : Pair) :
    ‖pairPotential u f‖ ≤ (sumNorm u.1 + sumNorm u.2) * ‖f‖ := by
  change ‖pairing u.1 f.1 + pairing u.2 f.2‖ ≤ _
  calc
    _ ≤ ‖pairing u.1 f.1‖ + ‖pairing u.2 f.2‖ := norm_add_le _ _
    _ ≤ ‖pairing (p := 3) u.1‖ * ‖f.1‖ +
        ‖pairing (p := 3 / 2) u.2‖ * ‖f.2‖ :=
      add_le_add ((pairing (p := 3) u.1).le_opNorm _)
        ((pairing (p := 3 / 2) u.2).le_opNorm _)
    _ ≤ sumNorm u.1 * ‖f‖ + sumNorm u.2 * ‖f‖ := by
      apply add_le_add
      · exact mul_le_mul (norm_pairing_le_sumNorm (p := 3) u.1)
          (_root_.norm_fst_le f) (norm_nonneg f.1) (sumNorm_nonneg u.1)
      · exact mul_le_mul (norm_pairing_le_sumNorm (p := 3 / 2) u.2)
          (_root_.norm_snd_le f) (norm_nonneg f.2) (sumNorm_nonneg u.2)
    _ = (sumNorm u.1 + sumNorm u.2) * ‖f‖ := by ring

theorem norm_pairPotential_le (u : Potential) :
    ‖pairPotential u‖ ≤ sumNorm u.1 + sumNorm u.2 :=
  (pairPotential u).opNorm_le_bound (add_nonneg (sumNorm_nonneg _) (sumNorm_nonneg _))
    (norm_pairPotential_apply_le u)

/-- The actual article potentials separate physical density-current pairs. -/
theorem pair_eq_of_potentials (f g : Pair)
    (h : ∀ u : Potential, pairPotential u f = pairPotential u g) : f = g := by
  apply Prod.ext
  · apply intersection_eq_of_bounded_tests (q := 3 / 2)
    intro a
    simpa [pairPotential, pairing_ofParts, partsPairing] using
      h (ofParts a 0, ofParts 0 0)
  · apply intersection_eq_of_bounded_tests (q := 3)
    intro a
    simpa [pairPotential, pairing_ofParts, partsPairing] using
      h (ofParts 0 0, ofParts a 0)

/-- Bounded measurable tests with support in some finite-radius ball. -/
def BoundedBallTest (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :=
  {u : Lp E ∞ (volume : Measure Position) //
    ∃ n : ℕ, ∀ᵐ x ∂volume, x ∉ Metric.ball (0 : Position) (n + 1) → u x = 0}

abbrev Test := BoundedBallTest ℝ ⊕ BoundedBallTest Vector

def testPair : Test → Pair →L[ℝ] ℝ
  | Sum.inl t => (lpInner t.val).comp densityL1
  | Sum.inr t => (lpInner t.val).comp currentL1

theorem testPair_continuous (t : Test) : Continuous (testPair t) :=
  (testPair t).continuous

/-- The exact bounded, ball-supported test family used by localization
separates the density-current pair space in its article norm topology. -/
theorem pair_eq_of_bounded_ball_tests (f g : Pair)
    (h : ∀ t : Test, testPair t f = testPair t g) : f = g := by
  apply Prod.ext
  · apply fst_injective
    apply eq_of_bounded_supported_tests (fst f.1) (fst g.1)
      (fun n : ℕ => Metric.ball (0 : Position) (n + 1))
      (fun _ => measurableSet_ball) (Metric.iUnion_ball_nat_succ 0)
    intro n u hu
    exact h (Sum.inl ⟨u, n, hu⟩)
  · apply fst_injective
    apply eq_of_bounded_supported_tests (fst f.2) (fst g.2)
      (fun n : ℕ => Metric.ball (0 : Position) (n + 1))
      (fun _ => measurableSet_ball) (Metric.iUnion_ball_nat_succ 0)
    intro n u hu
    exact h (Sum.inr ⟨u, n, hu⟩)

/-- Every continuous functional on the article pair space is a physical
potential pairing, using only the four ordinary Lp representation theorems. -/
theorem pairPotential_surjective
    (hρ1 : LpDualRepresentation ℝ 1 ∞ (volume : Measure Position))
    (hρ3 : LpDualRepresentation ℝ 3 (3 / 2) (volume : Measure Position))
    (hj1 : LpDualRepresentation Vector 1 ∞ (volume : Measure Position))
    (hj32 : LpDualRepresentation Vector (3 / 2) 3 (volume : Measure Position)) :
    Function.Surjective pairPotential := by
  intro L
  obtain ⟨u, hu⟩ := pairing_surjective hρ1 hρ3
    (L.comp (ContinuousLinearMap.inl ℝ Density Current))
  obtain ⟨v, hv⟩ := pairing_surjective hj1 hj32
    (L.comp (ContinuousLinearMap.inr ℝ Density Current))
  refine ⟨(u, v), ?_⟩
  apply ContinuousLinearMap.ext
  intro f
  change pairing (p := 3) u f.1 + pairing (p := 3 / 2) v f.2 = L f
  have hu' := congrArg (fun F : Density →L[ℝ] ℝ => F f.1) hu
  have hv' := congrArg (fun F : Current →L[ℝ] ℝ => F f.2) hv
  change pairing (p := 3) u f.1 = L (f.1, 0) at hu'
  change pairing (p := 3 / 2) v f.2 = L (0, f.2) at hv'
  rw [hu', hv']
  rw [← map_add]
  simp only [Prod.mk_add_mk, zero_add, add_zero, Prod.eta]

end Physical

/-- Explicit standard Lp background on sigma-finite measure spaces, for
finite-dimensional real Hilbert values and exponents 1 ≤ p < ∞.  No
physical density, current, state, or constrained functional occurs here. -/
def StandardFiniteDimensionalLpRepresentation : Prop :=
  ∀ (α E : Type) [MeasurableSpace α] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (μ : Measure α) [SigmaFinite μ]
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate q p], p ≠ ∞ → LpDualRepresentation E p q μ

/-- Explicit universal real normed-space Fenchel–Moreau background. -/
def StandardDualFenchelMoreau : Prop :=
  ∀ (D : Type) [NormedAddCommGroup D] [NormedSpace ℝ D],
    DFT.FenchelMoreau (fun l : D →L[ℝ] ℝ => fun d => l d)

theorem pairPotential_surjective_of_standard
    (hLp : StandardFiniteDimensionalLpRepresentation) :
    Function.Surjective pairPotential := by
  apply pairPotential_surjective
  · exact hLp _ _ _ 1 ∞ (by norm_num)
  · exact hLp _ _ _ 3 (3 / 2) (by norm_num)
  · exact hLp _ _ _ 1 ∞ (by norm_num)
  · exact hLp _ _ _ (3 / 2) 3 (ENNReal.div_ne_top (by norm_num) (by norm_num))

/-- Fenchel–Moreau for the actual article potential class follows from
ordinary Lp representation, proved Hahn–Banach transport, and the
universal continuous-dual Fenchel–Moreau theorem. -/
theorem physical_fenchelMoreau
    (hLp : StandardFiniteDimensionalLpRepresentation)
    (hFM : StandardDualFenchelMoreau) :
    DFT.FenchelMoreau (fun u : Potential => fun f => pairPotential u f) := by
  intro f hbot hfinite hconv hlsc d
  calc
    f d = DFT.biconjugate
        (fun L : PhysicalPairSpace.Pair →L[ℝ] ℝ => fun x => L x) f d :=
      hFM PhysicalPairSpace.Pair f hbot hfinite hconv hlsc d
    _ = DFT.biconjugate (fun u : Potential => fun x => pairPotential u x) f d := by
      exact ((pairPotential_surjective_of_standard hLp).iSup_comp
        (fun L : PhysicalPairSpace.Pair →L[ℝ] ℝ =>
          (⨅ x, f x + (L x : EReal)) - (L d : EReal))).symm

end GptLean.PhysicalPairDuality
