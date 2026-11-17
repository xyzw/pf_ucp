import GptLean.ElectronicH1Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import GptLean.SymmetricLift.WeakDerivativeClosure

/-!
Affine isometric changes of electronic variables on the actual H1 graph.

An affine isometry `A x = L x + c` of configuration space preserves Lebesgue
measure, so `u ↦ u ∘ A` is an isometry of electronic L². It preserves the
weak H1 graph, and the weak derivatives transform by the chain rule

`∂ⱼ (u ∘ A) = ∑ᵢ (L eⱼ)ᵢ (∂ᵢ u) ∘ A`.

The proof moves the test function by the inverse map, as in the coordinate
reindexing argument. Translations (`L = 1`) and orthogonal maps of each
particle position are the cases used in `prop-translation-covariance` and
`prop-orthogonal-covariance`.
-/

noncomputable section

namespace GptLean.TransformationsAffine

open MeasureTheory ElectronicH1Space SymmetricLift
open scoped ENNReal ContDiff

set_option backward.isDefEq.respectTransparency.types false

variable (I : Type*) [Fintype I] [DecidableEq I]

/-- An affine isometry `x ↦ L x + c` of configuration space. -/
structure AffineIsometry where
  linear : EuclideanSpace ℝ I ≃ₗᵢ[ℝ] EuclideanSpace ℝ I
  shift : EuclideanSpace ℝ I

namespace AffineIsometry

variable {I} (A : AffineIsometry I)

/-- The map `x ↦ L x + c`. -/
def apply (x : EuclideanSpace ℝ I) : EuclideanSpace ℝ I := A.linear x + A.shift

/-- The inverse affine isometry `y ↦ L⁻¹ (y - c)`. -/
def inv : AffineIsometry I where
  linear := A.linear.symm
  shift := -A.linear.symm A.shift

theorem inv_apply_apply (x : EuclideanSpace ℝ I) : A.inv.apply (A.apply x) = x := by
  simp only [apply, inv, map_add, LinearIsometryEquiv.symm_apply_apply]
  abel

theorem apply_inv_apply (y : EuclideanSpace ℝ I) : A.apply (A.inv.apply y) = y := by
  simp only [apply, inv, map_add, map_neg, LinearIsometryEquiv.apply_symm_apply]
  abel

/-- The affine isometry as a homeomorphism. -/
def toHomeomorph : EuclideanSpace ℝ I ≃ₜ EuclideanSpace ℝ I :=
  (A.linear.toHomeomorph).trans (Homeomorph.addRight A.shift)

theorem toHomeomorph_apply (x : EuclideanSpace ℝ I) : A.toHomeomorph x = A.apply x := rfl

theorem continuous_apply : Continuous A.apply := A.toHomeomorph.continuous

theorem measurePreserving : MeasurePreserving A.apply volume volume :=
  (measurePreserving_add_right volume A.shift).comp A.linear.measurePreserving

/-- The affine isometry as a measurable equivalence. -/
def toMeasurableEquiv : EuclideanSpace ℝ I ≃ᵐ EuclideanSpace ℝ I :=
  A.toHomeomorph.toMeasurableEquiv

theorem toMeasurableEquiv_apply (x : EuclideanSpace ℝ I) :
    A.toMeasurableEquiv x = A.apply x := rfl

theorem hasFDerivAt_apply (x : EuclideanSpace ℝ I) :
    HasFDerivAt A.apply (A.linear.toContinuousLinearEquiv.toContinuousLinearMap) x := by
  have h := A.linear.toContinuousLinearEquiv.hasFDerivAt (x := x)
  exact h.add_const A.shift

/-- The chain-rule coefficient `(L eⱼ)ᵢ`. -/
def coefficient (j i : I) : ℝ := A.linear (EuclideanSpace.single j 1) i

section Pull

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The pullback `u ↦ u ∘ A` on electronic L². -/
def pull (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 E] : L2 E I →ₗᵢ[𝕜] L2 E I :=
  Lp.compMeasurePreservingₗᵢ 𝕜 A.apply A.measurePreserving

theorem pull_ae (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 E] (v : L2 E I) :
    A.pull 𝕜 v =ᵐ[volume] fun x => v (A.apply x) :=
  Lp.coeFn_compMeasurePreserving v A.measurePreserving

theorem pull_inv_pull (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 E] (v : L2 E I) :
    A.inv.pull 𝕜 (A.pull 𝕜 v) = v := by
  apply Lp.ext
  have hp := A.inv.measurePreserving.quasiMeasurePreserving.ae (A.pull_ae 𝕜 v)
  filter_upwards [A.inv.pull_ae 𝕜 (A.pull 𝕜 v), hp] with x hx hy
  rw [hx, hy, A.apply_inv_apply]

theorem pull_pull_inv (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 E] (v : L2 E I) :
    A.pull 𝕜 (A.inv.pull 𝕜 v) = v := by
  apply Lp.ext
  have hp := A.measurePreserving.quasiMeasurePreserving.ae (A.inv.pull_ae 𝕜 v)
  filter_upwards [A.pull_ae 𝕜 (A.inv.pull 𝕜 v), hp] with x hx hy
  rw [hx, hy, A.inv_apply_apply]

theorem pull_test_integral (v : L2 E I) (φ : EuclideanSpace ℝ I → ℝ) :
    (∫ x, φ x • A.pull ℝ v x) = ∫ z, φ (A.inv.apply z) • v z := by
  calc
    _ = ∫ x, φ (A.inv.apply (A.apply x)) • v (A.apply x) := by
      apply integral_congr_ae
      filter_upwards [A.pull_ae ℝ v] with x hx
      rw [hx, A.inv_apply_apply]
    _ = _ := A.measurePreserving.integral_comp A.toMeasurableEquiv.measurableEmbedding
      (fun z => φ (A.inv.apply z) • v z)

theorem test_fderiv (φ : EuclideanSpace ℝ I → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (z : EuclideanSpace ℝ I) (w : EuclideanSpace ℝ I) :
    fderiv ℝ (fun y => φ (A.inv.apply y)) z w = fderiv ℝ φ (A.inv.apply z) (A.linear.symm w) := by
  have hh := ((hφ.differentiable (by simp) _).hasFDerivAt.comp z
    (A.inv.hasFDerivAt_apply z)).fderiv
  rw [show (fun y => φ (A.inv.apply y)) = φ ∘ A.inv.apply from rfl, hh]
  rfl

/-- The coefficients reconstruct `eⱼ` after `L⁻¹`. -/
theorem coefficient_sum (j : I) (T : EuclideanSpace ℝ I →L[ℝ] ℝ) :
    ∑ i, A.coefficient j i * T (A.linear.symm (EuclideanSpace.single i 1)) =
      T (EuclideanSpace.single j 1) := by
  have hv : (∑ i, A.coefficient j i • EuclideanSpace.single i (1 : ℝ)) =
      A.linear (EuclideanSpace.single j 1) := by
    ext k
    simp only [coefficient, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
      EuclideanSpace.ofLp_single, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have h := congrArg (fun v => T (A.linear.symm v)) hv
  simp only [map_sum, map_smul, smul_eq_mul, LinearIsometryEquiv.symm_apply_apply] at h
  exact h

/-- Pairing with a fixed square-integrable test function is linear. -/
def testFunctional (ψ : EuclideanSpace ℝ I → ℝ) (hψ : MemLp ψ 2 volume) : L2 E I →ₗ[ℝ] E where
  toFun v := ∫ x, ψ x • v x
  map_add' v w := by
    rw [← integral_add (integrable_l2_test hψ v) (integrable_l2_test hψ w)]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add v w] with x hx
    rw [hx, Pi.add_apply, smul_add]
  map_smul' c v := by
    rw [RingHom.id_apply, ← integral_smul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul c v] with x hx
    rw [hx, Pi.smul_apply, smul_comm]

/-- The derivative family of the pulled-back vector. -/
def pulledDerivative (u : H1 E I) (j : I) : L2 E I :=
  A.pull ℝ (∑ i, A.coefficient j i • derivative i u)

theorem pulledDerivative_test_integral (u : H1 E I) (j : I)
    (φ : EuclideanSpace ℝ I → ℝ) (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) :
    (∫ x, φ x • A.pulledDerivative u j x) = -(∫ x, (fderiv ℝ φ x (EuclideanSpace.single j 1)) •
      A.pull ℝ (value u) x) := by
  let ψ : EuclideanSpace ℝ I → ℝ := fun y => φ (A.inv.apply y)
  have haff : ContDiff ℝ ∞ A.inv.apply :=
    A.inv.linear.toContinuousLinearEquiv.contDiff.add contDiff_const
  have htest : ContDiff ℝ ∞ ψ := hφ.comp haff
  have hcompact : HasCompactSupport ψ := hs.comp_homeomorph A.inv.toHomeomorph
  have hψ2 : MemLp ψ 2 volume := htest.continuous.memLp_of_hasCompactSupport hcompact
  have hd (i : I) : MemLp (fun z => fderiv ℝ ψ z (EuclideanSpace.single i 1)) 2 volume :=
    ((htest.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hcompact.fderiv_apply ℝ _)
  have hL : (∫ x, φ x • A.pulledDerivative u j x) =
      ∑ i, A.coefficient j i • ∫ z, ψ z • derivative i u z := by
    unfold pulledDerivative
    rw [A.pull_test_integral]
    change testFunctional ψ hψ2 (∑ i, A.coefficient j i • derivative i u) = _
    rw [map_sum]
    simp only [map_smul]
    rfl
  have hweak (i : I) : (∫ z, ψ z • derivative i u z) =
      -(∫ z, (fderiv ℝ φ (A.inv.apply z) (A.linear.symm (EuclideanSpace.single i 1))) • value u z) := by
    have h := (weak u).weak i ψ htest hcompact
    rw [h]
    congr 2
    funext z
    rw [A.test_fderiv φ hφ z]
  have hR : (∫ x, (fderiv ℝ φ x (EuclideanSpace.single j 1)) • A.pull ℝ (value u) x) =
      ∫ z, (fderiv ℝ φ (A.inv.apply z) (EuclideanSpace.single j 1)) • value u z :=
    A.pull_test_integral (value u) (fun x => fderiv ℝ φ x (EuclideanSpace.single j 1))
  rw [hL, hR]
  simp_rw [hweak, smul_neg, ← integral_smul]
  rw [Finset.sum_neg_distrib, ← integral_finset_sum]
  · congr 1
    apply integral_congr_ae
    refine ae_of_all _ fun z => ?_
    simp only [smul_smul, ← Finset.sum_smul]
    congr 1
    exact A.coefficient_sum j (fderiv ℝ φ (A.inv.apply z))
  · intro i _
    have hi := integrable_l2_test (hd i) (value u)
    refine (hi.smul (A.coefficient j i)).congr (ae_of_all _ fun z => ?_)
    change A.coefficient j i • ((fderiv ℝ (fun y => φ (A.inv.apply y)) z)
      (EuclideanSpace.single i 1) • value u z) = _
    rw [A.test_fderiv φ hφ z]

theorem weak_pull (u : H1 E I) :
    HasWeakH1Local (A.pull ℝ (value u)) (fun j => A.pulledDerivative u j) :=
  ⟨fun K _ => (Lp.memLp _).restrict K, fun j K _ => (Lp.memLp _).restrict K,
    fun j φ hφ hs => A.pulledDerivative_test_integral u j φ hφ hs⟩

end Pull


section Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [CompleteSpace E]

/-- The pulled-back value and weak derivatives of a complex H1 vector. -/
def pullComplexPair (u : ElectronicH1Complex.ComplexH1 E I) : L2 E I × (I → L2 E I) :=
  (A.pull ℂ (ElectronicH1Complex.value u), fun j =>
    A.pull ℂ (∑ i, A.coefficient j i • ElectronicH1Complex.derivative i u))

theorem pullComplexPair_mem (u : ElectronicH1Complex.ComplexH1 E I) :
    A.pullComplexPair u ∈ ElectronicH1Complex.complexWeakGraph E I :=
  A.weak_pull (ElectronicH1Complex.realEquiv u)

/-- The chain-rule constant of the pulled-back H1 graph norm. -/
def h1Constant : ℝ := 1 + ∑ j, ∑ i, |A.coefficient j i|

theorem h1Constant_nonneg : 0 ≤ A.h1Constant := by
  unfold h1Constant
  positivity

/-- The pulled-back complex H1 vector. -/
def pullH1Fun (u : ElectronicH1Complex.ComplexH1 E I) : ElectronicH1Complex.ComplexH1 E I :=
  ⟨A.pullComplexPair u, A.pullComplexPair_mem u⟩

theorem pullH1Fun_norm_le (u : ElectronicH1Complex.ComplexH1 E I) :
    ‖A.pullH1Fun u‖ ≤ A.h1Constant * ‖u‖ := by
  have hu : 0 ≤ ‖u‖ := norm_nonneg u
  have hsum : 0 ≤ ∑ j, ∑ i, |A.coefficient j i| := by positivity
  rw [ElectronicH1Complex.norm_eq_max]
  apply max_le
  · change ‖A.pull ℂ (ElectronicH1Complex.value u)‖ ≤ _
    rw [LinearIsometry.norm_map]
    refine (ElectronicH1Complex.norm_value_le u).trans ?_
    unfold h1Constant
    nlinarith
  · apply (pi_norm_le_iff_of_nonneg (mul_nonneg A.h1Constant_nonneg hu)).mpr
    intro j
    change ‖A.pull ℂ (∑ i, A.coefficient j i • ElectronicH1Complex.derivative i u)‖ ≤ _
    rw [LinearIsometry.norm_map]
    calc _ ≤ ∑ i, ‖A.coefficient j i • ElectronicH1Complex.derivative i u‖ := norm_sum_le _ _
      _ ≤ ∑ i, |A.coefficient j i| * ‖u‖ := by
          apply Finset.sum_le_sum
          intro i _
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (ElectronicH1Complex.norm_derivative_le u i)
            (abs_nonneg _)
      _ = (∑ i, |A.coefficient j i|) * ‖u‖ := (Finset.sum_mul _ _ _).symm
      _ ≤ A.h1Constant * ‖u‖ := by
          apply mul_le_mul_of_nonneg_right _ hu
          unfold h1Constant
          have hj : ∑ i, |A.coefficient j i| ≤ ∑ j, ∑ i, |A.coefficient j i| :=
            Finset.single_le_sum (f := fun j => ∑ i, |A.coefficient j i|)
              (fun j _ => by positivity) (Finset.mem_univ j)
          linarith

/-- The pullback by an affine isometry as a bounded map of the complex H1 graph. -/
def pullH1 : ElectronicH1Complex.ComplexH1 E I →L[ℂ] ElectronicH1Complex.ComplexH1 E I :=
  LinearMap.mkContinuous
    { toFun := A.pullH1Fun
      map_add' := fun u v => ElectronicH1Complex.value_injective (by
        change A.pull ℂ (ElectronicH1Complex.value (u + v)) =
          A.pull ℂ (ElectronicH1Complex.value u) + A.pull ℂ (ElectronicH1Complex.value v)
        rw [map_add, map_add])
      map_smul' := fun c u => ElectronicH1Complex.value_injective (by
        change A.pull ℂ (ElectronicH1Complex.value (c • u)) =
          c • A.pull ℂ (ElectronicH1Complex.value u)
        rw [map_smul, map_smul]) }
    A.h1Constant A.pullH1Fun_norm_le

@[simp] theorem value_pullH1 (u : ElectronicH1Complex.ComplexH1 E I) :
    ElectronicH1Complex.value (A.pullH1 u) = A.pull ℂ (ElectronicH1Complex.value u) := rfl

@[simp] theorem derivative_pullH1 (j : I) (u : ElectronicH1Complex.ComplexH1 E I) :
    ElectronicH1Complex.derivative j (A.pullH1 u) =
      A.pull ℂ (∑ i, A.coefficient j i • ElectronicH1Complex.derivative i u) := rfl

theorem pullH1_inv (u : ElectronicH1Complex.ComplexH1 E I) : A.inv.pullH1 (A.pullH1 u) = u :=
  ElectronicH1Complex.value_injective (by
    rw [value_pullH1, value_pullH1, pull_inv_pull])

theorem pullH1_inv_left (u : ElectronicH1Complex.ComplexH1 E I) : A.pullH1 (A.inv.pullH1 u) = u :=
  ElectronicH1Complex.value_injective (by
    rw [value_pullH1, value_pullH1, pull_pull_inv])

end Complex

/-! ### Translations -/

/-- The translation `x ↦ x + c`. -/
def translation (c : EuclideanSpace ℝ I) : AffineIsometry I where
  linear := LinearIsometryEquiv.refl ℝ _
  shift := c

theorem translation_coefficient (c : EuclideanSpace ℝ I) (j i : I) :
    (translation c).coefficient j i = if j = i then 1 else 0 := by
  simp only [coefficient, translation, LinearIsometryEquiv.coe_refl, id_eq,
    EuclideanSpace.single_apply]
  split_ifs with h₁ h₂ h₂ <;> simp_all

theorem translation_sum {M : Type*} [AddCommGroup M] [Module ℝ M]
    (c : EuclideanSpace ℝ I) (j : I) (d : I → M) :
    ∑ i, (translation c).coefficient j i • d i = d j := by
  simp only [translation_coefficient, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

end AffineIsometry

end GptLean.TransformationsAffine
