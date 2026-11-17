import PfHk.PolarCalculus

/-! Bilinear radial/tangent splitting for weak form transport. -/

noncomputable section
namespace PfHk.PolarCalculus
open MeasureTheory
open scoped InnerProductSpace
set_option Elab.async false
set_option maxHeartbeats 300000

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The bilinear version of radial/tangent orthogonality. -/
theorem radial_tangent_inner (θ : UnitSphere I) (v w : H) (a b : I → H)
    (ha : (∑ j, θ.val j • a j) = 0) (hb : (∑ j, θ.val j • b j) = 0) :
    (∑ j, inner ℝ (θ.val j • v + a j) (θ.val j • w + b j)) =
      inner ℝ v w + ∑ j, inner ℝ (a j) (b j) := by
  have hθ : (∑ j, (θ.val j) ^ 2) = 1 := by
    simpa only [unitSphere_norm I θ, one_pow] using (EuclideanSpace.real_norm_sq_eq θ.val).symm
  have hrad : (∑ j, inner ℝ (θ.val j • v) (θ.val j • w)) = inner ℝ v w := by
    simp only [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, ← pow_two,
      ← Finset.sum_mul, hθ, one_mul]
  have hcross₁ : (∑ j, inner ℝ (θ.val j • v) (b j)) = 0 := by
    calc
      _ = inner ℝ v (∑ j, θ.val j • b j) := by
        simp only [inner_sum, real_inner_smul_left, real_inner_smul_right]
      _ = 0 := by rw [hb, inner_zero_right]
  have hcross₂ : (∑ j, inner ℝ (a j) (θ.val j • w)) = 0 := by
    calc
      _ = inner ℝ (∑ j, θ.val j • a j) w := by
        simp only [sum_inner, real_inner_smul_left, real_inner_smul_right]
      _ = 0 := by rw [ha, inner_zero_left]
  simp only [inner_add_left, inner_add_right, Finset.sum_add_distrib,
    hrad, hcross₁, hcross₂, add_zero, zero_add]

/-- Real and complex Hilbert structures with the same norm have the same
real pairing. This avoids relying on definitional equality of L2 instances. -/
theorem real_inner_eq_complex_re [InnerProductSpace ℂ H] (x y : H) :
    inner ℝ x y = (inner ℂ x y).re :=
  (real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two x y).trans
    (re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two
      (𝕜 := ℂ) x y).symm

/-- A complex unitary preserves every compatible real Hilbert pairing.
The proof uses the common norm, so no scalar-instance identification is needed. -/
theorem complexIsometry_real_inner [NormedSpace ℂ H]
    (U : H ≃ₗᵢ[ℂ] H) (x y : H) :
    inner ℝ (U x) (U y) = inner ℝ x y := by
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two]
  rw [← map_add, U.norm_map, U.norm_map, U.norm_map]

theorem l2_inner_integrable {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (u v : Lp H 2 μ) {f g : X → H} (hu : u =ᵐ[μ] f) (hv : v =ᵐ[μ] g) :
    Integrable (fun x => inner ℝ (f x) (g x)) μ := by
  apply (L2.integrable_inner (𝕜 := ℝ) u v).congr
  filter_upwards [hu, hv] with x hx hy
  rw [hx, hy]

theorem l2_inner_eq_integral {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (u v : Lp H 2 μ) {f g : X → H} (hu : u =ᵐ[μ] f) (hv : v =ᵐ[μ] g) :
    inner ℝ u v = ∫ x, inner ℝ (f x) (g x) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu, hv] with x hx hy
  rw [hx, hy]

theorem l2_freeForm_eq_integral [InnerProductSpace ℂ H]
    {X J : Type*} [MeasurableSpace X] [Fintype J] {μ : Measure X}
    (u v : J → Lp H 2 μ) (a b : Lp H 2 μ)
    {uf vf : J → X → H} {af bf : X → H}
    (hu : ∀ j, u j =ᵐ[μ] uf j) (hv : ∀ j, v j =ᵐ[μ] vf j)
    (ha : a =ᵐ[μ] af) (hb : b =ᵐ[μ] bf) :
    ((1 / 2 : ℂ) * ∑ j, inner ℂ (u j) (v j) + inner ℂ a b).re =
      ∫ x, (1 / 2 : ℝ) * ∑ j, inner ℝ (uf j x) (vf j x) + inner ℝ (af x) (bf x) ∂μ := by
  have hi (j : J) := l2_inner_integrable (u j) (v j) (hu j) (hv j)
  have hr := l2_inner_integrable a b ha hb
  rw [integral_add ((integrable_finsetSum _ fun j _ => hi j).const_mul _) hr,
    integral_const_mul, integral_finsetSum _ fun j _ => hi j]
  simp only [Complex.add_re, Complex.mul_re, Complex.div_re, Complex.div_im,
    Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_sum, Complex.im_sum]
  norm_num
  congr 1
  · apply congrArg (fun s : ℝ => (1 / 2 : ℝ) * s)
    apply Finset.sum_congr rfl
    intro j _
    exact (real_inner_eq_complex_re (u j) (v j)).symm.trans
      (l2_inner_eq_integral (u j) (v j) (hu j) (hv j))
  · exact (real_inner_eq_complex_re a b).symm.trans (l2_inner_eq_integral a b ha hb)

section Covariant
variable [NormedSpace ℂ H] [IsScalarTower ℝ ℂ H]

/-- Multiplication by a unit complex number preserves the underlying real inner product. -/
def phaseIsometry (a : ℂ) (ha : ‖a‖ = 1) : H →ₗᵢ[ℝ] H where
  toFun x := a • x
  map_add' x y := smul_add a x y
  map_smul' r x := smul_comm a r x
  norm_map' x := by
    change ‖a • x‖ = ‖x‖
    rw [norm_smul, ha, one_mul]

/-- Ordinary bilinear covariant splitting for arbitrary tangent actions. -/
theorem covariant_inner_decomposition (P : StandardPolarCalculus I H)
    (u v : Position I → H) (hu : ContDiff ℝ (1 : ℕ∞) u) (hv : ContDiff ℝ (1 : ℕ∞) v)
    (a b : I → Position I → H) {r : ℝ} (hr : 0 < r) (θ : UnitSphere I)
    (hus : SphereC1 (radialRestriction u r)) (hvs : SphereC1 (radialRestriction v r))
    (ha : (∑ j, θ.val j • a j (r • θ.val)) = 0)
    (hb : (∑ j, θ.val j • b j (r • θ.val)) = 0) :
    r ^ 2 * (∑ j, inner ℝ (covariant u a j (r • θ.val)) (covariant v b j (r • θ.val))) =
      r ^ 2 * inner ℝ (radialFirst u r θ) (radialFirst v r θ) +
        ∑ j, inner ℝ (angularCovariant u a r j θ) (angularCovariant v b r j θ) := by
  calc
    _ = ∑ j, inner ℝ (r • covariant u a j (r • θ.val))
        (r • covariant v b j (r • θ.val)) := by
      simp only [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, ← pow_two,
        Finset.mul_sum]
    _ = ∑ j, inner ℝ
        (θ.val j • ((-Complex.I) • (r • radialFirst u r θ)) + angularCovariant u a r j θ)
        (θ.val j • ((-Complex.I) • (r • radialFirst v r θ)) + angularCovariant v b r j θ) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [covariant_decomposition P u hu a hr θ j, covariant_decomposition P v hv b hr θ j]
    _ = inner ℝ ((-Complex.I) • (r • radialFirst u r θ))
        ((-Complex.I) • (r • radialFirst v r θ)) +
        ∑ j, inner ℝ (angularCovariant u a r j θ) (angularCovariant v b r j θ) :=
      radial_tangent_inner θ _ _ _ _ (angularCovariant_tangent P u a r θ hus ha)
        (angularCovariant_tangent P v b r θ hvs hb)
    _ = _ := by
      have hphase := (phaseIsometry (-Complex.I) (by simp) : H →ₗᵢ[ℝ] H).inner_map_map
        (r • radialFirst u r θ) (r • radialFirst v r θ)
      change inner ℝ ((-Complex.I) • (r • radialFirst u r θ))
        ((-Complex.I) • (r • radialFirst v r θ)) = _ at hphase
      rw [hphase, real_inner_smul_left, real_inner_smul_right]
      ring

end Covariant

end PfHk.PolarCalculus
