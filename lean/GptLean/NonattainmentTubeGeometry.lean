import GptLean.NonattainmentEllipse

/-!
Explicit normal geometry of the central ellipse. A quadratic normal/chord
estimate proves uniqueness of normal coordinates below the radius `a² / b`.
No reach estimate or tubular-coordinate existence theorem is assumed.
-/

noncomputable section

namespace GptLean.Nonattainment

open Gaussian
open scoped InnerProductSpace

set_option Elab.async false
set_option maxHeartbeats 400000

def ellipseNormalNumerator (a b t : ℝ) : FieldSpace :=
  (b * Real.cos t) • coordinateAxis 0 + (a * Real.sin t) • coordinateAxis 1

/-- The inward unit normal in the plane of the ellipse. -/
def ellipseNormal (a b t : ℝ) : FieldSpace :=
  -(‖ellipseVelocity a b t‖⁻¹ • ellipseNormalNumerator a b t)

theorem ellipseNormalNumerator_norm (a b t : ℝ) :
    ‖ellipseNormalNumerator a b t‖ = ‖ellipseVelocity a b t‖ := by
  have h : ‖ellipseNormalNumerator a b t‖ ^ 2 = ‖ellipseVelocity a b t‖ ^ 2 := by
    rw [ellipseVelocity_norm_sq]
    simp [ellipseNormalNumerator, coordinateAxis, EuclideanSpace.norm_sq_eq,
      Fin.sum_univ_three, mul_pow, add_comm]
  nlinarith [norm_nonneg (ellipseNormalNumerator a b t), norm_nonneg (ellipseVelocity a b t)]

theorem ellipseNormal_norm {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (t : ℝ) :
    ‖ellipseNormal a b t‖ = 1 := by
  rw [ellipseNormal, norm_neg, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (norm_nonneg _), ellipseNormalNumerator_norm]
  exact inv_mul_cancel₀ (ellipseVelocity_norm_pos ha hab t).ne'

theorem ellipseNormalNumerator_inner_chord (a b θ φ : ℝ) :
    ⟪ellipseNormalNumerator a b θ, ellipse a b φ - ellipse a b θ⟫_ℝ =
      a * b * (Real.cos (φ - θ) - 1) := by
  simp [ellipseNormalNumerator, ellipse, coordinateAxis, PiLp.inner_apply,
    Fin.sum_univ_three, Real.cos_sub]
  nlinarith [congrArg (fun r : ℝ => a * b * r) (Real.sin_sq_add_cos_sq θ)]

theorem ellipseNormal_inner_chord (a b θ φ : ℝ) :
    ⟪ellipseNormal a b θ, ellipse a b φ - ellipse a b θ⟫_ℝ =
      (a * b / ‖ellipseVelocity a b θ‖) * (1 - Real.cos (φ - θ)) := by
  rw [ellipseNormal, inner_neg_left, real_inner_smul_left,
    ellipseNormalNumerator_inner_chord]
  ring

theorem ellipse_chord_norm_sq (a b θ φ : ℝ) :
    ‖ellipse a b φ - ellipse a b θ‖ ^ 2 =
      a ^ 2 * (Real.cos φ - Real.cos θ) ^ 2 +
        b ^ 2 * (Real.sin φ - Real.sin θ) ^ 2 := by
  simp [ellipse, coordinateAxis, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  ring

theorem ellipse_chord_lower {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (θ φ : ℝ) :
    2 * a ^ 2 * (1 - Real.cos (φ - θ)) ≤ ‖ellipse a b φ - ellipse a b θ‖ ^ 2 := by
  have hcircle : (Real.cos φ - Real.cos θ) ^ 2 + (Real.sin φ - Real.sin θ) ^ 2 =
      2 * (1 - Real.cos (φ - θ)) := by
    rw [Real.cos_sub]
    nlinarith [Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq φ]
  rw [ellipse_chord_norm_sq]
  calc
    _ = a ^ 2 * (Real.cos φ - Real.cos θ) ^ 2 +
        a ^ 2 * (Real.sin φ - Real.sin θ) ^ 2 := by rw [← mul_add, hcircle]; ring
    a ^ 2 * (Real.cos φ - Real.cos θ) ^ 2 + a ^ 2 * (Real.sin φ - Real.sin θ) ^ 2 ≤
        a ^ 2 * (Real.cos φ - Real.cos θ) ^ 2 + b ^ 2 * (Real.sin φ - Real.sin θ) ^ 2 := by
      linarith [mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ ha hab 2) (sq_nonneg (Real.sin φ - Real.sin θ))]

/-- Global quadratic control of the inward normal component of every chord. -/
theorem ellipseNormal_chord_quadratic {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (θ φ : ℝ) :
    |⟪ellipseNormal a b θ, ellipse a b φ - ellipse a b θ⟫_ℝ| ≤
      (b / (2 * a ^ 2)) * ‖ellipse a b φ - ellipse a b θ‖ ^ 2 := by
  have hb : 0 < b := ha.trans_le hab
  have hc : 0 ≤ 1 - Real.cos (φ - θ) := sub_nonneg.mpr (Real.cos_le_one _)
  have hv := ellipseVelocity_norm_pos ha hab θ
  rw [ellipseNormal_inner_chord, abs_of_nonneg (mul_nonneg (div_nonneg
    (mul_nonneg ha.le hb.le) hv.le) hc)]
  calc
    (a * b / ‖ellipseVelocity a b θ‖) * (1 - Real.cos (φ - θ)) ≤
        b * (1 - Real.cos (φ - θ)) := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hv).mpr
      nlinarith [mul_le_mul_of_nonneg_right (le_ellipseVelocity_norm ha.le hab θ)
        (mul_nonneg hb.le hc)]
    _ ≤ (b / (2 * a ^ 2)) * ‖ellipse a b φ - ellipse a b θ‖ ^ 2 := by
      calc
        b * (1 - Real.cos (φ - θ)) = (b / (2 * a ^ 2)) *
            (2 * a ^ 2 * (1 - Real.cos (φ - θ))) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (ellipse_chord_lower ha.le hab θ φ)
          (show 0 ≤ b / (2 * a ^ 2) by positivity)

theorem ellipseNormal_eq_of_ellipse_eq {a b θ φ : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (h : ellipse a b θ = ellipse a b φ) : ellipseNormal a b θ = ellipseNormal a b φ := by
  have hb : 0 < b := ha.trans_le hab
  have hc : Real.cos θ = Real.cos φ := by
    have h₀ := congrArg (fun x : FieldSpace => x 0) h
    simpa [ellipse, coordinateAxis, ha.ne'] using h₀
  have hs : Real.sin θ = Real.sin φ := by
    have h₁ := congrArg (fun x : FieldSpace => x 1) h
    simpa [ellipse, coordinateAxis, hb.ne'] using h₁
  simp [ellipseNormal, ellipseNormalNumerator, ellipseVelocity, hc, hs]

/-- Normal offsets of absolute size less than `a² / b` have a unique base point
and a unique signed offset. This proves the required injectivity directly. -/
theorem ellipse_normal_coordinates_unique {a b θ φ t s : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (ht : |t| < a ^ 2 / b) (hs : |s| < a ^ 2 / b)
    (h : ellipse a b θ + t • ellipseNormal a b θ =
      ellipse a b φ + s • ellipseNormal a b φ) :
    ellipse a b θ = ellipse a b φ ∧ t = s := by
  have hb : 0 < b := ha.trans_le hab
  let D := ellipse a b φ - ellipse a b θ
  have hD : D = t • ellipseNormal a b θ - s • ellipseNormal a b φ := by
    dsimp [D]
    apply sub_eq_sub_iff_add_eq_add.mpr
    simpa only [add_comm] using h.symm
  have hθ := ellipseNormal_chord_quadratic ha hab θ φ
  have hφ := ellipseNormal_chord_quadratic ha hab φ θ
  have hφ' : |⟪ellipseNormal a b φ, D⟫_ℝ| ≤ (b / (2 * a ^ 2)) * ‖D‖ ^ 2 := by
    have hrev : ellipse a b θ - ellipse a b φ = -D := by dsimp [D]; abel
    rw [hrev, inner_neg_right, abs_neg, norm_neg] at hφ
    exact hφ
  have hbound : ‖D‖ ^ 2 ≤ (|t| + |s|) * (b / (2 * a ^ 2)) * ‖D‖ ^ 2 := by
    calc
      ‖D‖ ^ 2 = t * ⟪ellipseNormal a b θ, D⟫_ℝ - s * ⟪ellipseNormal a b φ, D⟫_ℝ := by
        rw [← real_inner_self_eq_norm_sq, hD]
        simp only [inner_sub_left, real_inner_smul_left]
      _ ≤ |t| * |⟪ellipseNormal a b θ, D⟫_ℝ| + |s| * |⟪ellipseNormal a b φ, D⟫_ℝ| := by
        nlinarith [le_abs_self (t * ⟪ellipseNormal a b θ, D⟫_ℝ),
          neg_le_abs (s * ⟪ellipseNormal a b φ, D⟫_ℝ),
          abs_mul t ⟪ellipseNormal a b θ, D⟫_ℝ, abs_mul s ⟪ellipseNormal a b φ, D⟫_ℝ]
      _ ≤ |t| * ((b / (2 * a ^ 2)) * ‖D‖ ^ 2) +
          |s| * ((b / (2 * a ^ 2)) * ‖D‖ ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hθ (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hφ' (abs_nonneg _))
      _ = _ := by ring
  have hsmall : (|t| + |s|) * (b / (2 * a ^ 2)) < 1 := by
    have hts := add_lt_add ht hs
    have hp : 0 < b / (2 * a ^ 2) := by positivity
    calc
      _ < (a ^ 2 / b + a ^ 2 / b) * (b / (2 * a ^ 2)) := mul_lt_mul_of_pos_right hts hp
      _ = 1 := by field_simp; ring
  have hzero : D = 0 := by
    have hn : ‖D‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖D‖]
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
  have hbase : ellipse a b θ = ellipse a b φ := (sub_eq_zero.mp hzero).symm
  refine ⟨hbase, ?_⟩
  have hnormal := ellipseNormal_eq_of_ellipse_eq ha hab hbase
  rw [hbase, hnormal] at h
  have hsmul := add_left_cancel h
  have hne : ellipseNormal a b φ ≠ 0 := by
    intro he
    have hn := ellipseNormal_norm ha hab φ
    simp [he] at hn
  exact (smul_left_injective ℝ hne) hsmul

end GptLean.Nonattainment
