import PfHk.PhysicalComparisonSpectral
import PfHk.PhysicalLocalEnergySobolev

/-! The first comparison-operator endpoint for actual scalar localizations.
The radiation field estimate recovers the ordinary gradient, and the exact
covariant product rule supplies the cutoff error terms. -/

noncomputable section
namespace PfHk.PhysicalOperatorDomain

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.ElectronicH1Multiplier PfHk.PhysicalLocalEnergy PfHk.PhysicalCutoffCommutator
open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 40000
set_option Elab.async false

local instance rootCutoffPhotonDirectInner : InnerProductSpace ℂ PhotonFock :=
  { (inferInstance : InnerProductSpace ℂ PhotonFock) with
    toNormedSpace := (inferInstance : NormedSpace ℂ PhotonFock) }

attribute [local irreducible] PhysicalPFReference.covariant PhysicalPFReference.field
  PhysicalPFReference.ordinary PhysicalPFReference.inclusion PhysicalPFReference.radiation
  PhysicalPFReference.potential PhysicalPFScalarMultiplier.multiply
  DifferentiableMultiplier.multiplier DifferentiableMultiplier.derivativeMultiplier

private theorem phase_sum_sq {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (x y z : H) (hz : z = x + (-Complex.I) • y) :
    ‖z‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h : ‖z‖ ≤ ‖x‖ + ‖y‖ := by
    simpa only [hz, norm_smul, norm_neg, Complex.norm_I, one_mul] using
      norm_add_le x ((-Complex.I) • y)
  have hs := pow_le_pow_left₀ (norm_nonneg z) h 2
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

def rootRecoveryFactor (d : ℕ) (e M : ℝ) : ℝ :=
  3 + 24 * e ^ 2 * (max M 0) ^ 2 * d

theorem rootRecoveryFactor_nonneg (d : ℕ) (e M : ℝ) : 0 ≤ rootRecoveryFactor d e M := by
  unfold rootRecoveryFactor
  positivity

private theorem root_recovery_algebra (d e m o k r n : ℝ)
    (hd : 0 ≤ d) (hk : 0 ≤ k) (hr : 0 ≤ r) (hn : 0 ≤ n)
    (ho : o ≤ 3 * k + 24 * e ^ 2 * m ^ 2 * d * r + 6 * e ^ 2 * m ^ 2 * d * n) :
    o + r + n ≤ (3 + 24 * e ^ 2 * m ^ 2 * d) * (k + r + n) := by
  have hprod : 0 ≤ e ^ 2 * m ^ 2 * d := mul_nonneg
    (mul_nonneg (sq_nonneg e) (sq_nonneg m)) hd
  nlinarith [mul_nonneg hprod hk, mul_nonneg hprod hn]

private theorem sum_recovery {J : Type*} [Fintype J] (o k : J → ℝ) (r n a b : ℝ)
    (h : ∀ j, o j ≤ 3 * k j + a * r + b * n) :
    (∑ j, o j) ≤ 3 * (∑ j, k j) + a * (Fintype.card J) * r + b * (Fintype.card J) * n := by
  calc
    _ ≤ ∑ j, (3 * k j + a * r + b * n) := Finset.sum_le_sum fun j _ => h j
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      ring

private theorem sum_phase_sq {J H : Type*} [Fintype J]
    [NormedAddCommGroup H] [NormedSpace ℂ H] (x y z : J → H)
    (hz : ∀ j, z j = x j + (-Complex.I) • y j) :
    (∑ j, ‖z j‖ ^ 2) ≤ 2 * (∑ j, ‖x j‖ ^ 2) + 2 * (∑ j, ‖y j‖ ^ 2) := by
  have h := Finset.sum_le_sum (s := Finset.univ) fun j _ => phase_sum_sq _ _ _ (hz j)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum] using h

private theorem weighted_sum_bound {J : Type*} (F : Finset J)
    (w lhs rhs : J → ℝ) (C : ℝ) (hw : ∀ j ∈ F, 0 ≤ w j)
    (h : ∀ j ∈ F, lhs j ≤ C * rhs j) :
    (∑ j ∈ F, w j * lhs j) ≤ C * ∑ j ∈ F, w j * rhs j := by
  calc
    _ ≤ ∑ j ∈ F, w j * (C * rhs j) :=
      Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (h j hj) (hw j hj)
    _ = _ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => mul_left_comm _ _ _

variable {I : Type} [Fintype I] [DecidableEq I]
variable (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hb : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)

private theorem ordinary_free_sq (u : Reference I (fun _ => 0)) (i : I) :
    ‖ordinary I (fun _ => 0) i u‖ ^ 2 ≤
      3 * ‖covariant I (fun _ => 0) C κ hκ M hb e i u‖ ^ 2 +
      24 * e ^ 2 * (max M 0) ^ 2 * ‖radiation I (fun _ => 0) u‖ ^ 2 +
      6 * e ^ 2 * (max M 0) ^ 2 * ‖inclusion I (fun _ => 0) u‖ ^ 2 := by
  have ho := ordinary_sq_le_external (fun _ => 0) C κ hκ M hb e
    (fun _ _ => 0) (fun _ => 0) (fun _ => 0) u (zeroExternalDomain (fun _ => 0) u) i
  have ho' : ‖ordinary I (fun _ => 0) i u‖ ^ 2 ≤
      3 * ‖covariant I (fun _ => 0) C κ hκ M hb e i u‖ ^ 2 +
        3 * e ^ 2 * ‖field I (fun _ => 0) C κ hκ M hb i u‖ ^ 2 := by
    simpa only [externalCovariant, roughMultiply_zero, add_zero, norm_zero,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] using ho
  have hf := mul_le_mul_of_nonneg_left
    (uniform_field_bound (fun _ => 0) C κ hκ M hb u i)
    (by positivity : 0 ≤ 3 * e ^ 2)
  linarith only [ho', hf]

theorem ordinary_free_energy (u : Reference I (fun _ => 0)) :
    (∑ i, ‖ordinary I (fun _ => 0) i u‖ ^ 2) ≤
      3 * (∑ i, ‖covariant I (fun _ => 0) C κ hκ M hb e i u‖ ^ 2) +
      24 * e ^ 2 * (max M 0) ^ 2 * (Fintype.card I) * ‖radiation I (fun _ => 0) u‖ ^ 2 +
      6 * e ^ 2 * (max M 0) ^ 2 * (Fintype.card I) * ‖inclusion I (fun _ => 0) u‖ ^ 2 := by
  exact sum_recovery _ _ _ _ _ _ (ordinary_free_sq C κ hκ M hb e u)

theorem root_norm_le_physical (S : ComparisonSpectralCalculus (I := I))
    (u : Reference I (fun _ => 0)) :
    ‖S.root u‖ ^ 2 ≤ rootRecoveryFactor (Fintype.card I) e M *
      ((∑ i, ‖covariant I (fun _ => 0) C κ hκ M hb e i u‖ ^ 2) +
        ‖radiation I (fun _ => 0) u‖ ^ 2 + ‖inclusion I (fun _ => 0) u‖ ^ 2) := by
  exact (S.root_form u).le.trans
    (root_recovery_algebra (Fintype.card I) e (max M 0) _ _ _ _
      (Nat.cast_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (sq_nonneg _) (sq_nonneg _) (ordinary_free_energy C κ hκ M hb e u))

/-- Actual localized half-power energy, including every first-cutoff
derivative. This is the first dyadic endpoint before weighted summation. -/
theorem root_localize (S : ComparisonSpectralCalculus (I := I))
    (a : DifferentiableMultiplier I) (u : Reference I (fun _ => 0)) :
    ‖S.root (PhysicalPFScalarMultiplier.multiply (fun _ => 0) a u)‖ ^ 2 ≤
      rootRecoveryFactor (Fintype.card I) e M *
        (2 * (∑ i, ‖a.multiplier (covariant I (fun _ => 0) C κ hκ M hb e i u)‖ ^ 2) +
          2 * (∑ i, ‖a.derivativeMultiplier i (inclusion I (fun _ => 0) u)‖ ^ 2) +
          ‖a.multiplier (radiation I (fun _ => 0) u)‖ ^ 2 +
          ‖a.multiplier (inclusion I (fun _ => 0) u)‖ ^ 2) := by
  have hsum' : (∑ i, ‖covariant I (fun _ => 0) C κ hκ M hb e i
      (PhysicalPFScalarMultiplier.multiply (fun _ => 0) a u)‖ ^ 2) ≤
      2 * (∑ i, ‖a.multiplier (covariant I (fun _ => 0) C κ hκ M hb e i u)‖ ^ 2) +
        2 * (∑ i, ‖a.derivativeMultiplier i (inclusion I (fun _ => 0) u)‖ ^ 2) :=
    sum_phase_sq _ _ _
      (PhysicalPFScalarMultiplier.covariant_multiply (fun _ => 0) a C κ hκ M hb e u)
  have hr := congrArg (fun z : WaveSpace I => ‖z‖ ^ 2)
    (PhysicalPFScalarMultiplier.radiation_multiply (fun _ => 0) a u)
  have hm := congrArg (fun z : WaveSpace I => ‖z‖ ^ 2)
    (PhysicalPFScalarMultiplier.value_multiply (fun _ => 0) a u)
  exact (root_norm_le_physical C κ hκ M hb e S _).trans
    (mul_le_mul_of_nonneg_left (add_le_add (add_le_add hsum' hr.le) hm.le)
      (rootRecoveryFactor_nonneg (Fintype.card I) e M))

/-- Weighted finite families of actual localizations. The annular powers
in the dyadic argument are substituted for the nonnegative weights. -/
theorem root_localize_sum {J : Type*} (F : Finset J)
    (S : ComparisonSpectralCalculus (I := I)) (a : J → DifferentiableMultiplier I)
    (w : J → ℝ) (hw : ∀ j ∈ F, 0 ≤ w j) (u : Reference I (fun _ => 0)) :
    (∑ j ∈ F, w j * ‖S.root (PhysicalPFScalarMultiplier.multiply (fun _ => 0) (a j) u)‖ ^ 2) ≤
      rootRecoveryFactor (Fintype.card I) e M *
        ∑ j ∈ F, w j *
          (2 * (∑ i, ‖(a j).multiplier (covariant I (fun _ => 0) C κ hκ M hb e i u)‖ ^ 2) +
            2 * (∑ i, ‖(a j).derivativeMultiplier i (inclusion I (fun _ => 0) u)‖ ^ 2) +
            ‖(a j).multiplier (radiation I (fun _ => 0) u)‖ ^ 2 +
            ‖(a j).multiplier (inclusion I (fun _ => 0) u)‖ ^ 2) := by
  exact weighted_sum_bound F _ _ _ _ hw fun j _ => root_localize C κ hκ M hb e S (a j) u

end PfHk.PhysicalOperatorDomain
