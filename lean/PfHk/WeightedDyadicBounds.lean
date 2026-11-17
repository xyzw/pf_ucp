import PfHk.WeightedDyadicCutoffs
import PfHk.DyadicCoefficientBounds
import PfHk.CarlemanAnnularWeights
import PfHk.ScalarCommutatorEstimate

/-! Finite-overlap endpoint envelopes for the constructed weighted cutoffs. -/

noncomputable section
namespace PfHk.SmoothDyadicCutoffs

open PfHk.CarlemanWeights PfHk.CarlemanSpatialDensity PfHk.DyadicFractional
  PfHk.SmoothCutoffBounds PfHk.PhysicalCutoffCommutator

set_option Elab.async false
set_option maxHeartbeats 80000

variable {I : Type} [Fintype I] [DecidableEq I] {O : EuclideanSpace ℝ I}

def dyadicBeta (α R : ℝ) (j : ℕ) : ℝ := beta α (-Real.log (radius R j))

theorem radius_le {R : ℝ} (hR : 0 ≤ R) (j : ℕ) : radius R j ≤ R := by
  simpa only [radius, pow_zero, div_one] using radius_antitone hR (Nat.zero_le j)

theorem dyadicBeta_pos {α R : ℝ} (hα : 0 < α) (hR : 0 < R)
    (hsmall : 2 * R ≤ Real.exp (-2)) (j : ℕ) : 0 < dyadicBeta α R j := by
  have hs : radius R j < 1 := (radius_le hR.le j).trans_lt
    (by have h := Real.exp_lt_one_iff.mpr (by norm_num : (-2 : ℝ) < 0); linarith)
  exact beta_pos hα (neg_pos.mpr (Real.log_neg (radius_pos hR j) hs))

theorem dyadicBeta_le_one {α R : ℝ} (hα : 0 < α)
    (hR : 0 < R) (hsmall : 2 * R ≤ Real.exp (-2)) (j : ℕ) : dyadicBeta α R j ≤ 1 := by
  have hs : radius R j ≤ Real.exp (-2) := by linarith [radius_le hR.le j]
  have ht := Real.log_le_log (radius_pos hR j) hs
  rw [Real.log_exp] at ht
  exact beta_le_one hα (by linarith)

private theorem exp_sq (z : ℝ) : Real.exp z ^ 2 = Real.exp (2*z) := by
  rw [sq, ← Real.exp_add]
  congr 1
  ring

theorem zero_coefficient_on_annulus {R τ α : ℝ} (hR : 0 < R)
    (hsmall : 2*R ≤ Real.exp (-2)) (hτ : 1 ≤ τ) (hα : 0 < α) (hαR : R ≤ Real.exp (-(4 * α + 2)))
    (j : ℕ) (x : EuclideanSpace ℝ I) (hx : x ∈ dyadicAnnulus O R j) :
    coefficient τ (dyadicBeta α R j) (radius R j) 0 *
        Real.exp (τ * weight α (-Real.log (dist x O))) ^ 2 ≤
      32 * max 0 (massWeight τ α (x-O)) := by
  have hrj := radius_pos hR j
  have hr : 0 < dist x O := by have h := hx.1; linarith
  have hlog := (annulus_log_bound hR hsmall j hx).2
  have hb := (beta_pos hα (by linarith : 0 < -Real.log (dist x O))).le
  have hcomp := (beta_annular_comparison hα ((radius_le hR.le j).trans hαR) hrj
    (by linarith [radius_le hR.le j]) hx.1 hx.2).1
  have hc := coefficient_zero_le_radial (τ := τ) (B := 8) (K := 2)
    (by linarith : 0 ≤ τ) hb (by norm_num) (by norm_num) hrj hr hcomp hx.2
  have hh := mul_le_mul_of_nonneg_right hc
    (sq_nonneg (Real.exp (τ * weight α (-Real.log (dist x O)))))
  have he : (τ^3 * beta α (-Real.log (dist x O)) / dist x O ^ 2) *
      Real.exp (τ * weight α (-Real.log (dist x O))) ^ 2 = massWeight τ α (x-O) := by
    rw [exp_sq]
    simp only [massWeight, dist_eq_norm]
    ring
  calc
    _ ≤ 32 * massWeight τ α (x-O) := by simpa only [dyadicBeta, show (8:ℝ)*2^2=32 by norm_num, mul_assoc, he] using hh
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)

theorem weighted_zero_sum (family : BufferedFamily O) {R τ α : ℝ} (hR : 0 < R)
    (hsmall : 2*R ≤ Real.exp (-2)) (hτ : 1 ≤ τ) (hα : 0 < α) (hαR : R ≤ Real.exp (-(4 * α + 2)))
    (S : Finset ℕ) (x : EuclideanSpace ℝ I) :
    (∑ j ∈ S, coefficient τ (dyadicBeta α R j) (radius R j) 0 *
      (weightedCutoff family R hR τ α j).scalar.weight x ^ 2) ≤
      96 * max 0 (massWeight τ α (x-O)) := by
  have h := sum_le_three_of_annular_bound O hR S x
    (fun j => coefficient τ (dyadicBeta α R j) (radius R j) 0 *
      (weightedCutoff family R hR τ α j).scalar.weight x ^ 2)
    (B := 32 * max 0 (massWeight τ α (x-O))) (by positivity) ?_ ?_
  · exact h.trans_eq (by ring)
  · intro j _ hx
    rw [(weightedCutoff_supported family hR τ α j x hx).1]
    simp
  · intro j _ hx
    apply (mul_le_mul_of_nonneg_left
      (show (weightedCutoff family R hR τ α j).scalar.weight x ^ 2 ≤
        Real.exp (τ * weight α (-Real.log (dist x O))) ^ 2 by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
          (weightedCutoff_weight_bound family hR hsmall τ α j x hx) 2)
      (coefficient_pos (by linarith) (dyadicBeta_pos hα hR hsmall j) (radius_pos hR j) 0).le).trans
    exact zero_coefficient_on_annulus hR hsmall hτ hα hαR j x hx

theorem weighted_source_sum (family : BufferedFamily O) {R τ α : ℝ} (hR : 0 < R)
    (hsmall : 2*R ≤ Real.exp (-2)) (hτ : 1 ≤ τ) (hα : 0 < α)
    (S : Finset ℕ) (x : EuclideanSpace ℝ I) :
    (∑ j ∈ S, coefficient τ (dyadicBeta α R j) (radius R j) 2 *
      (weightedCutoff family R hR τ α j).scalar.weight x ^ 2) ≤
      12 * sourceWeight τ α (x-O) := by
  have h := sum_le_three_of_annular_bound O hR S x
    (fun j => coefficient τ (dyadicBeta α R j) (radius R j) 2 *
      (weightedCutoff family R hR τ α j).scalar.weight x ^ 2)
    (B := 4 * sourceWeight τ α (x-O)) (by unfold sourceWeight; positivity) ?_ ?_
  · exact h.trans_eq (by ring)
  · intro j _ hx
    rw [(weightedCutoff_supported family hR τ α j x hx).1]
    simp
  · intro j _ hx
    have hrj := radius_pos hR j
    have hr : 0 < dist x O := by have h := hx.1; linarith
    have hscale : radius R j ^ 2 ≤ 4 * dist x O ^ 2 := by
      nlinarith [hx.1, sq_nonneg (2 * dist x O - radius R j)]
    have hc := (coefficient_two_le_radius_sq hτ (dyadicBeta_le_one hα hR hsmall j)).trans hscale
    have hw : (weightedCutoff family R hR τ α j).scalar.weight x ^ 2 ≤
        Real.exp (τ * weight α (-Real.log (dist x O))) ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
        (weightedCutoff_weight_bound family hR hsmall τ α j x hx) 2
    apply (mul_le_mul hc hw (sq_nonneg _) (by positivity)).trans_eq
    rw [exp_sq]
    simp only [sourceWeight, dist_eq_norm]
    ring

theorem weighted_mass_sum (family : BufferedFamily O) {R τ α : ℝ} (hR : 0 < R)
    (hsmall : 2*R ≤ Real.exp (-2)) (hτ : 1 ≤ τ) (hα : 0 < α) (hαR : R ≤ Real.exp (-(4 * α + 2)))
    (S : Finset ℕ) (x : EuclideanSpace ℝ I) :
    (∑ j ∈ S, coefficient τ (dyadicBeta α R j) (radius R j) 2 *
      (weightedCutoff family R hR τ α j).scalar.weight x ^ 2) ≤
      96 * max 0 (massWeight τ α (x-O)) := by
  apply (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right
    (coefficient_two_le_zero hτ (dyadicBeta_pos hα hR hsmall j).le (radius_pos hR j)
      (by have h := Real.exp_lt_one_iff.mpr (by norm_num : (-2:ℝ)<0)
          linarith [radius_le hR.le j])) (sq_nonneg _)).trans
  exact weighted_zero_sum family hR hsmall hτ hα hαR S x

theorem weighted_gradient_sum (family : BufferedFamily O) {R τ α : ℝ} (hR : 0 < R)
    (hsmall : 2*R ≤ Real.exp (-2)) (hτ : 1 ≤ τ) (hα : 0 < α) (hαR : R ≤ Real.exp (-(4 * α + 2)))
    (S : Finset ℕ) (x : EuclideanSpace ℝ I) :
    (∑ j ∈ S, coefficient τ (dyadicBeta α R j) (radius R j) 2 *
      (∑ i, (weightedCutoff family R hR τ α j).scalar.gradient i x ^ 2)) ≤
      (24 * (Fintype.card I : ℝ) * firstWeightConstant family ^ 2) *
        max 0 (kineticWeight τ α (x-O)) := by
  let d : ℝ := Fintype.card I
  let G := firstWeightConstant family
  have h := sum_le_three_of_annular_bound O hR S x
    (fun j => coefficient τ (dyadicBeta α R j) (radius R j) 2 *
      (∑ i, (weightedCutoff family R hR τ α j).scalar.gradient i x ^ 2))
    (B := 8*d*G^2*max 0 (kineticWeight τ α (x-O))) (by dsimp [d]; positivity) ?_ ?_
  · exact h.trans_eq (by dsimp [d, G]; ring)
  · intro j _ hx
    simp only [(weightedCutoff_supported family hR τ α j x hx).2.1,
      zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, mul_zero]
  · intro j _ hx
    let E := Real.exp (τ * weight α (-Real.log (dist x O)))
    have hrj := radius_pos hR j
    have hτpos : 0 < τ := by linarith
    have hsum : (∑ i, (weightedCutoff family R hR τ α j).scalar.gradient i x ^ 2) ≤
        d * (G*τ/radius R j*E)^2 := by
      calc
        _ ≤ ∑ _ : I, (G*τ/radius R j*E)^2 := Finset.sum_le_sum fun i _ => by
          simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
            (weightedCutoff_first_bound family hR hsmall hτ hα j x hx i) 2
        _ = _ := by simp [d]
    have hb := (beta_annular_comparison hα ((radius_le hR.le j).trans hαR) hrj
      (by linarith [radius_le hR.le j]) hx.1 hx.2).1
    have hcoef : coefficient τ (dyadicBeta α R j) (radius R j) 2 *
        (d*(G*τ/radius R j*E)^2) = d*G^2*τ*dyadicBeta α R j*E^2 := by
      rw [coefficient_two]
      field_simp <;> ring
    apply (mul_le_mul_of_nonneg_left hsum
      (coefficient_pos hτpos (dyadicBeta_pos hα hR hsmall j) hrj 2).le).trans
    rw [hcoef]
    have hb' := mul_le_mul_of_nonneg_left hb (show 0 ≤ d*G^2*τ*E^2 by dsimp [d]; positivity)
    have he : E^2 * τ * beta α (-Real.log (dist x O)) = kineticWeight τ α (x-O) := by
      dsimp [E]
      rw [exp_sq]
      simp only [kineticWeight, dist_eq_norm]
      ring
    calc
      _ ≤ 8*d*G^2*kineticWeight τ α (x-O) := by rw [← he]; dsimp only [dyadicBeta]; nlinarith only [hb']
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) (by dsimp [d]; positivity)

theorem weighted_laplacian_sum (family : BufferedFamily O) {R τ α : ℝ} (hR : 0 < R)
    (hsmall : 2*R ≤ Real.exp (-2)) (hτ : 1 ≤ τ) (hα : 0 < α) (hαR : R ≤ Real.exp (-(4 * α + 2)))
    (S : Finset ℕ) (x : EuclideanSpace ℝ I) :
    (∑ j ∈ S, coefficient τ (dyadicBeta α R j) (radius R j) 2 *
      laplacian (weightedCutoff family R hR τ α j) x ^ 2) ≤
      (96 * ((Fintype.card I : ℝ) * secondWeightConstant family)^2) *
        max 0 (massWeight τ α (x-O)) := by
  let d : ℝ := Fintype.card I
  let H := secondWeightConstant family
  have h := sum_le_three_of_annular_bound O hR S x
    (fun j => coefficient τ (dyadicBeta α R j) (radius R j) 2 *
      laplacian (weightedCutoff family R hR τ α j) x ^ 2)
    (B := 32*(d*H)^2*max 0 (massWeight τ α (x-O))) (by positivity) ?_ ?_
  · exact h.trans_eq (by dsimp [d, H]; ring)
  · intro j _ hx
    simp only [laplacian, (weightedCutoff_supported family hR τ α j x hx).2.2,
      Finset.sum_const_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
  · intro j _ hx
    let E := Real.exp (τ * weight α (-Real.log (dist x O)))
    have hrj := radius_pos hR j
    have hτpos : 0 < τ := by linarith
    have habs : |laplacian (weightedCutoff family R hR τ α j) x| ≤
        d * (H*τ^2/(radius R j)^2*E) := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      have hdiag := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
        weightedCutoff_second_bound family hR hsmall hτ hα j x hx i i
      simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hdiag
    have hsq : laplacian (weightedCutoff family R hR τ α j) x ^ 2 ≤
        (d * (H*τ^2/(radius R j)^2*E))^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) habs 2
    have hcoef : coefficient τ (dyadicBeta α R j) (radius R j) 2 *
        (d * (H*τ^2/(radius R j)^2*E))^2 =
        (d*H)^2 * (coefficient τ (dyadicBeta α R j) (radius R j) 0 * E^2) := by
      rw [coefficient_two, coefficient_zero]
      field_simp <;> ring
    apply (mul_le_mul_of_nonneg_left hsq
      (coefficient_pos hτpos (dyadicBeta_pos hα hR hsmall j) hrj 2).le).trans
    rw [hcoef]
    have hz := mul_le_mul_of_nonneg_left
      (zero_coefficient_on_annulus hR hsmall hτ hα hαR j x hx) (sq_nonneg (d*H))
    exact hz.trans_eq (by ring)

end PfHk.SmoothDyadicCutoffs
