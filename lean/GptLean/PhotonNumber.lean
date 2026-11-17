import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.Real.Sqrt

/-!
Adapted from `claude_lean/QEDFT/PhotonLoss/NumberStatistics.lean`.

The countable joint-law argument remains valid in the current proof of
`thm-continuum-compactness`. It proves the
probability of discarding photons is bounded by a retained-sector tail
plus 2^(M+1) times the drop of the expectation of 2^(-photon number).
It needs no bound on mean photon number.

All sums, summability conditions, marginal identities, Markov inequalities,
and the square-root estimate are proved here. Identifying the joint law
with the actual geometric-localization dilation remains a standard Fock
input. Trace-norm compactness and the sharp energy estimate are not
asserted by this module.
-/




namespace GptLean
namespace PhotonLoss

open Finset




theorem two_pow_weight_lower_bound {a b M : ℕ} (ha : a ≤ M) (hb : 1 ≤ b) :
    (1 / 2 : ℝ) ^ (M + 1) ≤ (1 / 2 : ℝ) ^ a * (1 - (1 / 2 : ℝ) ^ b) := by
  have hA : (1 / 2 : ℝ) ^ M ≤ (1 / 2 : ℝ) ^ a :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) ha
  have hB : (1 / 2 : ℝ) ^ b ≤ (1 / 2 : ℝ) ^ 1 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hb
  have hM : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ M := by positivity
  calc (1 / 2 : ℝ) ^ (M + 1) = (1 / 2 : ℝ) ^ M * (1 / 2) := by rw [pow_succ]
    _ ≤ (1 / 2 : ℝ) ^ a * (1 - (1 / 2 : ℝ) ^ b) :=
        mul_le_mul hA (by linarith) (by norm_num) (hM.trans hA)


theorem indicator_discard_le (a b M : ℕ) :
    (if 1 ≤ b then (1 : ℝ) else 0)
      ≤ (if M < a then (1 : ℝ) else 0)
        + 2 ^ (M + 1) * ((1 / 2 : ℝ) ^ a * (1 - (1 / 2 : ℝ) ^ b)) := by
  have hb1 : (1 / 2 : ℝ) ^ b ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hw : 0 ≤ (2 : ℝ) ^ (M + 1) * ((1 / 2 : ℝ) ^ a * (1 - (1 / 2 : ℝ) ^ b)) :=
    mul_nonneg (by positivity) (mul_nonneg (by positivity) (by linarith))
  by_cases hb : 1 ≤ b
  · by_cases ha : M < a
    · simp only [hb, ha, ite_true]; linarith
    · have h := two_pow_weight_lower_bound (not_lt.mp ha) hb
      have h2 : (2 : ℝ) ^ (M + 1) * (1 / 2 : ℝ) ^ (M + 1) = 1 := by
        rw [← mul_pow]; norm_num
      have h3 : (2 : ℝ) ^ (M + 1) * (1 / 2 : ℝ) ^ (M + 1)
          ≤ 2 ^ (M + 1) * ((1 / 2 : ℝ) ^ a * (1 - (1 / 2 : ℝ) ^ b)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
      simp only [hb, ha, ite_true, ite_false]; linarith
  · simp only [hb, ite_false]
    split_ifs <;> linarith



variable (p : ℕ × ℕ → ℝ)


noncomputable def discardProb : ℝ := ∑' x : ℕ × ℕ, if 1 ≤ x.2 then p x else 0


noncomputable def tailIn (M : ℕ) : ℝ := ∑' x : ℕ × ℕ, if M < x.1 then p x else 0


noncomputable def tailTot (M : ℕ) : ℝ := ∑' x : ℕ × ℕ, if M < x.1 + x.2 then p x else 0


noncomputable def bIn : ℝ := ∑' x : ℕ × ℕ, (1 / 2 : ℝ) ^ x.1 * p x


noncomputable def bTot : ℝ := ∑' x : ℕ × ℕ, (1 / 2 : ℝ) ^ (x.1 + x.2) * p x


noncomputable def nIn (k : ℕ) : ℝ := ∑' b : ℕ, p (k, b)


noncomputable def nTot (k : ℕ) : ℝ := ∑ x ∈ antidiagonal k, p x

variable {p}


theorem summable_weight_mul (hp : ∀ x, 0 ≤ p x) (hs : Summable p) {w : ℕ × ℕ → ℝ}
    (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1) : Summable fun x => w x * p x :=
  Summable.of_nonneg_of_le (fun x => mul_nonneg (hw0 x) (hp x))
    (fun x => by simpa using mul_le_mul_of_nonneg_right (hw1 x) (hp x)) hs


theorem summable_ite (hp : ∀ x, 0 ≤ p x) (hs : Summable p) (S : ℕ × ℕ → Prop)
    [DecidablePred S] : Summable fun x => if S x then p x else 0 :=
  Summable.of_nonneg_of_le (fun x => by split_ifs <;> simp [hp x])
    (fun x => by split_ifs <;> simp [hp x]) hs


theorem summable_bIn (hp : ∀ x, 0 ≤ p x) (hs : Summable p) :
    Summable fun x : ℕ × ℕ => (1 / 2 : ℝ) ^ x.1 * p x :=
  summable_weight_mul hp hs (fun _ => by positivity)
    (fun _ => pow_le_one₀ (by norm_num) (by norm_num))


theorem summable_bTot (hp : ∀ x, 0 ≤ p x) (hs : Summable p) :
    Summable fun x : ℕ × ℕ => (1 / 2 : ℝ) ^ (x.1 + x.2) * p x :=
  summable_weight_mul hp hs (fun _ => by positivity)
    (fun _ => pow_le_one₀ (by norm_num) (by norm_num))


theorem bIn_sub_bTot_eq (hp : ∀ x, 0 ≤ p x) (hs : Summable p) :
    bIn p - bTot p = ∑' x : ℕ × ℕ, (1 / 2 : ℝ) ^ x.1 * (1 - (1 / 2 : ℝ) ^ x.2) * p x := by
  unfold bIn bTot
  rw [← (summable_bIn hp hs).tsum_sub (summable_bTot hp hs)]
  refine tsum_congr fun x => ?_
  rw [pow_add]; ring


theorem bIn_sub_bTot_nonneg (hp : ∀ x, 0 ≤ p x) (hs : Summable p) : 0 ≤ bIn p - bTot p := by
  rw [bIn_sub_bTot_eq hp hs]
  refine tsum_nonneg fun x => ?_
  have h1 : (1 / 2 : ℝ) ^ x.2 ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  exact mul_nonneg (mul_nonneg (by positivity) (by linarith)) (hp x)


theorem bTot_nonneg (hp : ∀ x, 0 ≤ p x) : 0 ≤ bTot p :=
  tsum_nonneg fun x => mul_nonneg (by positivity) (hp x)


theorem bIn_le_one (hp : ∀ x, 0 ≤ p x) (hs : Summable p) (h1 : ∑' x, p x = 1) : bIn p ≤ 1 := by
  rw [← h1]
  refine (summable_bIn hp hs).tsum_le_tsum (fun x => ?_) hs
  simpa using mul_le_mul_of_nonneg_right
    (pow_le_one₀ (by norm_num) (by norm_num) : (1 / 2 : ℝ) ^ x.1 ≤ 1) (hp x)


theorem discardProb_nonneg (hp : ∀ x, 0 ≤ p x) : 0 ≤ discardProb p :=
  tsum_nonneg fun x => by split_ifs <;> simp [hp x]


theorem discardProb_le_one (hp : ∀ x, 0 ≤ p x) (hs : Summable p) (h1 : ∑' x, p x = 1) :
    discardProb p ≤ 1 := by
  rw [← h1]
  exact (summable_ite hp hs _).tsum_le_tsum (fun x => by split_ifs <;> simp [hp x]) hs


theorem discardProb_le (hp : ∀ x, 0 ≤ p x) (hs : Summable p) (M : ℕ) :
    discardProb p ≤ tailIn p M + 2 ^ (M + 1) * (bIn p - bTot p) := by
  have hsw : Summable fun x : ℕ × ℕ => (1 / 2 : ℝ) ^ x.1 * (1 - (1 / 2 : ℝ) ^ x.2) * p x := by
    refine summable_weight_mul hp hs (fun x => ?_) (fun x => ?_)
    · have h1 : (1 / 2 : ℝ) ^ x.2 ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      exact mul_nonneg (by positivity) (by linarith)
    · have h1 : (1 / 2 : ℝ) ^ x.1 ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have h2 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ x.2 := by positivity
      have h3 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ x.1 := by positivity
      nlinarith
  rw [bIn_sub_bTot_eq hp hs, tailIn, discardProb, ← hsw.tsum_mul_left,
    ← (summable_ite hp hs _).tsum_add (hsw.mul_left _)]
  refine (summable_ite hp hs _).tsum_le_tsum (fun x => ?_)
    ((summable_ite hp hs _).add (hsw.mul_left _))
  have h := mul_le_mul_of_nonneg_right (indicator_discard_le x.1 x.2 M) (hp x)
  have e1 : (if 1 ≤ x.2 then p x else 0) = (if 1 ≤ x.2 then (1 : ℝ) else 0) * p x := by
    split_ifs <;> simp
  have e2 : (if M < x.1 then p x else 0) = (if M < x.1 then (1 : ℝ) else 0) * p x := by
    split_ifs <;> simp
  rw [e1, e2]
  linarith


theorem discardProb_le_of_tail_le (hp : ∀ x, 0 ≤ p x) (hs : Summable p) (M : ℕ) {δ : ℝ}
    (hδ : tailIn p M ≤ δ) : discardProb p ≤ δ + 2 ^ (M + 1) * (bIn p - bTot p) :=
  (discardProb_le hp hs M).trans (by linarith)




theorem bIn_eq_tsum_nIn (hp : ∀ x, 0 ≤ p x) (hs : Summable p) :
    bIn p = ∑' k : ℕ, (1 / 2 : ℝ) ^ k * nIn p k := by
  unfold bIn nIn
  rw [(summable_bIn hp hs).tsum_prod]
  exact tsum_congr fun k => tsum_mul_left (a := (1 / 2 : ℝ) ^ k) (f := fun b => p (k, b))


theorem tailIn_eq_tsum_nIn (hp : ∀ x, 0 ≤ p x) (hs : Summable p) (M : ℕ) :
    tailIn p M = ∑' k : ℕ, if M < k then nIn p k else 0 := by
  unfold tailIn nIn
  rw [(summable_ite hp hs fun x => M < x.1).tsum_prod]
  refine tsum_congr fun k => ?_
  by_cases h : M < k <;> simp [h]


theorem tsum_prod_eq_tsum_antidiagonal {f : ℕ × ℕ → ℝ} (hf : Summable f) :
    ∑' x, f x = ∑' k : ℕ, ∑ x ∈ antidiagonal k, f x := by
  have hf' : Summable fun y : Σ n : ℕ, antidiagonal n => f (y.2 : ℕ × ℕ) :=
    (HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).summable_iff.mpr hf
  rw [← (HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).tsum_eq f]
  rw [show (fun y : Σ n : ℕ, antidiagonal n =>
      f (HasAntidiagonal.sigmaAntidiagonalEquivProd y)) = fun y => f (y.2 : ℕ × ℕ) from rfl]
  rw [hf'.tsum_sigma' fun n => (hasSum_fintype _).summable]
  refine tsum_congr fun k => ?_
  rw [tsum_fintype]
  exact Finset.sum_coe_sort (antidiagonal k) f


theorem bTot_eq_tsum_nTot (hp : ∀ x, 0 ≤ p x) (hs : Summable p) :
    bTot p = ∑' k : ℕ, (1 / 2 : ℝ) ^ k * nTot p k := by
  unfold bTot nTot
  rw [tsum_prod_eq_tsum_antidiagonal (summable_bTot hp hs)]
  refine tsum_congr fun k => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [mem_antidiagonal.mp hx]


theorem tailTot_eq_tsum_nTot (hp : ∀ x, 0 ≤ p x) (hs : Summable p) (M : ℕ) :
    tailTot p M = ∑' k : ℕ, if M < k then nTot p k else 0 := by
  unfold tailTot nTot
  rw [tsum_prod_eq_tsum_antidiagonal (summable_ite hp hs fun x => M < x.1 + x.2)]
  refine tsum_congr fun k => ?_
  by_cases h : M < k
  · rw [ite_eq_left h]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [mem_antidiagonal.mp hx, ite_eq_left h]
  · rw [ite_eq_right h]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [mem_antidiagonal.mp hx, ite_eq_right h]


theorem tailIn_le_tailTot (hp : ∀ x, 0 ≤ p x) (hs : Summable p) (M : ℕ) :
    tailIn p M ≤ tailTot p M := by
  refine (summable_ite hp hs _).tsum_le_tsum (fun x => ?_) (summable_ite hp hs _)
  by_cases h : M < x.1
  · have h' : M < x.1 + x.2 := by omega
    simp [h, h']
  · rw [ite_eq_right h]
    split_ifs <;> simp [hp x]




theorem tail_le_mean_div {n : ℕ → ℝ} (hn : ∀ k, 0 ≤ n k)
    (hmean : Summable fun k : ℕ => (k : ℝ) * n k) (M : ℕ) :
    (∑' k : ℕ, if M < k then n k else 0) ≤ (∑' k : ℕ, (k : ℝ) * n k) / ((M : ℝ) + 1) := by
  have hM : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hpt : ∀ k : ℕ, (if M < k then n k else 0) ≤ (k : ℝ) * n k / ((M : ℝ) + 1) := by
    intro k
    by_cases h : M < k
    · rw [ite_eq_left h, le_div_iff₀ hM]
      have hk : (M : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast h
      nlinarith [hn k]
    · rw [ite_eq_right h]
      exact div_nonneg (mul_nonneg (Nat.cast_nonneg k) (hn k)) hM.le
  have hs2 : Summable fun k : ℕ => (k : ℝ) * n k / ((M : ℝ) + 1) := hmean.div_const _
  have hs1 : Summable fun k : ℕ => if M < k then n k else 0 :=
    Summable.of_nonneg_of_le (fun k => by split_ifs <;> simp [hn k]) hpt hs2
  calc (∑' k : ℕ, if M < k then n k else 0)
      ≤ ∑' k : ℕ, (k : ℝ) * n k / ((M : ℝ) + 1) := hs1.tsum_le_tsum hpt hs2
    _ = (∑' k : ℕ, (k : ℝ) * n k) / ((M : ℝ) + 1) := tsum_div_const




noncomputable def lossModulus (t : ℝ) : ℝ := 2 * √t + t


@[simp] theorem lossModulus_zero : lossModulus 0 = 0 := by simp [lossModulus]


theorem lossModulus_mono : Monotone lossModulus := fun s t hst => by
  unfold lossModulus
  have := Real.sqrt_le_sqrt hst
  linarith


theorem lossModulus_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ lossModulus t := by
  unfold lossModulus
  have := Real.sqrt_nonneg t
  linarith


theorem lossModulus_le {ε t : ℝ} (hε : 0 < ε) (ht : t ≤ 2 * min (ε ^ 2 / 32) (ε / 4)) :
    2 * √t + t ≤ ε := by
  have h1 : t ≤ (ε / 4) ^ 2 := by
    have := min_le_left (ε ^ 2 / 32) (ε / 4)
    nlinarith
  have h2 : t ≤ ε / 2 := by
    have := min_le_right (ε ^ 2 / 32) (ε / 4)
    linarith
  have h3 : √t ≤ ε / 4 := (Real.sqrt_le_left (by positivity)).mpr h1
  linarith


theorem lossModulus_discardProb_le (hp : ∀ x, 0 ≤ p x) (hs : Summable p) (M : ℕ) {ε : ℝ}
    (hε : 0 < ε) (htail : tailIn p M ≤ min (ε ^ 2 / 32) (ε / 4))
    (hb : 2 ^ (M + 1) * (bIn p - bTot p) ≤ min (ε ^ 2 / 32) (ε / 4)) :
    2 * √(discardProb p) + discardProb p ≤ ε :=
  lossModulus_le hε (by have := discardProb_le hp hs M; linarith)

end PhotonLoss
end GptLean
