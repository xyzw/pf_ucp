import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.LocallyFinite

/-!
Electronic localization in Step 1 of exact soft removal.

The root-mean-square operation below is differentiated at its zeros as well
as at its positive points. Nonnegative differentiable factors have zero
derivative at their zeros. This removes the apparent singularity in the
norm derivative without assuming a final Sobolev product identity.

The spatial construction starts from standard nonnegative, locally finite
one-electron square-partition data. Ordered labels and permutation averaging
give symmetric multipliers. Repeated labels are retained, with normalization
by the number of permutations, instead of selecting one representative of
each orbit.
-/

noncomputable section

namespace GptLean.ElectronicLocalization

open Finset Filter
open scoped Topology InnerProductSpace ComplexConjugate ENNReal

section RMS

variable {J E : Type*} [Fintype J]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def rms (v : J → ℝ) : ℝ := Real.sqrt (∑ j, v j ^ 2)

theorem rms_nonneg (v : J → ℝ) : 0 ≤ rms v := Real.sqrt_nonneg _

theorem rms_sq (v : J → ℝ) : rms v ^ 2 = ∑ j, v j ^ 2 :=
  Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)

theorem rms_eq_norm (v : J → ℝ) :
    rms v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ J)‖ := by
  simp [rms, EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs]

theorem rms_eq_zero_iff (v : J → ℝ) : rms v = 0 ↔ ∀ j, v j = 0 := by
  rw [rms_eq_norm, norm_eq_zero]
  exact ⟨fun h j => congrArg (fun w : EuclideanSpace ℝ J => w j) h,
    fun h => by ext j; exact h j⟩

def rmsDerivative (g : J → E → ℝ) (x : E) : E →L[ℝ] ℝ :=
  (rms (fun j => g j x))⁻¹ • ∑ j, g j x • fderiv ℝ (g j) x

theorem rmsDerivative_apply (g : J → E → ℝ) (x v : E) :
    rmsDerivative g x v =
      (∑ j, g j x * fderiv ℝ (g j) x v) / rms (fun j => g j x) := by
  simp [rmsDerivative, div_eq_mul_inv, mul_comm]

omit [Fintype J] in
/-- A nonnegative differentiable scalar has zero derivative at every zero. -/
theorem fderiv_eq_zero_of_nonneg {f : E → ℝ} (hf : ∀ y, 0 ≤ f y)
    {x : E} (hx : f x = 0) : fderiv ℝ f x = 0 := by
  apply IsLocalMin.fderiv_eq_zero
  exact Filter.Eventually.of_forall fun y => by simpa [hx] using hf y

omit [Fintype J] in
/-- Norms of zero-valued maps with zero derivative have derivative zero. -/
theorem hasFDerivAt_norm_of_zero {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} {x : E}
    (hf : HasFDerivAt f (0 : E →L[ℝ] F) x) (hx : f x = 0) :
    HasFDerivAt (fun y => ‖f y‖) (0 : E →L[ℝ] ℝ) x := by
  rw [hasFDerivAt_iff_tendsto] at hf ⊢
  simpa [hx] using hf

/-- The RMS derivative formula is valid everywhere, including its zero set. -/
theorem rms_hasFDerivAt (g : J → E → ℝ)
    (hg : ∀ j, Differentiable ℝ (g j)) (hpos : ∀ j y, 0 ≤ g j y) (x : E) :
    HasFDerivAt (fun y => rms (fun j => g j y)) (rmsDerivative g x) x := by
  classical
  by_cases hz : rms (fun j => g j x) = 0
  · have hgzero := (rms_eq_zero_iff _).mp hz
    have hd : ∀ j, fderiv ℝ (g j) x = 0 := fun j =>
      fderiv_eq_zero_of_nonneg (hpos j) (hgzero j)
    have hv : HasFDerivAt (fun y => WithLp.toLp 2 (fun j => g j y))
        (0 : E →L[ℝ] EuclideanSpace ℝ J) x := by
      have hp := (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 (fun j => g j x)).comp x
        (hasFDerivAt_pi.mpr (fun j => (hg j x).hasFDerivAt))
      change HasFDerivAt (WithLp.toLp 2 ∘ fun y j => g j y) 0 x
      apply hp.congr_fderiv
      ext v j
      simp [hd]
    have hvzero : (WithLp.toLp 2 (fun j => g j x) : EuclideanSpace ℝ J) = 0 := by
      ext j
      exact hgzero j
    rw [show rmsDerivative g x = 0 by simp [rmsDerivative, hz]]
    simpa only [rms_eq_norm] using
      hasFDerivAt_norm_of_zero hv hvzero
  · have hs : (∑ j, g j x ^ 2) ≠ 0 := by
      intro h
      exact hz (by simp [rms, h])
    have hd := (HasFDerivAt.fun_sum (fun j (_ : j ∈ univ) =>
      (hg j x).hasFDerivAt.pow 2)).sqrt hs
    apply hd.congr_fderiv
    ext v
    simp only [smul_apply, _root_.sum_apply,
      Nat.reduceSub, pow_one, nsmul_eq_mul, Nat.cast_ofNat, smul_eq_mul,
      rmsDerivative_apply, rms]
    rw [show (∑ j, 2 * g j x * fderiv ℝ (g j) x v) =
      2 * ∑ j, g j x * fderiv ℝ (g j) x v by
        rw [mul_sum]; apply sum_congr rfl; intro j _; ring]
    field_simp

theorem rms_mul_derivative (g : J → E → ℝ) (x v : E) :
    rms (fun j => g j x) * rmsDerivative g x v =
      ∑ j, g j x * fderiv ℝ (g j) x v := by
  by_cases hz : rms (fun j => g j x) = 0
  · have hgzero := (rms_eq_zero_iff _).mp hz
    rw [hz, zero_mul]
    simp [hgzero]
  · rw [rmsDerivative_apply]
    field_simp

/-- The norm-gradient bound also holds at zero, with the explicit zero derivative. -/
theorem rms_derivative_sq_le (g : J → E → ℝ) (x v : E) :
    rmsDerivative g x v ^ 2 ≤ ∑ j, fderiv ℝ (g j) x v ^ 2 := by
  by_cases hz : rms (fun j => g j x) = 0
  · simp only [rmsDerivative, hz, inv_zero, zero_smul, zero_apply,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact sum_nonneg fun _ _ => sq_nonneg _
  · have hs : 0 < ∑ j, g j x ^ 2 := by
      rw [← rms_sq]
      exact sq_pos_of_ne_zero hz
    rw [rmsDerivative_apply, div_pow, rms_sq, div_le_iff₀ hs]
    exact (sum_mul_sq_le_sq_mul_sq univ _ _).trans_eq (mul_comm _ _)

end RMS

section CountablePartition

variable {A E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- Local finiteness supplies one finite set containing every active label
throughout a neighborhood, so derivatives vanish outside the same set. -/
theorem exists_local_active_finset (f : A → E → ℝ)
    (hf : LocallyFinite (fun a => Function.support (f a))) (x : E) :
    ∃ s : Finset A, ∀ᶠ y in 𝓝 x, ∀ a ∉ s, f a y = 0 := by
  classical
  obtain ⟨U, hU, hfin⟩ := hf x
  refine ⟨hfin.toFinset, Filter.eventually_of_mem hU ?_⟩
  intro y hy a ha
  by_contra h
  apply ha
  exact hfin.mem_toFinset.mpr ⟨y, h, hy⟩

/-- Differentiating the locally finite square partition derives its zero
connection. No differentiated partition identity is an input. -/
theorem square_partition_connection (f : A → E → ℝ)
    (hf : LocallyFinite (fun a => Function.support (f a)))
    (hd : ∀ a, Differentiable ℝ (f a))
    (hsq : ∀ x, HasSum (fun a => f a x ^ 2) 1) (x v : E) :
    HasSum (fun a => f a x * fderiv ℝ (f a) x v) 0 := by
  classical
  obtain ⟨s, hs⟩ := exists_local_active_finset f hf x
  have hx := hs.self_of_nhds
  have hsum : (fun y => ∑ a ∈ s, f a y ^ 2) =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
    filter_upwards [hs] with y hy
    exact (hasSum_sum_of_ne_finset_zero (fun a ha => by rw [hy a ha]; norm_num)).unique
      (hsq y)
  have hdf := HasFDerivAt.fun_sum (fun a (_ : a ∈ s) => (hd a x).hasFDerivAt.pow 2)
  have hzero : fderiv ℝ (fun y => ∑ a ∈ s, f a y ^ 2) x = 0 := by
    rw [hsum.fderiv_eq, fderiv_const_apply]
  have heq := congrArg (fun L : E →L[ℝ] ℝ => L v) (hdf.fderiv.symm.trans hzero)
  simp only [_root_.sum_apply, smul_apply,
    Nat.reduceSub, pow_one, nsmul_eq_mul, Nat.cast_ofNat, smul_eq_mul,
    zero_apply] at heq
  have hcross : ∑ a ∈ s, f a x * fderiv ℝ (f a) x v = 0 := by
    have hfactor : (∑ a ∈ s, 2 * f a x * fderiv ℝ (f a) x v) =
        2 * ∑ a ∈ s, f a x * fderiv ℝ (f a) x v := by
      rw [mul_sum]; apply sum_congr rfl; intro a _; ring
    rw [hfactor] at heq
    linarith
  rw [← hcross]
  exact hasSum_sum_of_ne_finset_zero fun a ha => by rw [hx a ha, zero_mul]

end CountablePartition

end GptLean.ElectronicLocalization
