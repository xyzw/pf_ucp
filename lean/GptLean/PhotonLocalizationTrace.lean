import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
Trace compression and finite-dimensional corners for photon localization.

Adapted from `claude_lean/QEDFT/PhotonLoss/GentleMeasurement.lean`.
The positive functional represents `a ↦ Tr(a Γ)`. Its dual norm is the
trace norm in the normal-state realization. Compression, its factor-two
norm bound, and precompactness of finite-dimensional corners are proved.
Only the identification with physical normal trace-class states remains
standard operator background. No localization or compactness estimate is
assumed here.
-/

namespace GptLean.PhotonTrace

open scoped ComplexOrder

/-! ### Pure ⋆-algebra identities -/

section Algebra

variable {A : Type*} [Ring A] [StarRing A]

theorem star_mul_proj_mul {T : A} (hT : IsStarProjection T) (c : A) :
    star c * T * c = star (T * c) * (T * c) := by
  have h : T * (T * c) = T * c := by rw [← mul_assoc, hT.isIdempotentElem.eq]
  rw [star_mul, hT.isSelfAdjoint.star_eq, mul_assoc, mul_assoc, h]

theorem two_conj_add_two_conj_sub (T a b : A) :
    2 • (star a * T * a) + 2 • (star b * T * b) - star (a + b) * T * (a + b)
      = star (a - b) * T * (a - b) := by
  simp only [star_add, star_sub]
  noncomm_ring

theorem star_one_sub_mul_self_of_commute {P ζ : A} (hP : IsStarProjection P)
    (hζ : IsSelfAdjoint ζ) (hc : Commute ζ P) :
    star (1 - ζ * P) * (1 - ζ * P) = (1 - P) + P * (1 - ζ) ^ 2 := by
  have h1 : ζ * P = P * ζ := hc.eq
  have h2 : P * ζ * (P * ζ) = P * ζ * ζ := by
    calc P * ζ * (P * ζ) = P * (ζ * P) * ζ := by noncomm_ring
      _ = P * P * ζ * ζ := by rw [h1]; noncomm_ring
      _ = P * ζ * ζ := by rw [hP.isIdempotentElem.eq]
  rw [star_sub, star_one, star_mul, hP.isSelfAdjoint.star_eq, hζ.star_eq, h1]
  calc (1 - P * ζ) * (1 - P * ζ) = 1 - P * ζ - P * ζ + P * ζ * (P * ζ) := by noncomm_ring
    _ = 1 - P * ζ - P * ζ + P * ζ * ζ := by rw [h2]
    _ = (1 - P) + P * (1 - ζ) ^ 2 := by noncomm_ring

theorem proj_mul_one_sub_sq_of_commute {P ζ : A} (hζ : IsSelfAdjoint ζ) (hc : Commute ζ P) :
    P * (1 - ζ) ^ 2 = star (1 - ζ) * P * (1 - ζ) := by
  have h : Commute (1 - ζ) P := (Commute.one_left P).sub_left hc
  rw [star_sub, star_one, hζ.star_eq, h.eq, sq, mul_assoc]

end Algebra

/-! ### Positive functionals on a C⋆-algebra -/

variable {A : Type*} [CStarAlgebra A]

/-- Positivity of the trace functional on squares. -/
def IsPosFunctional (φ : A →L[ℂ] ℂ) : Prop := ∀ a : A, 0 ≤ φ (star a * a)

/-- The operator corner map `a ↦ S a S`. -/
noncomputable def comprMap (S : A) : A →L[ℂ] A := ContinuousLinearMap.mulLeftRight ℂ A S S

/-- Dual representation of the actual state compression `S Γ S`. -/
noncomputable def compr (S : A) (φ : A →L[ℂ] ℂ) : A →L[ℂ] ℂ := φ.comp (comprMap S)

@[simp] theorem comprMap_apply (S a : A) : comprMap S a = S * a * S := rfl

@[simp] theorem compr_apply (S : A) (φ : A →L[ℂ] ℂ) (a : A) : compr S φ a = φ (S * a * S) := rfl

namespace IsPosFunctional

variable {φ : A →L[ℂ] ℂ}

theorem re_nonneg (hφ : IsPosFunctional φ) (a : A) : 0 ≤ (φ (star a * a)).re :=
  (Complex.nonneg_iff.mp (hφ a)).1

theorem im_eq_zero (hφ : IsPosFunctional φ) (a : A) : (φ (star a * a)).im = 0 :=
  (Complex.nonneg_iff.mp (hφ a)).2.symm

theorem one_nonneg (hφ : IsPosFunctional φ) : 0 ≤ φ 1 := by
  simpa using hφ 1

theorem one_re_nonneg (hφ : IsPosFunctional φ) : 0 ≤ (φ 1).re :=
  (Complex.nonneg_iff.mp hφ.one_nonneg).1

theorem conj_proj_re_nonneg (hφ : IsPosFunctional φ) {T : A} (hT : IsStarProjection T) (c : A) :
    0 ≤ (φ (star c * T * c)).re := by
  rw [star_mul_proj_mul hT]
  exact hφ.re_nonneg _

theorem proj_re_nonneg (hφ : IsPosFunctional φ) {T : A} (hT : IsStarProjection T) :
    0 ≤ (φ T).re := by
  simpa using hφ.conj_proj_re_nonneg hT 1

theorem conj_proj_re_le (hφ : IsPosFunctional φ) {T : A} (hT : IsStarProjection T) (a : A) :
    (φ (star a * T * a)).re ≤ (φ (star a * a)).re := by
  have h := hφ.conj_proj_re_nonneg hT.one_sub a
  have e : star a * (1 - T) * a = star a * a - star a * T * a := by noncomm_ring
  rw [e, map_sub, Complex.sub_re] at h
  linarith

theorem compr (hφ : IsPosFunctional φ) {S : A} (hS : IsSelfAdjoint S) :
    IsPosFunctional (compr S φ) := fun a => by
  have e : S * (star a * a) * S = star (a * S) * (a * S) := by
    rw [star_mul, hS.star_eq]; noncomm_ring
  rw [compr_apply, e]
  exact hφ _

theorem conj_add_re_le (hφ : IsPosFunctional φ) {T : A} (hT : IsStarProjection T) (a b : A) :
    (φ (star (a + b) * T * (a + b))).re
      ≤ 2 * (φ (star a * T * a)).re + 2 * (φ (star b * T * b)).re := by
  have h := hφ.conj_proj_re_nonneg hT (a - b)
  rw [← two_conj_add_two_conj_sub, map_sub, map_add, map_nsmul, map_nsmul] at h
  simp only [Complex.sub_re, Complex.add_re, nsmul_eq_mul, Nat.cast_ofNat, Complex.mul_re,
    Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero] at h
  linarith

theorem one_sub_proj_re_le (hφ : IsPosFunctional φ) {S : A} (hS : IsStarProjection S) (X : A) :
    (φ (1 - S)).re
      ≤ 2 * (φ (star (1 - X) * (1 - X))).re + 2 * (φ (star X * (1 - S) * X)).re := by
  have h := hφ.conj_add_re_le hS.one_sub (1 - X) X
  have h' := hφ.conj_proj_re_le hS.one_sub (1 - X)
  rw [sub_add_cancel, star_one, one_mul, mul_one] at h
  linarith

theorem one_sub_cutoff_re_le (hφ : IsPosFunctional φ) {P ζ : A} (hP : IsStarProjection P)
    (hζ : IsSelfAdjoint ζ) (hc : Commute ζ P) :
    (φ (star (1 - ζ * P) * (1 - ζ * P))).re ≤ (φ (1 - P)).re + (φ ((1 - ζ) ^ 2)).re := by
  have h := hφ.conj_proj_re_le hP (1 - ζ)
  rw [← proj_mul_one_sub_sq_of_commute hζ hc] at h
  have e : star (1 - ζ) * (1 - ζ) = (1 - ζ) ^ 2 := by rw [star_sub, star_one, hζ.star_eq, sq]
  rw [e] at h
  rw [star_one_sub_mul_self_of_commute hP hζ hc, map_add, Complex.add_re]
  linarith

variable [PartialOrder A] [StarOrderedRing A]

theorem map_nonneg (hφ : IsPosFunctional φ) {a : A} (ha : 0 ≤ a) : 0 ≤ φ a := by
  obtain ⟨b, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha
  exact hφ b

noncomputable def toPLM (hφ : IsPosFunctional φ) : A →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ φ.toLinearMap fun _ h => hφ.map_nonneg h

theorem cauchy_schwarz (hφ : IsPosFunctional φ) (x y : A) :
    ‖φ (star x * y)‖ ≤ √(φ (star x * x)).re * √(φ (star y * y)).re := by
  have h := PositiveLinearMap.norm_map_star_mul_le hφ.toPLM x y
  have hx : ‖φ (star x * x)‖ = (φ (star x * x)).re := (Complex.re_eq_norm.mpr (hφ x)).symm
  have hy : ‖φ (star y * y)‖ = (φ (star y * y)).re := (Complex.re_eq_norm.mpr (hφ y)).symm
  rw [← hx, ← hy]
  exact h

theorem star_mul_self_re_le (hφ : IsPosFunctional φ) (a : A) :
    (φ (star a * a)).re ≤ ‖a‖ ^ 2 * (φ 1).re := by
  have h := PositiveLinearMap.norm_apply_le_of_nonneg hφ.toPLM (star a * a) (star_mul_self_nonneg a)
  have h1 : ‖φ 1‖ = (φ 1).re := (Complex.re_eq_norm.mpr hφ.one_nonneg).symm
  have h2 : ‖φ (star a * a)‖ = (φ (star a * a)).re := (Complex.re_eq_norm.mpr (hφ a)).symm
  have h3 : ‖hφ.toPLM (star a * a)‖ ≤ ‖hφ.toPLM 1‖ * ‖star a * a‖ := h
  change ‖φ (star a * a)‖ ≤ ‖φ 1‖ * ‖star a * a‖ at h3
  rw [h1, h2, CStarRing.norm_star_mul_self] at h3
  nlinarith [h3]

theorem norm_apply_le (hφ : IsPosFunctional φ) (a : A) : ‖φ a‖ ≤ ‖a‖ * (φ 1).re := by
  have h := hφ.cauchy_schwarz 1 a
  simp only [star_one, one_mul] at h
  refine h.trans ?_
  calc √(φ 1).re * √(φ (star a * a)).re
      ≤ √(φ 1).re * √(‖a‖ ^ 2 * (φ 1).re) := by
        gcongr; exact hφ.star_mul_self_re_le a
    _ = ‖a‖ * (φ 1).re := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg a), mul_comm, mul_assoc,
          Real.mul_self_sqrt hφ.one_re_nonneg]

theorem opNorm_le (hφ : IsPosFunctional φ) : ‖φ‖ ≤ (φ 1).re :=
  φ.opNorm_le_bound hφ.one_re_nonneg fun a => by rw [mul_comm]; exact hφ.norm_apply_le a

theorem opNorm_eq (hφ : IsPosFunctional φ) : ‖φ‖ = (φ 1).re := by
  refine le_antisymm hφ.opNorm_le ?_
  rcases subsingleton_or_nontrivial A with hA | hA
  · rw [Subsingleton.elim (1 : A) 0, map_zero, Complex.zero_re]
    exact norm_nonneg φ
  · calc (φ 1).re ≤ ‖φ 1‖ := Complex.re_le_norm _
      _ ≤ ‖φ‖ * ‖(1 : A)‖ := φ.le_opNorm 1
      _ = ‖φ‖ := by rw [CStarRing.norm_one, mul_one]

/-- The homogeneous gentle-compression bound follows from positivity
and Cauchy–Schwarz, without a trace compression estimate as a premise. -/
theorem norm_sub_compr_le (hφ : IsPosFunctional φ) {S : A} (hS : IsStarProjection S) :
    ‖φ - GptLean.PhotonTrace.compr S φ‖ ≤ 2 * √((φ 1).re * (φ (1 - S)).re) := by
  have h1 := hφ.one_re_nonneg
  have hT := hφ.proj_re_nonneg hS.one_sub
  have hTT : star (1 - S) * (1 - S) = 1 - S := by
    rw [hS.one_sub.isSelfAdjoint.star_eq, hS.one_sub.isIdempotentElem.eq]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun a => ?_
  have e : (φ - GptLean.PhotonTrace.compr S φ) a
      = φ (star (1 - S) * a) + φ (star (star a * S) * (1 - S)) := by
    rw [sub_apply, compr_apply, ← map_sub, ← map_add, star_mul, star_star,
      hS.isSelfAdjoint.star_eq, hS.one_sub.isSelfAdjoint.star_eq]
    congr 1
    noncomm_ring
  -- first term: `|φ((1-S)a)| ≤ φ(1-S)^{1/2} ‖a‖ φ(1)^{1/2}`
  have t1 : ‖φ (star (1 - S) * a)‖ ≤ ‖a‖ * (√(φ 1).re * √(φ (1 - S)).re) := by
    refine (hφ.cauchy_schwarz (1 - S) a).trans ?_
    rw [hTT]
    calc √(φ (1 - S)).re * √(φ (star a * a)).re
        ≤ √(φ (1 - S)).re * √(‖a‖ ^ 2 * (φ 1).re) := by
          gcongr; exact hφ.star_mul_self_re_le a
      _ = ‖a‖ * (√(φ 1).re * √(φ (1 - S)).re) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg a)]; ring
  -- second term: `|φ(Sa(1-S))| ≤ φ(S a a⋆ S)^{1/2} φ(1-S)^{1/2}` and `φ(S a a⋆ S) ≤ ‖a‖² φ(S)`
  have t2 : ‖φ (star (star a * S) * (1 - S))‖ ≤ ‖a‖ * (√(φ 1).re * √(φ (1 - S)).re) := by
    refine (hφ.cauchy_schwarz (star a * S) (1 - S)).trans ?_
    rw [hTT]
    have hc := (hφ.compr hS.isSelfAdjoint).star_mul_self_re_le (star a)
    have e2 : star (star a * S) * (star a * S) = S * (star (star a) * star a) * S := by
      rw [star_mul, hS.isSelfAdjoint.star_eq]; noncomm_ring
    rw [compr_apply, compr_apply, ← e2, mul_one, hS.isIdempotentElem.eq, norm_star] at hc
    have hS1 : (φ S).re ≤ (φ 1).re := by
      have : (φ (1 - S)).re = (φ 1).re - (φ S).re := by rw [map_sub, Complex.sub_re]
      linarith
    calc √(φ (star (star a * S) * (star a * S))).re * √(φ (1 - S)).re
        ≤ √(‖a‖ ^ 2 * (φ 1).re) * √(φ (1 - S)).re := by
          gcongr
          exact hc.trans (by gcongr)
      _ = ‖a‖ * (√(φ 1).re * √(φ (1 - S)).re) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg a)]; ring
  rw [e, Real.sqrt_mul h1]
  calc ‖φ (star (1 - S) * a) + φ (star (star a * S) * (1 - S))‖
      ≤ ‖φ (star (1 - S) * a)‖ + ‖φ (star (star a * S) * (1 - S))‖ := norm_add_le _ _
    _ ≤ 2 * (√(φ 1).re * √(φ (1 - S)).re) * ‖a‖ := by linarith

theorem norm_sub_compr_le_of_le_one (hφ : IsPosFunctional φ) (h1 : (φ 1).re ≤ 1) {S : A}
    (hS : IsStarProjection S) :
    ‖φ - GptLean.PhotonTrace.compr S φ‖ ≤ 2 * √(φ (1 - S)).re := by
  refine (hφ.norm_sub_compr_le hS).trans ?_
  gcongr
  exact mul_le_of_le_one_left (hφ.proj_re_nonneg hS.one_sub) h1

end IsPosFunctional

/-! ### Finite-rank projections and precompactness of the compressions -/

/-- Finite-dimensional operator corner of an orthogonal projection.
For bounded Hilbert-space operators this is the usual finite-rank condition. -/
structure IsFiniteRankProj (S : A) : Prop where
  
  isStarProjection : IsStarProjection S
  
  finiteDimensional : FiniteDimensional ℂ (LinearMap.range (comprMap S).toLinearMap)

variable [PartialOrder A] [StarOrderedRing A]

theorem totallyBounded_compr {S : A} (hS : IsFiniteRankProj S) :
    TotallyBounded {ψ : A →L[ℂ] ℂ | ∃ φ, IsPosFunctional φ ∧ (φ 1).re ≤ 1 ∧ ψ = compr S φ} := by
  set V := LinearMap.range (comprMap S).toLinearMap
  have : FiniteDimensional ℂ V := hS.finiteDimensional
  let c : A →L[ℂ] V := (comprMap S).codRestrict V fun x => LinearMap.mem_range_self _ x
  have : ProperSpace (V →L[ℂ] ℂ) := FiniteDimensional.proper_rclike ℂ (V →L[ℂ] ℂ)
  have hK : TotallyBounded (Metric.closedBall (0 : V →L[ℂ] ℂ) 1) :=
    (isCompact_closedBall _ _).totallyBounded
  refine (hK.image (ContinuousLinearMap.precomp ℂ c).uniformContinuous).subset ?_
  rintro ψ ⟨φ, hφ, h1, rfl⟩
  refine ⟨φ.comp V.subtypeL, ?_, ?_⟩
  · have hn : ‖φ.comp V.subtypeL‖ ≤ 1 :=
      calc ‖φ.comp V.subtypeL‖ ≤ ‖φ‖ * ‖V.subtypeL‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ 1 * 1 := by
            gcongr
            · exact hφ.opNorm_le.trans h1
            · exact V.norm_subtypeL_le
        _ = 1 := one_mul 1
    exact (mem_closedBall_zero_iff (a := φ.comp V.subtypeL) (r := 1)).mpr hn
  · ext a
    rfl

end GptLean.PhotonTrace
