import GptLean.PhysicalFockSectors
import GptLean.PhotonLocalizationPhysicalKernels
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Prod

/-!
The article's ultraviolet cutoff and arbitrary measurable real transverse
polarization frame. A frame is represented by its orthonormal completion
with the radial unit vector. The transverse projection and its invariance
under momentum reversal are derived. No parity is required of either
polarization vector.
-/

noncomputable section

namespace GptLean.PhysicalPolarization

open MeasureTheory Gaussian PhysicalFock PhotonLocalizationPhysicalKernels
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

/-- The two transverse vectors are the first two columns. The final
column is the radial direction away from the null momentum. -/
structure Frame where
  basis : FieldSpace → OrthonormalBasis (Fin 3) ℝ FieldSpace
  measurable : ∀ a, Measurable (fun k => basis k a)
  radial : ∀ k, k ≠ 0 → basis k 2 = ‖k‖⁻¹ • k

namespace Frame

variable (F : Frame)

def epsilon (k : FieldSpace) (a : Fin 2) : FieldSpace := F.basis k a.castSucc

theorem epsilon_measurable (a : Fin 2) : Measurable (fun k => F.epsilon k a) :=
  F.measurable a.castSucc

theorem epsilon_norm (k : FieldSpace) (a : Fin 2) : ‖F.epsilon k a‖ = 1 :=
  (F.basis k).orthonormal.norm_eq_one a.castSucc

theorem epsilon_component_bound (k : FieldSpace) (a : Fin 2) (i : Fin 3) :
    |F.epsilon k a i| ≤ 1 := by
  simpa only [Real.norm_eq_abs, F.epsilon_norm] using PiLp.norm_apply_le (F.epsilon k a) i

def transverseProjection (k : FieldSpace) : FieldSpace →L[ℝ] FieldSpace :=
  ∑ a : Fin 2, InnerProductSpace.rankOne ℝ (F.epsilon k a) (F.epsilon k a)

theorem transverseProjection_eq (k : FieldSpace) :
    F.transverseProjection k = ContinuousLinearMap.id ℝ FieldSpace -
      InnerProductSpace.rankOne ℝ (F.basis k 2) (F.basis k 2) := by
  have h := (F.basis k).sum_rankOne_eq_id
  rw [Fin.sum_univ_castSucc] at h
  exact eq_sub_iff_add_eq.mpr h

theorem radial_neg (k : FieldSpace) (hk : k ≠ 0) :
    F.basis (-k) 2 = -(F.basis k 2) := by
  rw [F.radial (-k) (neg_ne_zero.mpr hk), F.radial k hk, norm_neg, smul_neg]

theorem transverseProjection_neg (k : FieldSpace) (hk : k ≠ 0) :
    F.transverseProjection (-k) = F.transverseProjection k := by
  rw [F.transverseProjection_eq, F.transverseProjection_eq, F.radial_neg k hk]
  congr 1
  ext v
  simp only [InnerProductSpace.rankOne_apply, inner_neg_left, neg_smul, smul_neg, neg_neg]

theorem transverseProjection_epsilon (k : FieldSpace) (a : Fin 2) :
    F.transverseProjection k (F.epsilon k a) = F.epsilon k a := by
  rw [F.transverseProjection_eq]
  have horth : inner ℝ (F.basis k 2) (F.epsilon k a) = 0 :=
    (F.basis k).orthonormal.2 (by
      intro h
      have := congrArg Fin.val h
      have ha := a.isLt
      change 2 = a.val at this
      omega)
  simp only [sub_apply, ContinuousLinearMap.id_apply,
    InnerProductSpace.rankOne_apply, horth, zero_smul, sub_zero]

/-- Frame overlap transports transverse coordinates across momentum reversal. -/
def overlap (k : FieldSpace) (a b : Fin 2) : ℝ :=
  inner ℝ (F.epsilon k a) (F.epsilon (-k) b)

theorem overlap_reconstruction (k : FieldSpace) (hk : k ≠ 0) (a : Fin 2) :
    (∑ b : Fin 2, F.overlap k a b • F.epsilon (-k) b) = F.epsilon k a := by
  have h := congrArg (fun A : FieldSpace →L[ℝ] FieldSpace => A (F.epsilon k a))
    (F.transverseProjection_neg k hk)
  rw [F.transverseProjection_epsilon] at h
  simpa only [transverseProjection, sum_apply,
    InnerProductSpace.rankOne_apply, overlap, real_inner_comm] using h

end Frame

/-- Exactly the cutoff assumptions used in the article, at the level of
measurable representatives and their two finite moments. -/
structure ArticleCutoff where
  value : FieldSpace → ℂ
  measurable : Measurable value
  reality : ∀ᵐ k ∂volume, value k = starRingEnd ℂ (value (-k))
  ultraviolet : Integrable (fun k => ‖value k‖ ^ 2) volume
  infrared : Integrable (fun k => (1 / ‖k‖) * ‖value k‖ ^ 2) volume

variable (F : Frame) (χ : ArticleCutoff)

/-- The article uses chi(-k)/sqrt(2), with no additional frequency factor. -/
def base (i : Fin 3) (p : PhotonMode) : ℂ :=
  ((F.epsilon p.1 p.2 i : ℝ) : ℂ) * χ.value (-p.1) / (Real.sqrt 2 : ℂ)

theorem base_measurable (i : Fin 3) : Measurable (base F χ i) := by
  have he : Measurable (fun p : PhotonMode => F.epsilon p.1 p.2 i) := by
    apply measurable_from_prod_countable_left
    intro a
    exact (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).measurable.comp
      (F.epsilon_measurable a)
  exact ((Complex.measurable_ofReal.comp he).mul
    (χ.measurable.comp measurable_fst.neg)).div_const _

theorem base_norm_bound (i : Fin 3) (p : PhotonMode) :
    ‖base F χ i p‖ ^ 2 ≤ ‖χ.value (-p.1)‖ ^ 2 := by
  have hb := F.epsilon_component_bound p.1 p.2 i
  have hs : 1 ≤ Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hn : ‖base F χ i p‖ ≤ ‖χ.value (-p.1)‖ := by
    simp only [base, norm_div, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    apply (div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num))).mpr
    exact (mul_le_mul_of_nonneg_right hb (norm_nonneg _)).trans (by
      simpa only [one_mul, mul_one] using
        mul_le_mul_of_nonneg_left hs (norm_nonneg (χ.value (-p.1))))
  exact pow_le_pow_left₀ (norm_nonneg _) hn 2

theorem base_ultraviolet (i : Fin 3) :
    Integrable (fun p => ‖base F χ i p‖ ^ 2) photonMeasure := by
  have h := ((Measure.measurePreserving_neg volume).integrable_comp_of_integrable
    χ.ultraviolet).comp_fst
    (Measure.count : Measure (Fin 2))
  apply h.mono' ((base_measurable F χ i).norm.pow_const 2).aestronglyMeasurable
  exact ae_of_all _ fun p => by
    change ‖‖base F χ i p‖ ^ 2‖ ≤ ‖χ.value (-p.1)‖ ^ 2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact base_norm_bound F χ i p

theorem base_infrared (i : Fin 3) :
    Integrable (fun p => (1 / ‖p.1‖) * ‖base F χ i p‖ ^ 2) photonMeasure := by
  have h := ((Measure.measurePreserving_neg volume).integrable_comp_of_integrable
    χ.infrared).comp_fst
    (Measure.count : Measure (Fin 2))
  simp only [Function.comp_def, norm_neg] at h
  apply h.mono' (((measurable_fst.norm.const_div 1).mul
    ((base_measurable F χ i).norm.pow_const 2)).aestronglyMeasurable)
  exact ae_of_all _ fun p => by
    change ‖(1 / ‖p.1‖) * ‖base F χ i p‖ ^ 2‖ ≤
      (1 / ‖p.1‖) * ‖χ.value (-p.1)‖ ^ 2
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (base_norm_bound F χ i p) (by positivity)

def formFactors : FormFactors photonMeasure (Fin 3) where
  momentum := Prod.fst
  momentum_measurable := measurable_fst
  base := base F χ
  measurable := base_measurable F χ
  ultraviolet := base_ultraviolet F χ
  infrared := base_infrared F χ

/-- Solenoidal conjugation written in arbitrary polarization coordinates. -/
def frameConjugation (f : PhotonMode → ℂ) (p : PhotonMode) : ℂ :=
  ∑ b : Fin 2, (F.overlap p.1 p.2 b : ℂ) * starRingEnd ℂ (f (-p.1, b))

theorem frameConjugation_component (i : Fin 3) (c : FieldSpace → ℂ)
    (k : FieldSpace) (hk : k ≠ 0) (hc : starRingEnd ℂ (c (-k)) = c k) (a : Fin 2) :
    frameConjugation F (fun p => (F.epsilon p.1 p.2 i : ℂ) * c p.1) (k, a) =
      (F.epsilon k a i : ℂ) * c k := by
  have hr := congrArg (fun v : FieldSpace => v i) (F.overlap_reconstruction k hk a)
  have hr' : (∑ b : Fin 2, F.overlap k a b * F.epsilon (-k) b i) = F.epsilon k a i := by
    simpa only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul] using hr
  unfold frameConjugation
  simp only [map_mul, Complex.conj_ofReal, hc]
  calc
    _ = (∑ b : Fin 2, ((F.overlap k a b * F.epsilon (-k) b i : ℝ) : ℂ)) * c k := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b _
      rw [Complex.ofReal_mul, mul_assoc]
    _ = (F.epsilon k a i : ℂ) * c k := by
      rw [← Complex.ofReal_sum, hr']

theorem fieldPhase_conjugate_neg (k x : FieldSpace) :
    starRingEnd ℂ (fieldPhase (-k) x) = fieldPhase k x := by
  rw [fieldPhase, ← Complex.exp_conj]
  congr 1
  simp only [inner_neg_left, neg_neg, map_mul, Complex.conj_ofReal,
    Complex.conj_I, Complex.ofReal_neg]
  ring

theorem derivativeFactor_conjugate_neg (ds : List (Fin 3)) (k : FieldSpace) :
    starRingEnd ℂ (derivativeFactor ds (-k)) = derivativeFactor ds k := by
  induction ds with
  | nil => simp only [derivativeFactor, map_one]
  | cons j ds ih =>
    simp only [derivativeFactor, map_mul, map_neg, Complex.conj_I,
      Complex.conj_ofReal, PiLp.neg_apply, Complex.ofReal_neg, ih]
    ring

/-- Every translated physical field label belongs to the transported real family. -/
theorem momentumKernel_real (i : Fin 3) (x : FieldSpace) :
    frameConjugation F (momentumKernel Prod.fst (base F χ i) x) =ᵐ[photonMeasure]
      momentumKernel Prod.fst (base F χ i) x := by
  have hn : ∀ᵐ k ∂(volume : Measure FieldSpace), k ≠ 0 := volume.ae_ne 0
  have hr := (Measure.quasiMeasurePreserving_fst
    (ν := (Measure.count : Measure (Fin 2)))).ae (χ.reality.and hn)
  filter_upwards [hr] with p hp
  let c : FieldSpace → ℂ := fun k => χ.value (-k) * fieldPhase k x / (Real.sqrt 2 : ℂ)
  have hc : starRingEnd ℂ (c (-p.1)) = c p.1 := by
    have hχ : starRingEnd ℂ (χ.value p.1) = χ.value (-p.1) := by
      have h := congrArg (starRingEnd ℂ) hp.1
      simpa only [Complex.conj_conj] using h
    simp only [c, neg_neg, map_div₀, map_mul, hχ, fieldPhase_conjugate_neg,
      Complex.conj_ofReal]
  have he : momentumKernel Prod.fst (base F χ i) x =
      fun q => (F.epsilon q.1 q.2 i : ℂ) * c q.1 := by
    funext q
    simp only [momentumKernel, base, c]
    ring
  rw [he]
  exact frameConjugation_component F i c p.1 hp.2 hc p.2

theorem frameConjugation_mul (c : FieldSpace → ℂ) (f : PhotonMode → ℂ)
    (p : PhotonMode) (hc : starRingEnd ℂ (c (-p.1)) = c p.1) :
    frameConjugation F (fun q => c q.1 * f q) p =
      c p.1 * frameConjugation F f p := by
  simp only [frameConjugation, map_mul, hc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Sharp soft restriction and every ordered spatial derivative stay in
the same transported real family. -/
theorem softDerivativeKernel_real (i : Fin 3) (ds : List (Fin 3))
    (r : ℝ) (x : FieldSpace) :
    frameConjugation F (softDerivativeKernel Prod.fst ds r x (base F χ i))
      =ᵐ[photonMeasure] softDerivativeKernel Prod.fst ds r x (base F χ i) := by
  classical
  let c : FieldSpace → ℂ := fun k =>
    if ‖k‖ < r then derivativeFactor ds k else 0
  have he : softDerivativeKernel Prod.fst ds r x (base F χ i) =
      fun p => c p.1 * momentumKernel Prod.fst (base F χ i) x p := by
    funext p
    by_cases hp : ‖p.1‖ < r
    · simp only [softDerivativeKernel, softBase, hp, c, momentumKernel, ↓reduceIte]
      ring
    · simp only [softDerivativeKernel, softBase, hp, c, ↓reduceIte, mul_zero, zero_mul]
  rw [he]
  filter_upwards [momentumKernel_real F χ i x] with p hp
  rw [frameConjugation_mul, hp]
  simp only [c, norm_neg]
  split_ifs <;> simp only [derivativeFactor_conjugate_neg, map_zero]

end GptLean.PhysicalPolarization
