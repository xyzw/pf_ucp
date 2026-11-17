import GptLean.PhysicalPolarizationFrame
import GptLean.PhysicalPhotonHardSoft
import GptLean.PhysicalOnePhotonFourier
import GptLean.PhysicalFockSpatialField
import GptLean.PhysicalFockRealStructure
import Mathlib.MeasureTheory.Function.LpSeminorm.Count
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap

/-!
The article's real one-photon structure in an arbitrary measurable
polarization frame. Momentum reversal transports the two polarization
coordinates by the actual frame overlap. No parity condition is imposed
on the frame.
-/

noncomputable section

namespace GptLean.PhysicalPolarization.Frame

open MeasureTheory Gaussian PhysicalFock PhysicalOnePhotonFourier
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

variable (F : Frame)

theorem overlap_neg (k : FieldSpace) (a b : Fin 2) :
    F.overlap (-k) a b = F.overlap k b a := by
  simp only [overlap, neg_neg, real_inner_comm]

theorem overlap_measurable (a b : Fin 2) :
    Measurable (fun k => F.overlap k a b) := by
  exact (continuous_inner : Continuous (fun p : FieldSpace × FieldSpace =>
    inner ℝ p.1 p.2)).measurable.comp
      ((F.epsilon_measurable a).prodMk ((F.epsilon_measurable b).comp measurable_neg))

theorem epsilon_inner (k : FieldSpace) (a b : Fin 2) :
    inner ℝ (F.epsilon k a) (F.epsilon k b) = if a = b then 1 else 0 := by
  simpa only [epsilon, Fin.castSucc_inj] using
    (orthonormal_iff_ite.mp (F.basis k).orthonormal a.castSucc b.castSucc)

theorem overlap_reconstruction_all (k : FieldSpace) (a : Fin 2) :
    (∑ b : Fin 2, F.overlap k a b • F.epsilon (-k) b) = F.epsilon k a := by
  by_cases hk : k = 0
  · subst k
    simp only [overlap, neg_zero, epsilon_inner, ite_smul, one_smul, zero_smul]
    simp
  · exact F.overlap_reconstruction k hk a

theorem overlap_rows (k : FieldSpace) (a c : Fin 2) :
    (∑ b : Fin 2, F.overlap k a b * F.overlap k c b) = if a = c then 1 else 0 := by
  have h := congrArg (fun v => inner ℝ v (F.epsilon k c))
    (F.overlap_reconstruction_all k a)
  simp only [sum_inner, real_inner_smul_left] at h
  simpa only [overlap, real_inner_comm, epsilon_inner] using h

theorem overlap_columns (k : FieldSpace) (a c : Fin 2) :
    (∑ b : Fin 2, F.overlap k b a * F.overlap k b c) = if a = c then 1 else 0 := by
  simpa only [F.overlap_neg] using F.overlap_rows (-k) a c

private theorem finite_memLp (f : Fin 2 → ℂ) :
    MemLp f 2 (Measure.count : Measure (Fin 2)) :=
  ⟨(measurable_of_countable f).aestronglyMeasurable,
    eLpNorm_count_lt_top_of_lt (fun _ => enorm_lt_top)⟩

private def fiberVector (f : Fin 2 → ℂ) : Polarization :=
  (finite_memLp f).toLp f

private theorem fiberVector_apply (f : Fin 2 → ℂ) (a : Fin 2) :
    fiberVector f a = f a :=
  Measure.ae_count_iff.mp (finite_memLp f).coeFn_toLp a

private def fiberEval (a : Fin 2) : Polarization →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun u := u a
      map_add' u v := Measure.ae_count_iff.mp (Lp.coeFn_add u v) a
      map_smul' c u := Measure.ae_count_iff.mp (Lp.coeFn_smul c u) a }

private theorem fiberEval_apply (a : Fin 2) (u : Polarization) : fiberEval a u = u a := rfl

private def fiberBasis (a : Fin 2) : Polarization :=
  fiberVector (fun b => if b = a then 1 else 0)

private theorem fiberBasis_apply (a b : Fin 2) :
    fiberBasis a b = if b = a then 1 else 0 := fiberVector_apply _ _

private def fiberMatrix (k : FieldSpace) : Polarization →L[ℂ] Polarization :=
  ∑ a : Fin 2, ∑ b : Fin 2,
    (F.overlap k a b : ℂ) • (fiberEval b).smulRight (fiberBasis a)

private theorem fiberMatrix_apply (k : FieldSpace) (u : Polarization) (a : Fin 2) :
    fiberMatrix F k u a = ∑ b : Fin 2, (F.overlap k a b : ℂ) * u b := by
  change fiberEval a (fiberMatrix F k u) = _
  simp only [fiberMatrix, sum_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, map_sum, map_smul, fiberEval_apply,
    fiberBasis_apply, smul_eq_mul]
  simp [mul_ite]

private theorem overlap_columns_complex (k : FieldSpace) (a c : Fin 2) :
    (∑ b : Fin 2, (F.overlap k b a : ℂ) * (F.overlap k b c : ℂ)) =
      if a = c then 1 else 0 := by
  have h := congrArg (fun r : ℝ => (r : ℂ)) (F.overlap_columns k a c)
  simpa only [Complex.ofReal_sum, Complex.ofReal_mul, apply_ite,
    Complex.ofReal_one, Complex.ofReal_zero] using h

private theorem fiberMatrix_inner (k : FieldSpace) (u v : Polarization) :
    inner ℂ (fiberMatrix F k u) (fiberMatrix F k v) = inner ℂ u v := by
  have h00 := overlap_columns_complex F k 0 0
  have h01 := overlap_columns_complex F k 0 1
  have h10 := overlap_columns_complex F k 1 0
  have h11 := overlap_columns_complex F k 1 1
  norm_num [Fin.sum_univ_two] at h00 h01 h10 h11
  simp only [L2.inner_def, integral_count, RCLike.inner_apply, fiberMatrix_apply,
    Fin.sum_univ_two, map_add, map_mul, Complex.conj_ofReal]
  linear_combination
    h00 * (starRingEnd ℂ (u 0) * v 0) +
    h01 * (starRingEnd ℂ (u 0) * v 1) +
    h10 * (starRingEnd ℂ (u 1) * v 0) +
    h11 * (starRingEnd ℂ (u 1) * v 1)

private theorem fiberMatrix_norm (k : FieldSpace) (u : Polarization) :
    ‖fiberMatrix F k u‖ = ‖u‖ := by
  rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, fiberMatrix_inner]

private theorem fiberMatrix_stronglyMeasurable : StronglyMeasurable (fiberMatrix F) := by
  unfold fiberMatrix
  apply Finset.stronglyMeasurable_fun_sum
  intro a _
  apply Finset.stronglyMeasurable_fun_sum
  intro b _
  exact (Complex.measurable_ofReal.comp (F.overlap_measurable a b)).stronglyMeasurable.smul_const _

private theorem fiberMatrix_bound : ∀ᵐ k ∂(volume : Measure FieldSpace),
    ‖fiberMatrix F k‖ ≤ 1 := by
  exact ae_of_all _ fun k => (fiberMatrix F k).opNorm_le_bound (by norm_num)
    (fun u => by rw [fiberMatrix_norm, one_mul])

private theorem fiberMatrix_inverse (k : FieldSpace) (u : Polarization) :
    fiberMatrix F k (fiberMatrix F (-k) u) = u := by
  apply Lp.ext
  apply ae_of_all
  intro a
  simp only [fiberMatrix_apply, F.overlap_neg]
  calc
    _ = ∑ c : Fin 2, ((∑ b : Fin 2,
        (F.overlap k a b : ℂ) * (F.overlap k c b : ℂ)) * u c) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      congr 1
      ext c
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = u a := by
      have hh (c : Fin 2) : (∑ b : Fin 2,
          (F.overlap k a b : ℂ) * (F.overlap k c b : ℂ)) = if a = c then 1 else 0 := by
        simpa only [F.overlap_neg] using overlap_columns_complex F (-k) a c
      simp only [hh]
      simp

private abbrev fiberConjugation : RealStructure Polarization :=
  RealStructure.complex.onLp (Measure.count : Measure (Fin 2))

private theorem fiberConjugation_apply (u : Polarization) (a : Fin 2) :
    fiberConjugation.conjugation u a = starRingEnd ℂ (u a) :=
  Measure.ae_count_iff.mp (RealStructure.onLp_ae RealStructure.complex _ u) a

private theorem fiberMatrix_conjugation (k : FieldSpace) (u : Polarization) :
    fiberConjugation.conjugation (fiberMatrix F k u) =
      fiberMatrix F k (fiberConjugation.conjugation u) := by
  apply Lp.ext
  apply ae_of_all
  intro a
  simp only [fiberConjugation_apply, fiberMatrix_apply, map_sum, map_mul,
    Complex.conj_ofReal]

private def matrixMultiplier : PositionSpace →L[ℂ] PositionSpace :=
  spatialOperator volume (fiberMatrix F) (fiberMatrix_stronglyMeasurable F).aestronglyMeasurable
    1 (fiberMatrix_bound F)

private theorem matrixMultiplier_ae (u : PositionSpace) :
    matrixMultiplier F u =ᵐ[volume] fun k => fiberMatrix F k (u k) :=
  spatialOperator_ae _ _ _ _ _ u

private theorem matrixMultiplier_norm (u : PositionSpace) :
    ‖matrixMultiplier F u‖ = ‖u‖ := by
  apply congrArg ENNReal.toReal
  apply eLpNorm_congr_norm_ae
  filter_upwards [matrixMultiplier_ae F u] with k hk
  rw [hk, fiberMatrix_norm]

private def momentumReflection : PositionSpace →ₗᵢ[ℂ] PositionSpace :=
  Lp.compMeasurePreservingₗᵢ ℂ Neg.neg (Measure.measurePreserving_neg volume)

private theorem momentumReflection_ae (u : PositionSpace) :
    momentumReflection u =ᵐ[volume] fun k => u (-k) :=
  Lp.coeFn_compMeasurePreserving u (Measure.measurePreserving_neg volume)

private def positionMap : PositionSpace →ₛₗ[starRingEnd ℂ] PositionSpace where
  toFun u := matrixMultiplier F ((fiberConjugation.onLp volume).conjugation
    (momentumReflection u))
  map_add' u v := by simp only [map_add]
  map_smul' c u := by simp only [map_smul, map_smulₛₗ]

private theorem positionMap_ae (u : PositionSpace) :
    positionMap F u =ᵐ[volume] fun k =>
      fiberMatrix F k (fiberConjugation.conjugation (u (-k))) := by
  filter_upwards [matrixMultiplier_ae F ((fiberConjugation.onLp volume).conjugation
      (momentumReflection u)), fiberConjugation.onLp_ae volume (momentumReflection u),
    momentumReflection_ae u] with k h₁ h₂ h₃
  exact h₁.trans (congrArg (fiberMatrix F k) (h₂.trans (congrArg _ h₃)))

private theorem positionMap_norm (u : PositionSpace) : ‖positionMap F u‖ = ‖u‖ := by
  exact (matrixMultiplier_norm F _).trans
    (((fiberConjugation.onLp volume).conjugation.norm_map _).trans
      (momentumReflection.norm_map u))

private theorem positionMap_involutive (u : PositionSpace) :
    positionMap F (positionMap F u) = u := by
  have hr := (Measure.measurePreserving_neg (volume : Measure FieldSpace)).quasiMeasurePreserving.ae
    (positionMap_ae F u)
  apply Lp.ext
  filter_upwards [positionMap_ae F (positionMap F u), hr] with k hk hrk
  rw [hk, hrk, neg_neg, fiberMatrix_conjugation, fiberConjugation.involutive,
    fiberMatrix_inverse]

private def positionConjugation : PositionSpace ≃ₗᵢ⋆[ℂ] PositionSpace where
  toLinearMap := positionMap F
  invFun := positionMap F
  left_inv := positionMap_involutive F
  right_inv := positionMap_involutive F
  norm_map' := positionMap_norm F

/-- The actual one-photon conjugation in the given transverse frame. -/
def conjugation : Lp ℂ 2 photonMeasure ≃ₗᵢ⋆[ℂ] Lp ℂ 2 photonMeasure :=
  (PhysicalSourceFubini.curryEquiv.trans (positionConjugation F)).trans
    PhysicalSourceFubini.curryEquiv.symm

theorem conjugation_involutive : Function.Involutive F.conjugation := by
  intro u
  change PhysicalSourceFubini.curryEquiv.symm
    (positionMap F (PhysicalSourceFubini.curryEquiv
      (PhysicalSourceFubini.curryEquiv.symm
        (positionMap F (PhysicalSourceFubini.curryEquiv u))))) = u
  rw [LinearIsometryEquiv.apply_symm_apply, positionMap_involutive,
    LinearIsometryEquiv.symm_apply_apply]

/-- The concrete antiunitary defines an ordinary Hilbert real structure. -/
def realStructure : RealStructure (Lp ℂ 2 photonMeasure) where
  conjugation := F.conjugation
  involutive := F.conjugation_involutive

theorem conjugation_ae (u : Lp ℂ 2 photonMeasure) :
    F.conjugation u =ᵐ[photonMeasure] frameConjugation F u := by
  have hout := PhysicalSourceFubini.curryEquiv_represents_ae (F.conjugation u)
  have he : PhysicalSourceFubini.curryEquiv (F.conjugation u) =
      positionMap F (PhysicalSourceFubini.curryEquiv u) :=
    LinearIsometryEquiv.apply_symm_apply _ _
  rw [he] at hout
  have hin := (Measure.measurePreserving_neg (volume : Measure FieldSpace)).quasiMeasurePreserving.ae
    (PhysicalSourceFubini.curryEquiv_represents_ae u)
  have hsections : ∀ᵐ k ∂(volume : Measure FieldSpace), ∀ a : Fin 2,
      F.conjugation u (k, a) = frameConjugation F u (k, a) := by
    filter_upwards [hout, positionMap_ae F (PhysicalSourceFubini.curryEquiv u), hin]
      with k ho hp hi
    intro a
    have hoa : positionMap F (PhysicalSourceFubini.curryEquiv u) k a =
        F.conjugation u (k, a) := Measure.ae_count_iff.mp ho a
    rw [← hoa, hp, fiberMatrix_apply]
    simp only [fiberConjugation_apply, frameConjugation]
    apply Finset.sum_congr rfl
    intro b _
    have hib : PhysicalSourceFubini.curryEquiv u (-k) b = u (-k, b) :=
      Measure.ae_count_iff.mp hi b
    rw [hib]
  have h := (Measure.quasiMeasurePreserving_fst
    (ν := (Measure.count : Measure (Fin 2)))).ae hsections
  filter_upwards [h] with p hp
  exact hp p.2

theorem frameConjugation_congr_ae {f g : PhotonMode → ℂ} (h : f =ᵐ[photonMeasure] g) :
    frameConjugation F f =ᵐ[photonMeasure] frameConjugation F g := by
  have hs := (Measure.measurePreserving_neg (volume : Measure FieldSpace)).quasiMeasurePreserving.ae
    (Measure.ae_ae_of_ae_prod h)
  have hp := (Measure.quasiMeasurePreserving_fst
    (ν := (Measure.count : Measure (Fin 2)))).ae hs
  filter_upwards [hp] with p hp
  unfold frameConjugation
  apply Finset.sum_congr rfl
  intro b _
  rw [Measure.ae_count_iff.mp hp b]

/-- A real representative yields a fixed L² vector. -/
theorem conjugation_toLp_fixed {f : PhotonMode → ℂ} (hf : MemLp f 2 photonMeasure)
    (hr : frameConjugation F f =ᵐ[photonMeasure] f) :
    F.conjugation (hf.toLp f) = hf.toLp f := by
  apply Lp.ext
  exact (F.conjugation_ae _).trans
    ((F.frameConjugation_congr_ae hf.coeFn_toLp).trans (hr.trans hf.coeFn_toLp.symm))

/-- Every article field label is fixed by the concrete L² conjugation. -/
theorem fourierKernel_fixed (χ : ArticleCutoff) (i : Fin 3) (x : FieldSpace) :
    F.conjugation ((formFactors F χ).fourierKernel (i, x)) =
      (formFactors F χ).fourierKernel (i, x) :=
  F.conjugation_toLp_fixed
    (PhotonLocalizationPhysicalKernels.momentumKernel_memLp Prod.fst measurable_fst
      (base F χ i) (base_measurable F χ i) (base_ultraviolet F χ i) x)
    (momentumKernel_real F χ i x)

/-- The same statement applies to every ordered soft spatial derivative. -/
theorem softDerivativeKernel_fixed (χ : ArticleCutoff) (i : Fin 3)
    (ds : List (Fin 3)) (κ : ℝ) (x : FieldSpace)
    (hf : MemLp (softDerivativeKernel Prod.fst ds κ x (base F χ i)) 2 photonMeasure) :
    F.conjugation (hf.toLp _) = hf.toLp _ :=
  F.conjugation_toLp_fixed hf (softDerivativeKernel_real F χ i ds κ x)

private theorem frameConjugation_soft_indicator (κ : ℝ) (f : PhotonMode → ℂ) :
    frameConjugation F ((softMomentumSet κ).indicator f) =
      (softMomentumSet κ).indicator (frameConjugation F f) := by
  funext p
  by_cases hp : ‖p.1‖ < κ
  · simp [frameConjugation, softMomentumSet, NormalPhoton.frequency, Set.indicator, hp]
  · simp [frameConjugation, softMomentumSet, NormalPhoton.frequency, Set.indicator, hp]

/-- Soft momentum truncation respects the actual frame conjugation. -/
theorem conjugation_soft_projection (κ : ℝ) (u : Lp ℂ 2 photonMeasure) :
    F.conjugation (MomentumSplit.projection photonMeasure (softMomentumSet κ)
      (softMomentumSet_measurable κ) u) =
    MomentumSplit.projection photonMeasure (softMomentumSet κ)
      (softMomentumSet_measurable κ) (F.conjugation u) := by
  apply Lp.ext
  refine (F.conjugation_ae _).trans ?_
  refine (F.frameConjugation_congr_ae
    (MomentumSplit.projection_ae photonMeasure (softMomentumSet κ)
      (softMomentumSet_measurable κ) u)).trans ?_
  rw [frameConjugation_soft_indicator]
  have hi : (softMomentumSet κ).indicator (frameConjugation F u) =ᵐ[photonMeasure]
      (softMomentumSet κ).indicator (F.conjugation u) := by
    filter_upwards [F.conjugation_ae u] with p hp
    by_cases hs : p ∈ softMomentumSet κ <;> simp only [Set.indicator, hs, hp, ↓reduceIte]
  exact hi.trans (MomentumSplit.projection_ae photonMeasure (softMomentumSet κ)
    (softMomentumSet_measurable κ) (F.conjugation u)).symm

theorem conjugation_mem_soft (κ : ℝ) (u : softOnePhoton κ) :
    F.conjugation (u : Lp ℂ 2 photonMeasure) ∈ softOnePhoton κ := by
  have h := MomentumSplit.projection_mem_supported photonMeasure (softMomentumSet κ)
    (softMomentumSet_measurable κ) (F.conjugation (u : Lp ℂ 2 photonMeasure))
  rw [← F.conjugation_soft_projection, MomentumSplit.projection_of_supported] at h
  exact h

/-- The soft one-photon space carries the restricted physical real structure. -/
def softRealStructure (κ : ℝ) : RealStructure (softOnePhoton κ) where
  conjugation :=
    { toFun u := ⟨F.conjugation u, F.conjugation_mem_soft κ u⟩
      invFun u := ⟨F.conjugation u, F.conjugation_mem_soft κ u⟩
      map_add' u v := Subtype.ext (map_add F.conjugation (u : Lp ℂ 2 photonMeasure) v)
      map_smul' c u := Subtype.ext (F.conjugation.map_smulₛₗ c (u : Lp ℂ 2 photonMeasure))
      left_inv u := Subtype.ext (F.conjugation_involutive u)
      right_inv u := Subtype.ext (F.conjugation_involutive u)
      norm_map' u := F.conjugation.norm_map u }
  involutive u := Subtype.ext (F.conjugation_involutive u)

@[simp] theorem softRealStructure_apply (κ : ℝ) (u : softOnePhoton κ) :
    ((F.softRealStructure κ).conjugation u : Lp ℂ 2 photonMeasure) = F.conjugation u := rfl

end GptLean.PhysicalPolarization.Frame
