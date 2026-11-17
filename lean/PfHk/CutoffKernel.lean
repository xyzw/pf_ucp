import PfHk.GroundState
import GptLean.PhysicalMeanFieldsWeighted
import GptLean.PhysicalNonattainmentFluxKernel

/-!
The photon stationarity part of `prop-cutoff-kernel` in `pf_ucp.tex`.
This module proves the exact Weyl orthogonality identity on the physical
model. The further Fourier transform identification is a separate obligation.
-/

noncomputable section

namespace PfHk

open MeasureTheory Filter GptLean GptLean.PhysicalPairSpace
  GptLean.PhysicalPairDuality GptLean.PhysicalGroundState
  GptLean.PhysicalFock GptLean.PhysicalWeyl GptLean.PhysicalNonattainmentFluxKernel
  GptLean.Representability
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

variable {N : ℕ} (i : Fin N) (F : PhysicalPolarization.Frame)
  (χ : PhysicalPolarization.ArticleCutoff) (C : CanonicalSectorCCR photonMeasure)
  (B : PhysicalNormalTrace.StandardNormalTraceBackground)
  (S : PhysicalClosedForms.StandardClosedFormBackground) (e : ℝ)
  (W : ConcreteWeylLaw photonMeasure)

/-- The integrability needed for subtracting the two photon stationarity
identities. The field induced by an arbitrary one-photon L² vector is bounded. -/
theorem classical_current_integrable (a : Potential) (d : Pair)
    (f : Lp ℂ 2 photonMeasure) (b : Fin 3) :
    Integrable (fun y => classicalVector F χ f b y * physicalCurrent a d y b) volume :=
  (physicalCurrent_component_integrable a d b).bdd_mul
    (classicalVector_continuous F χ f b).aestronglyMeasurable
    (ae_of_all _ (classicalVector_bound F χ f b))

include W in
/-- Equation `weyl-orthogonality`. It uses the same common ground state for
both potentials, so the annihilation expectation cancels. The kernel
condition expresses `f ∈ D(ω)` using the existing weighted-kernel interface.
No photon-number finiteness assumption is introduced. -/
theorem weyl_orthogonality
    {a₁ a₂ : Potential} {p₁ p₂ : State F χ C B S e (N := N)}
    (h₁ : IsGroundState i F χ C B S e a₁ p₁)
    (h₂ : IsGroundState i F χ C B S e a₂ p₂)
    (hd : (model i F χ C B S e).density p₁ =
      (model i F χ C B S e).density p₂)
    (he : e ≠ 0) {f : Lp ℂ 2 photonMeasure} (K : WeightedPhotonKernel)
    (hK : ∀ᵐ p ∂photonMeasure, K.val.2 p = (Real.sqrt ‖p.1‖ : ℂ) * f p) :
    (∑ b, ∫ y, classicalVector F χ f b y *
      vectorDifference a₁ a₂ ((model i F χ C B S e).density p₁) y b) = 0 := by
  have hcommon := (common_ground_state i F χ C B S e h₁ h₂ hd).2.1
  have ha₁ := ground_real_amplitude i F χ C B S e W h₁ K hK
  have ha₂ := ground_real_amplitude i F χ C B S e W hcommon K hK
  have hsame := mul_left_cancel₀ he (ha₁.symm.trans ha₂)
  calc
    _ = (∑ b, ∫ y, classicalVector F χ f b y *
          physicalCurrent a₁ ((model i F χ C B S e).density p₁) y b) -
        ∑ b, ∫ y, classicalVector F χ f b y *
          physicalCurrent a₂ ((model i F χ C B S e).density p₁) y b := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro b _
      rw [← integral_sub (classical_current_integrable F χ a₁ _ f b)
        (classical_current_integrable F χ a₂ _ f b)]
      apply integral_congr_ae
      exact ae_of_all _ fun y => by
        dsimp only
        rw [vectorDifference_eq_current_sub, PiLp.sub_apply, mul_sub]
    _ = 0 := sub_eq_zero.mpr hsame

/-- The Bochner source in equation `gb-def`, retaining its infrared-weighted
component as well as its ordinary one-photon component. -/
def currentSource (b : Position → Vector) : WeightedPhotonKernel :=
  ∑ μ : Fin 3, ∫ x, (b x μ) • fieldKernel F χ (μ, x)

theorem currentSource_integrable {b : Position → Vector} (hb : Integrable b volume)
    (μ : Fin 3) : Integrable (fun x => (b x μ) • fieldKernel F χ (μ, x)) volume := by
  have hc := (EuclideanSpace.proj μ : Vector →L[ℝ] ℝ).integrable_comp hb
  have hk : Continuous (fun x : Position => fieldKernel F χ (μ, x)) :=
    (PhysicalProfiles.momentumKernel_continuous (PhysicalPolarization.formFactors F χ) rfl
      (LinearIsometryEquiv.refl ℝ _)).comp (continuous_const.prodMk continuous_id)
  refine (hc.norm.const_mul (PhysicalRemovalKernels.bound F χ)).mono'
    (hc.aestronglyMeasurable.smul hk.aestronglyMeasurable) ?_
  refine ae_of_all _ fun x => ?_
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left
    (PhysicalProfiles.momentumKernel_bound (PhysicalPolarization.formFactors F χ) rfl
      (LinearIsometryEquiv.refl ℝ _) (μ, x)) (norm_nonneg (b x μ))).trans_eq (mul_comm _ _)

/-- The pairing of the Bochner source with a Weyl direction equals the
classical-field pairing. This is the passage from `weyl-orthogonality`
to the one-photon Hilbert space. -/
theorem currentSource_pairing {b : Position → Vector} (hb : Integrable b volume)
    (f : Lp ℂ 2 photonMeasure) :
    2 * (⟪(currentSource F χ b).val.1, f⟫_ℂ).re =
      ∑ μ : Fin 3, ∫ x, classicalVector F χ f μ x * b x μ := by
  let P : WeightedPhotonKernel →L[ℝ] ℝ :=
    (Complex.reCLM.comp ((innerSL ℂ f).restrictScalars ℝ)).comp (component false)
  have hmap : P (currentSource F χ b) =
      ∑ μ : Fin 3, ∫ x, P ((b x μ) • fieldKernel F χ (μ, x)) := by
    rw [currentSource, map_sum]
    apply Finset.sum_congr rfl
    intro μ _
    exact (P.integral_comp_comm (currentSource_integrable F χ hb μ)).symm
  have hP (k : WeightedPhotonKernel) : P k = (⟪k.val.1, f⟫_ℂ).re :=
    re_inner_comm f k.val.1
  rw [← hP, hmap, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro μ _
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    dsimp only
    rw [map_smul, smul_eq_mul, hP]
    unfold classicalVector
    ring

/-- Pairing a weighted kernel with its truncated inverse-frequency direction
is the squared norm of its truncated infrared component. -/
theorem inner_truncDirection (k : WeightedPhotonKernel) (m : ℕ) :
    (⟪k.val.1, truncDirection m k⟫_ℂ).re = ‖(truncKernel m k).val.2‖ ^ 2 := by
  rw [L2.inner_def, PhysicalPFSoftTag.norm_sq_eq_integral]
  refine (integral_re (L2.integrable_inner (𝕜 := ℂ) k.val.1
    (truncDirection m k))).symm.trans ?_
  apply integral_congr_ae
  filter_upwards [windowInvCut_ae m k.val.1, windowCut_ae m k.val.2, k.property]
    with p hf ht hk
  change (⟪k.val.1 p, windowInvCut m k.val.1 p⟫_ℂ).re =
    ‖windowCut m k.val.2 p‖ ^ 2
  rw [hf, ht]
  change RCLike.re (⟪k.val.1 p, windowInv m p • k.val.1 p⟫_ℂ) = _
  rw [← real_inner_eq_re_inner ℂ, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hnorm : ‖k.val.1 p‖ ^ 2 = ‖p.1‖ * ‖k.val.2 p‖ ^ 2 := by
    rw [hk, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      mul_pow, Real.sq_sqrt (norm_nonneg _)]
  rw [hnorm]
  unfold windowInv window
  by_cases hp : p ∈ windowSet m
  · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, one_smul]
    have hpos : 0 < ‖p.1‖ := (by positivity : 0 < 1 / ((m : ℝ) + 1)).trans_le hp.1
    field_simp [hpos.ne']
  · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp]
    simp

/-- The already proved frequency truncations suffice to separate weighted
one-photon kernels. This supplies the density step without a new background. -/
theorem weightedKernel_zero_of_trunc_pairings (k : WeightedPhotonKernel)
    (h : ∀ m, (⟪k.val.1, truncDirection m k⟫_ℂ).re = 0) : k = 0 := by
  have hz (m : ℕ) : (truncKernel m k).val.2 = 0 := by
    have hsq := (inner_truncDirection k m).symm.trans (h m)
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (truncKernel m k).val.2])
  have hlim := truncKernel_tendsto k
  simp only [hz, sub_zero] at hlim
  have hk₂ : k.val.2 = 0 := norm_eq_zero.mp
    (tendsto_nhds_unique tendsto_const_nhds hlim)
  have hk₁ : k.val.1 = 0 := by
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    filter_upwards [k.property, Lp.eq_zero_iff_ae_eq_zero.mp hk₂] with p hp hzero
    simp only [hzero, Pi.zero_apply, mul_zero] at hp
    exact hp
  apply Subtype.ext
  exact Prod.ext hk₁ hk₂

include W in
/-- The source `g` in `gb-def` vanishes for equal-data ground states at
nonzero coupling. Its definition is the actual weighted Bochner integral. -/
theorem currentSource_zero
    {a₁ a₂ : Potential} {p₁ p₂ : State F χ C B S e (N := N)}
    (h₁ : IsGroundState i F χ C B S e a₁ p₁)
    (h₂ : IsGroundState i F χ C B S e a₂ p₂)
    (hd : (model i F χ C B S e).density p₁ =
      (model i F χ C B S e).density p₂) (he : e ≠ 0) :
    currentSource F χ
      (vectorDifference a₁ a₂ ((model i F χ C B S e).density p₁)) = 0 := by
  apply weightedKernel_zero_of_trunc_pairings
  intro m
  let b := vectorDifference a₁ a₂ ((model i F χ C B S e).density p₁)
  have hpair := currentSource_pairing F χ
    (vectorDifference_integrable a₁ a₂ ((model i F χ C B S e).density p₁))
    (truncDirection m (currentSource F χ b))
  have hz := weyl_orthogonality i F χ C B S e W h₁ h₂ hd he
    (truncKernel m (currentSource F χ b)) (truncKernel_direction m (currentSource F χ b))
  have heq : 2 * (⟪(currentSource F χ b).val.1,
      truncDirection m (currentSource F χ b)⟫_ℂ).re = 0 := hpair.trans hz
  linarith

end PfHk
