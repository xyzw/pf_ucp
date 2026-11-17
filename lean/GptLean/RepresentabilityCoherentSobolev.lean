import GptLean.SymmetricLift.FullH1TensorLift
import GptLean.SymmetricLift.CompactTest
import GptLean.SymmetricLift.SobolevRemovability

/-!
The weak chain passage needed by the combined coherent phase and amplitude.
The derivative is split before taking limits. A uniformly bounded operator
acts on the weak derivative, another on the input, and the remainder is
bounded. In particular, no square integrability of the product of an input
and its weak derivative is required.
-/

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1200000

namespace GptLean.Representability

open MeasureTheory Filter SymmetricLift
open scoped ENNReal Topology ContDiff

variable {X P E : Type*} [MeasurableSpace X]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Contractions acting on a convergent L2 input pass to the L2 limit.
Strong operator convergence only needs to hold on the fixed limiting input. -/
theorem contraction_apply_tendsto_eLpNorm {μ : Measure X}
    (A : ℕ → X → P →L[ℝ] E) (A₀ : X → P →L[ℝ] E)
    (hA : ∀ n, AEStronglyMeasurable (A n) μ)
    (hA₀ : AEStronglyMeasurable A₀ μ)
    (hbound : ∀ n x v, ‖A n x v‖ ≤ ‖v‖)
    (hbound₀ : ∀ x v, ‖A₀ x v‖ ≤ ‖v‖)
    (u : ℕ → X → P) (u₀ : X → P)
    (hu : ∀ n, AEStronglyMeasurable (u n) μ) (hu₀ : MemLp u₀ 2 μ)
    (hconv : Tendsto (fun n => eLpNorm (u n - u₀) 2 μ) atTop (𝓝 0))
    (hfixed : ∀ᵐ x ∂μ, Tendsto (fun n => A n x (u₀ x)) atTop (𝓝 (A₀ x (u₀ x)))) :
    Tendsto (fun n => eLpNorm
      ((fun x => A n x (u n x)) - fun x => A₀ x (u₀ x)) 2 μ) atTop (𝓝 0) := by
  let a n := fun x => A n x (u n x - u₀ x)
  let b n := (fun x => A n x (u₀ x)) - fun x => A₀ x (u₀ x)
  have happ (n) : AEStronglyMeasurable (fun x => A n x (u₀ x)) μ :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      ((hA n).prodMk hu₀.aestronglyMeasurable)
  have happ₀ : AEStronglyMeasurable (fun x => A₀ x (u₀ x)) μ :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      (hA₀.prodMk hu₀.aestronglyMeasurable)
  have ha : Tendsto (fun n => eLpNorm (a n) 2 μ) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv
      (fun _ => zero_le)
    intro n
    exact eLpNorm_mono_ae (ae_of_all _ fun x => hbound n x _)
  have hb : Tendsto (fun n => eLpNorm (b n) 2 μ) atTop (𝓝 0) := by
    apply tendsto_eLpNorm_two_of_dominated_sq happ happ₀
      (hu₀.integrable_norm_pow (by norm_num))
    · exact fun n => ae_of_all _ fun x =>
        (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 (hbound n x _)
    · exact ae_of_all _ fun x =>
        (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 (hbound₀ x _)
    · exact hfixed
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [add_zero] using ha.add hb) (fun _ => zero_le)
  intro n
  have he : ((fun x => A n x (u n x)) - fun x => A₀ x (u₀ x)) = a n + b n := by
    funext x
    simp only [a, b, Pi.add_apply, Pi.sub_apply, map_sub]
    abel
  change eLpNorm ((fun x => A n x (u n x)) - fun x => A₀ x (u₀ x)) 2 μ ≤
    eLpNorm (a n) 2 μ + eLpNorm (b n) 2 μ
  rw [he]
  apply eLpNorm_add_le
  · exact isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      ((hA n).prodMk ((hu n).sub hu₀.aestronglyMeasurable))
  · exact (happ n).sub happ₀
  · norm_num

section Chain

variable {d : ℕ} [CompleteSpace P] [CompleteSpace E]

abbrev CoherentBase (d : ℕ) := EuclideanSpace ℝ (Fin d)

omit [CompleteSpace E] in
/-- An ordinary differentiable map with a bounded split derivative acts on
local weak H1 fields. All approximation and distributional passage is proved
here. The supplied derivative hypothesis is only a classical line rule. -/
theorem weakH1Local_bounded_split_chain
    (F : CoherentBase d × P → E)
    (A : CoherentBase d × P → P →L[ℝ] E)
    (B : Fin d → CoherentBase d × P → P →L[ℝ] E)
    (R : Fin d → CoherentBase d × P → E)
    (hF : Continuous F) (hA : Continuous A)
    (hB : ∀ i, Continuous (B i)) (hR : ∀ i, Continuous (R i))
    (hFnorm : ∀ x, ‖F x‖ ≤ 1)
    (hAnorm : ∀ x v, ‖A x v‖ ≤ ‖v‖)
    (hBnorm : ∀ i x v, ‖B i x v‖ ≤ ‖v‖)
    (hRnorm : ∀ i x, ‖R i x‖ ≤ 1)
    (hline : ∀ (v : CoherentBase d → P) i x dv,
      HasLineDerivAt ℝ v dv x (EuclideanSpace.single i 1) →
      HasLineDerivAt ℝ (fun y => F (y, v y))
        (A (x, v x) dv + B i (x, v x) (v x) + R i (x, v x))
        x (EuclideanSpace.single i 1))
    {u : CoherentBase d → P} {du : Fin d → CoherentBase d → P}
    (hu : HasWeakH1Local u du) :
    HasWeakH1Local (fun x => F (x, u x))
      (fun i x => A (x, u x) (du i x) + B i (x, u x) (u x) + R i (x, u x)) := by
  have hui := localMemLp_two_locallyIntegrable hu.function_memLp
  have hdui := fun i => localMemLp_two_locallyIntegrable (hu.derivative_memLp i)
  let uₙ := boundedMollification u
  let duₙ := fun i => boundedMollification (du i)
  have huₙ (n) : ContDiff ℝ ∞ (uₙ n) := boundedMollification_contDiff hui n
  have hduₙ (i n) : ContDiff ℝ ∞ (duₙ i n) := boundedMollification_contDiff (hdui i) n
  have hpair : AEStronglyMeasurable (fun x => (x, u x)) volume :=
    continuous_id.aestronglyMeasurable.prodMk hui.aestronglyMeasurable
  have hpairₙ (n) : Continuous (fun x => (x, uₙ n x)) :=
    continuous_id.prodMk (huₙ n).continuous
  have hlim := boundedMollification_ae_tendsto hui
  have hFm : AEStronglyMeasurable (fun x => F (x, u x)) volume :=
    hF.comp_aestronglyMeasurable hpair
  have hAm : AEStronglyMeasurable (fun x => A (x, u x)) volume :=
    hA.comp_aestronglyMeasurable hpair
  have hBm (i) : AEStronglyMeasurable (fun x => B i (x, u x)) volume :=
    (hB i).comp_aestronglyMeasurable hpair
  have hRm (i) : AEStronglyMeasurable (fun x => R i (x, u x)) volume :=
    (hR i).comp_aestronglyMeasurable hpair
  have hAmem (i K) (hK : IsCompact K) :
      MemLp (fun x => A (x, u x) (du i x)) 2 (volume.restrict K) :=
    (hu.derivative_memLp i K hK).mono
      (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
        (hAm.prodMk (hdui i).aestronglyMeasurable)).restrict
      (ae_of_all _ fun x => hAnorm _ _)
  have hBmem (i K) (hK : IsCompact K) :
      MemLp (fun x => B i (x, u x) (u x)) 2 (volume.restrict K) :=
    (hu.function_memLp K hK).mono
      (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
        ((hBm i).prodMk hui.aestronglyMeasurable)).restrict
      (ae_of_all _ fun x => hBnorm i _ _)
  have hRmem (i K) (hK : IsCompact K) :
      MemLp (fun x => R i (x, u x)) 2 (volume.restrict K) := by
    let : IsFiniteMeasure (volume.restrict K) :=
      isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
    exact MemLp.of_bound (hRm i).restrict 1 (ae_of_all _ fun x => hRnorm i _)
  have hFmem (K) (hK : IsCompact K) :
      MemLp (fun x => F (x, u x)) 2 (volume.restrict K) := by
    let : IsFiniteMeasure (volume.restrict K) :=
      isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
    exact MemLp.of_bound hFm.restrict 1 (ae_of_all _ fun x => hFnorm _)
  refine ⟨hFmem, fun i K hK => ((hAmem i K hK).add (hBmem i K hK)).add
    (hRmem i K hK), ?_⟩
  intro i φ hφ hs
  let K := tsupport φ
  have hK : IsCompact K := hs
  let : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  let fₙ := fun n x => F (x, uₙ n x)
  let aₙ := fun n x => A (x, uₙ n x) (duₙ i n x)
  let bₙ := fun n x => B i (x, uₙ n x) (uₙ n x)
  let rₙ := fun n x => R i (x, uₙ n x)
  have hfₙ (n) : MemLp (fₙ n) 2 (volume.restrict K) :=
    MemLp.of_bound (hF.comp (hpairₙ n)).aestronglyMeasurable.restrict 1
      (ae_of_all _ fun x => hFnorm _)
  have haₙ (n) : MemLp (aₙ n) 2 (volume.restrict K) :=
    (boundedMollification_memLp_two_restrict (hdui i) n hK).mono
      (((hA.comp (hpairₙ n)).clm_apply (hduₙ i n).continuous).aestronglyMeasurable.restrict)
      (ae_of_all _ fun x => hAnorm _ _)
  have hbₙ (n) : MemLp (bₙ n) 2 (volume.restrict K) :=
    (boundedMollification_memLp_two_restrict hui n hK).mono
      (((hB i).comp (hpairₙ n)).clm_apply (huₙ n).continuous).aestronglyMeasurable.restrict
      (ae_of_all _ fun x => hBnorm i _ _)
  have hrₙ (n) : MemLp (rₙ n) 2 (volume.restrict K) :=
    MemLp.of_bound ((hR i).comp (hpairₙ n)).aestronglyMeasurable.restrict 1
      (ae_of_all _ fun x => hRnorm i _)
  have hflim : Tendsto (fun n => eLpNorm (fₙ n - fun x => F (x, u x))
      2 (volume.restrict K)) atTop (𝓝 0) := by
    apply tendsto_eLpNorm_two_of_dominated_sq (fun n => (hfₙ n).1) hFm.restrict
      (integrable_const (1 : ℝ))
    · exact fun n => ae_of_all _ fun x => by nlinarith [hFnorm (x, uₙ n x), norm_nonneg (fₙ n x)]
    · exact ae_of_all _ fun x => by nlinarith [hFnorm (x, u x), norm_nonneg (F (x, u x))]
    · filter_upwards [ae_restrict_le hlim] with x hx
      exact (hF.tendsto _).comp (tendsto_const_nhds.prodMk_nhds hx)
  have halim : Tendsto (fun n => eLpNorm (aₙ n - fun x => A (x, u x) (du i x))
      2 (volume.restrict K)) atTop (𝓝 0) := by
    apply contraction_apply_tendsto_eLpNorm
      (fun n x => A (x, uₙ n x)) (fun x => A (x, u x))
      (fun n => (hA.comp (hpairₙ n)).aestronglyMeasurable.restrict) hAm.restrict
      (fun n x v => hAnorm _ v) (fun x v => hAnorm _ v)
      (duₙ i) (du i) (fun n => (hduₙ i n).continuous.aestronglyMeasurable.restrict)
      (hu.derivative_memLp i K hK)
      (boundedMollification_tendsto_eLpNorm_sub (hu.derivative_memLp i) hK)
    filter_upwards [ae_restrict_le hlim] with x hx
    have hc : Continuous (fun p : CoherentBase d × P => A p (du i x)) :=
      hA.clm_apply continuous_const
    exact (hc.tendsto (x, u x)).comp (tendsto_const_nhds.prodMk_nhds hx)
  have hblim : Tendsto (fun n => eLpNorm (bₙ n - fun x => B i (x, u x) (u x))
      2 (volume.restrict K)) atTop (𝓝 0) := by
    apply contraction_apply_tendsto_eLpNorm
      (fun n x => B i (x, uₙ n x)) (fun x => B i (x, u x))
      (fun n => ((hB i).comp (hpairₙ n)).aestronglyMeasurable.restrict) (hBm i).restrict
      (fun n x v => hBnorm i _ v) (fun x v => hBnorm i _ v)
      uₙ u (fun n => (huₙ n).continuous.aestronglyMeasurable.restrict)
      (hu.function_memLp K hK)
      (boundedMollification_tendsto_eLpNorm_sub hu.function_memLp hK)
    filter_upwards [ae_restrict_le hlim] with x hx
    have hc : Continuous (fun p : CoherentBase d × P => B i p (u x)) :=
      (hB i).clm_apply continuous_const
    exact (hc.tendsto (x, u x)).comp (tendsto_const_nhds.prodMk_nhds hx)
  have hrlim : Tendsto (fun n => eLpNorm (rₙ n - fun x => R i (x, u x))
      2 (volume.restrict K)) atTop (𝓝 0) := by
    apply tendsto_eLpNorm_two_of_dominated_sq (fun n => (hrₙ n).1) (hRm i).restrict
      (integrable_const (1 : ℝ))
    · exact fun n => ae_of_all _ fun x => by nlinarith [hRnorm i (x, uₙ n x), norm_nonneg (rₙ n x)]
    · exact ae_of_all _ fun x => by nlinarith [hRnorm i (x, u x), norm_nonneg (R i (x, u x))]
    · filter_upwards [ae_restrict_le hlim] with x hx
      exact ((hR i).tendsto _).comp (tendsto_const_nhds.prodMk_nhds hx)
  have hdlim := tendsto_eLpNorm_add_of_tendsto
    (fun n => (haₙ n).add (hbₙ n)) hrₙ ((hAmem i K hK).add (hBmem i K hK))
    (hRmem i K hK)
    (tendsto_eLpNorm_add_of_tendsto haₙ hbₙ (hAmem i K hK) (hBmem i K hK) halim hblim) hrlim
  let φ' := fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)
  have hφ' : Continuous φ' := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hmφ : MemLp φ 2 (volume.restrict K) :=
    (hφ.continuous.memLp_of_hasCompactSupport hs).restrict K
  have hmφ' : MemLp φ' 2 (volume.restrict K) :=
    (hφ'.memLp_of_hasCompactSupport (hs.fderiv_apply ℝ _)).restrict K
  have hz : ∀ x, x ∉ K → φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hz' : ∀ x, x ∉ K → φ' x = 0 := fun x hx => by simp [φ', fderiv_of_notMem_tsupport ℝ hx]
  have hweak (n) : (∫ x in K, φ x • (aₙ n x + bₙ n x + rₙ n x)) =
      -(∫ x in K, φ' x • fₙ n x) := by
    rw [← integral_smul_eq_setIntegral _ hz, ← integral_smul_eq_setIntegral _ hz']
    apply integral_smul_lineDeriv_eq_neg_of_ae_regularLine (D := Set.univ)
    · exact ae_of_all _ fun _ _ => Set.mem_univ _
    · intro x _
      exact hline (uₙ n) i x (duₙ i n x)
        (boundedMollification_hasLineDerivAt hui (hu.weak i) n x)
    · exact fun x => (hφ.differentiable (by simp) x).hasFDerivAt.hasLineDerivAt _
    · exact integrable_smul_of_memLp_on_support hmφ' (hfₙ n) hz'
    · exact integrable_smul_of_memLp_on_support hmφ (((haₙ n).add (hbₙ n)).add (hrₙ n)) hz
    · exact integrable_smul_of_memLp_on_support hmφ (hfₙ n) hz
  have hfinal := weak_derivative_identity_closed_eLpNorm hmφ hmφ'
    hfₙ (fun n => ((haₙ n).add (hbₙ n)).add (hrₙ n)) (hFmem K hK)
    (((hAmem i K hK).add (hBmem i K hK)).add (hRmem i K hK))
    hflim hdlim (Eventually.of_forall hweak)
  rw [integral_smul_eq_setIntegral _ hz, integral_smul_eq_setIntegral _ hz']
  exact hfinal

end Chain
end GptLean.Representability
