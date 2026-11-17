import GptLean.PhysicalZeroCurrent

/-!
`thm-many-electron-soft-purification` on the actual fermionic Pauli--Fierz
model, reduced to its tagging step.

The article's proof has two steps. First, `lem-exact-soft-removal` replaces a
finite-energy density matrix by one with the same density and combined
current, no soft photons and nearly the same energy. On the actual model this
is `PhysicalRemoval.optimized`, and `InfraredRepair.exists_profile_gain` turns
its estimate into `E(Γ_κ) ≤ E(Γ) + G (κ² + b_κ²)`. Second, a density matrix
without soft photons, `Γ_κ = ∑_r p_r |Φ_r ⊗ Ω_<⟩⟨Φ_r ⊗ Ω_<|`, is purified by
orthonormal one-photon soft tags, `Ψ_κ = ∑_r √p_r Φ_r ⊗ a†(f_r) Ω_<`, with the
same pair and energy at most `E(Γ_κ) + t(κ)`, `t(κ) → 0`.

This file proves that the second step, stated as `TaggingInput`, implies the
exact-pair recovery `many-electron-pure-approximation` and all conclusions of
the theorem: `F_LL = F̃_L = F_L`, equality of pure and mixed representability,
the rank-one characterization of pure attainment, and the pure form of
`prop-zero-current-density-functional`. The removal step is proved, not
assumed. `PhysicalSoftTagging.tagging_input` proves the tagging step, and
`PhysicalSoftTagging` and `PhysicalSoftTagNumber` state the unconditional
conclusions.
-/

noncomputable section

namespace GptLean.PhysicalSoftPurification

open MeasureTheory Filter Topology PhysicalFock PhysicalNormalTrace PhysicalClosedForms
  PhysicalPolarization PhysicalRemovalKernels PhysicalSobolevRealization
  PhysicalPhotonLocalizedNumber PhysicalPairSpace PhysicalPairDuality
  Gaussian SymmetricLift PhysicalAttainmentFunctionals
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 800000

attribute [local irreducible] PhysicalPFReference.normalEnergy

variable {N : ℕ} (i : Fin N) (F : Frame) (χ : ArticleCutoff)
  (C : CanonicalSectorCCR photonMeasure) (B : StandardNormalTraceBackground)
  (S : StandardClosedFormBackground) (e : ℝ)

/-- The tagging step of `thm-many-electron-soft-purification`: every
finite-energy density matrix without photons of frequency below `κ` has a
pure representative with the same density and combined current, at energy
cost at most `t κ`. -/
def TaggingInput (t : ℝ → ℝ) : Prop :=
  ∀ κ : ℝ, 0 < κ → κ ≤ 1 → ∀ r : MixedState F χ C B S e (N := N),
    PhysicalRemoval.softEnergy F χ 1 C B S e r κ = 0 →
    ∃ p : PureState F χ C B S e (N := N),
      (PhysicalAttainment.pureModel i F χ C B S e).density p =
        (PhysicalRemoval.model i F χ 1 C B S e).density r ∧
      (PhysicalAttainment.pureModel i F χ C B S e).energy p ≤
        (PhysicalRemoval.model i F χ 1 C B S e).energy r + t κ

variable (BF : StandardSymmetricFockExponential) (BW : StandardWienerSegal)
  (core : CountableSpatialTestCore) (smooth : SmoothSobolevBackground)
  (C₀ : ℝ) (scaled : ScaledGradientSobolevBackground (6 + 12 * (N : ℝ)) C₀)
  (B₀ : TensorBackground Repair.SixTag) (B₁ : TensorMultilinearData B₀)
  {ι : Type*} (basis : HilbertBasis ι ℂ (recursiveLiftCandidate B₀ N).target)
  (index : ι ↪ ℕ) (Sob : StandardHomogeneousSobolev)
  (Rellich : PhysicalRellichFourier.StandardSupportedHalfRellich)
  (Hardy : StandardFractionalHardy)
  (hLp : StandardFiniteDimensionalLpRepresentation) (hFM : StandardDualFenchelMoreau)

include BF BW core smooth scaled B₀ B₁ basis index in
/-- **`many-electron-pure-approximation` from the tagging step.** Soft removal
followed by tagging gives, for every finite-energy density matrix and every
`ε > 0`, a pure state with exactly the same pair and energy below `E + ε`. -/
theorem exactRecovery_of_tagging (he : 0 ≤ e) (hC₀ : 0 ≤ C₀) {t : ℝ → ℝ}
    (ht : Tendsto t (𝓝[>] 0) (𝓝 0)) (htag : TaggingInput i F χ C B S e t) :
    DFT.ExactRecovery (PhysicalAttainment.pureModel i F χ C B S e)
      (PhysicalRemoval.model i F χ 1 C B S e) := by
  intro m ε hε
  have hP := PhysicalRemoval.moments i F χ 1 C B S e
  obtain ⟨κ₀, G, hκ₀, hκ₀1, _, hgain⟩ := InfraredRepair.exists_profile_gain
    hP.dispersion_measurable hP.dispersion_positive hP.weighted_finite
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (RemovalEnergy.latticeRemovalConstant_nonneg N C₀))
    he
  have hsq : Tendsto (fun κ : ℝ => κ ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun κ : ℝ => κ ^ 2) (𝓝 0) (𝓝 ((0 : ℝ) ^ 2)) :=
      (continuous_pow 2).tendsto 0
    rw [zero_pow two_ne_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun κ => G * (κ ^ 2 +
      CutoffProfile.bsq photonMeasure NormalPhoton.frequency χ.profile κ) + t κ)
      (𝓝[>] 0) (𝓝 0) := by
    have hb := CutoffProfile.tendsto_bsq hP.dispersion_measurable hP.dispersion_positive
      hP.cutoff_finite
    simpa using ((hsq.add hb).const_mul G).add ht
  have hev : ∀ᶠ κ in 𝓝[>] (0 : ℝ), G * (κ ^ 2 +
      CutoffProfile.bsq photonMeasure NormalPhoton.frequency χ.profile κ) + t κ < ε :=
    hlim (Iio_mem_nhds hε)
  have hsmall : ∀ᶠ κ in 𝓝[>] (0 : ℝ), κ ∈ Set.Ioc 0 κ₀ := Ioc_mem_nhdsGT hκ₀
  obtain ⟨κ, hκε, hκpos, hκle⟩ := (hev.and hsmall).exists
  obtain ⟨r, hpair, henergy, _, hsoft, _, _⟩ := PhysicalRemoval.optimized i F χ 1 zero_le_one
    C B S BF BW e core smooth C₀ scaled B₀ B₁ basis index he hC₀ m κ hκpos (hκle.trans hκ₀1)
  have hr := hgain κ ((PhysicalRemoval.model i F χ 1 C B S e).energy m)
    ((PhysicalRemoval.model i F χ 1 C B S e).energy r)
    (PhysicalRemoval.softEnergy F χ 1 C B S e m κ).toReal hκpos hκle ENNReal.toReal_nonneg
    henergy
  obtain ⟨p, hpd, hpe⟩ := htag κ hκpos (hκle.trans hκ₀1) r hsoft
  refine ⟨p, hpd.trans hpair, ?_⟩
  have hs : 0 ≤ (PhysicalRemoval.softEnergy F χ 1 C B S e m κ).toReal := ENNReal.toReal_nonneg
  linarith

include BF BW core smooth scaled B₀ B₁ basis index Sob Rellich Hardy hLp hFM in
/-- **`thm-many-electron-soft-purification`, given the tagging step.**
`F_LL = F̃_L = F_L` at every pair, the pure and mixed representability classes
coincide, and at every pair the pure infimum is attained exactly when the
mixed problem has a rank-one minimizer. -/
theorem soft_purification (he : 0 ≤ e) (hC₀ : 0 ≤ C₀) {t : ℝ → ℝ}
    (ht : Tendsto t (𝓝[>] 0) (𝓝 0)) (htag : TaggingInput i F χ C B S e t) :
    (∀ d, pureFunctional i F χ C B S e d = mixedFunctional i F χ C B S e d) ∧
    (∀ d, pureFunctional i F χ C B S e d = liebFunctional i F χ C B S e d) ∧
    Set.range (PhysicalAttainment.pureModel i F χ C B S e).density =
      Set.range (PhysicalRemoval.model i F χ 1 C B S e).density ∧
    (∀ d, DFT.Attained (PhysicalAttainment.pureModel i F χ C B S e) d ↔
      ∃ m, m ∈ Set.range (PhysicalPFStates.pureEmbedding i (PhysicalRemoval.potential N 1) C
          (full F χ N) (full_measurable F χ N) (bound F χ) (full_bound F χ N) B S e).toMixed ∧
        (PhysicalRemoval.model i F χ 1 C B S e).density m = d ∧
        ((PhysicalRemoval.model i F χ 1 C B S e).energy m : EReal) =
          DFT.search (PhysicalRemoval.model i F χ 1 C B S e) d) := by
  have recovery := exactRecovery_of_tagging i F χ C B S e BF BW core smooth C₀ scaled B₀ B₁
    basis index he hC₀ ht htag
  let emb := PhysicalPFStates.pureEmbedding i (PhysicalRemoval.potential N 1) C
    (full F χ N) (full_measurable F χ N) (bound F χ) (full_bound F χ N) B S e
  obtain ⟨_, _, _, _, _, heq⟩ := unrestricted_attainment i F χ C B S e BF BW core smooth C₀
    scaled B₀ B₁ basis index Sob Rellich Hardy hLp hFM he hC₀
  have hpm : ∀ d, pureFunctional i F χ C B S e d = mixedFunctional i F χ C B S e d :=
    DFT.pure_eq_mixed _ _ emb recovery
  exact ⟨hpm, fun d => (hpm d).trans (heq d), DFT.pure_mixed_representability _ _ emb recovery,
    fun d => DFT.pure_attained_iff_rank_one _ _ emb recovery d⟩

include BF BW core smooth scaled B₀ B₁ basis index Sob Rellich Hardy hLp hFM in
/-- **`zero-current-pure-density-search` from the tagging step.** -/
theorem pure_zero_current_of_tagging (he : 0 ≤ e) (hC₀ : 0 ≤ C₀) {t : ℝ → ℝ}
    (ht : Tendsto t (𝓝[>] 0) (𝓝 0)) (htag : TaggingInput i F χ C B S e t) (ρ : Density) :
    pureFunctional i F χ C B S e (ρ, 0) =
        PhysicalZeroCurrent.densityPureFunctional i F χ C B S e ρ ∧
      pureFunctional i F χ C B S e (ρ, 0) = liebFunctional i F χ C B S e (ρ, 0) :=
  PhysicalZeroCurrent.pure_zero_current i F χ C B S e BF BW core smooth C₀ scaled B₀ B₁ basis
    index Sob Rellich Hardy hLp hFM he hC₀
    (exactRecovery_of_tagging i F χ C B S e BF BW core smooth C₀ scaled B₀ B₁ basis index he
      hC₀ ht htag) ρ

end GptLean.PhysicalSoftPurification
