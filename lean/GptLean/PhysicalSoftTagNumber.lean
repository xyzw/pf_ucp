import GptLean.PhysicalSoftTagging

/-!
Finite photon number of the purifying state, the remaining clause of
`many-electron-pure-approximation`.

Every photon of the tagged vector `Ψ = ∑ₙ T_{fₙ} uₙ` has frequency at least
`κ/2`: the photons of the hard vectors `uₙ` have frequency at least `κ`, and
the shell modes `fₙ` lie in `κ/2 < |k| < κ`. The set of wave functions with
values in the corresponding generated Fock space is closed, so `Ψ(x)` is
supported on frequencies at least `κ/2` for almost every `x`. Hence
`N ≤ (2/κ) H_rad` pointwise, and the mean photon number of `Ψ` is at most
`(2/κ) ‖H_rad^{1/2} Ψ‖² < ∞`.

`pure_approximation` is then `many-electron-pure-approximation` in full: for
every finite-energy density matrix `Γ` and `ε > 0` there is a normalized
fermionic `Ψ` in the form domain with finite mean photon number, the pair of
`Γ`, and energy at most `E(Γ) + ε`.
-/

noncomputable section

namespace GptLean.PhysicalSoftPurification

open MeasureTheory Filter Topology PhysicalFock PhysicalFock.SoftTag PhysicalPFReference
  PhysicalNormalTrace PhysicalClosedForms PhysicalPolarization PhysicalRemovalKernels
  PhysicalSobolevRealization PhysicalPhotonLocalizedNumber PhysicalPairDuality
  Gaussian SymmetricLift PhysicalAttainmentFunctionals PhysicalPFSoftTag
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 800000

attribute [local irreducible] PhysicalPFReference.normalEnergy

section Fock

theorem generatedFockSubspace_mono {V W : Submodule ℂ (Lp ℂ 2 photonMeasure)} (h : V ≤ W) :
    generatedFockSubspace V ≤ generatedFockSubspace W :=
  Submodule.topologicalClosure_mono (Submodule.span_mono fun _ ⟨w, hw, hv⟩ =>
    ⟨w, fun f hf => h (hw f hf), hv⟩)

theorem hardOnePhoton_anti {κ κ' : ℝ} (h : κ' ≤ κ) : hardOnePhoton κ ≤ hardOnePhoton κ' := by
  intro u hu
  have hu' := (MomentumSplit.mem_supported_iff photonMeasure (softMomentumSet κ)ᶜ
    (softMomentumSet_measurable κ).compl u).mp hu
  apply (MomentumSplit.mem_supported_iff photonMeasure (softMomentumSet κ')ᶜ
    (softMomentumSet_measurable κ').compl u).mpr
  filter_upwards [hu'] with p hp hout
  apply hp
  intro hin
  have h1 : NormalPhoton.frequency p < κ' := not_not.mp hout
  exact hin (h1.trans_le h)

theorem mode_mem_hard_half {κ : ℝ} (hκ : 0 < κ) (n : ℕ) :
    PhysicalSoftTagModes.mode hκ n ∈ hardOnePhoton (κ / 2) := by
  apply (MomentumSplit.mem_supported_iff photonMeasure (softMomentumSet (κ / 2))ᶜ
    (softMomentumSet_measurable (κ / 2)).compl _).mpr
  filter_upwards [PhysicalSoftTagModes.mode_support hκ n] with p hp hout
  apply hp
  intro hc
  have h1 : NormalPhoton.frequency p < κ / 2 := not_not.mp hout
  exact absurd h1 (not_lt.mpr (PhysicalSoftTagModes.shell_subset hκ n hc.1).1.le)

/-- A tag stays in every generated space containing its mode and the hard
one-photon space. -/
theorem tagOp_mem_generated {κ : ℝ} (C : CanonicalSectorCCR photonMeasure)
    (BF : StandardSymmetricFockExponential) {f : Lp ℂ 2 photonMeasure}
    (hf : f ∈ softOnePhoton κ) {W : Submodule ℂ (Lp ℂ 2 photonMeasure)} (hfW : f ∈ W)
    (hW : hardOnePhoton κ ≤ W) (u : PhotonFock) :
    tagOp κ C BF hf u ∈ generatedFockSubspace W := by
  apply mem_generated_of_photonSector photonMeasure W
  intro n
  cases n with
  | zero =>
    change lp.single 2 0 (0 : Sector photonMeasure 0) ∈ _
    rw [lp.single_zero]
    exact (generatedFockSubspace W).zero_mem
  | succ n =>
    exact creationBlock_mem_generated photonMeasure W n f hfW (hardProjection κ u)
      (generatedFockSubspace_mono hW (hardProjection_mem κ BF u))

end Fock

section Closed

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Wave functions with values in a closed subspace form a closed set. -/
theorem ae_mem_of_tendsto (W : Submodule ℂ PhotonFock) [CompleteSpace W]
    {v : ℕ → Lp PhotonFock 2 μ} {w : Lp PhotonFock 2 μ}
    (hv : ∀ K, ∀ᵐ x ∂μ, v K x ∈ W) (hlim : Tendsto v atTop (𝓝 w)) :
    ∀ᵐ x ∂μ, w x ∈ W := by
  have hfix : ∀ g : Lp PhotonFock 2 μ, (∀ᵐ x ∂μ, g x ∈ W) →
      W.starProjection.compLpL 2 μ g = g := fun g hg => by
    apply Lp.ext
    filter_upwards [W.starProjection.coeFn_compLpL g, hg] with x h₁ h₂
    exact h₁.trans (W.starProjection_eq_self_iff.mpr h₂)
  have hclosed : IsClosed {g : Lp PhotonFock 2 μ | W.starProjection.compLpL 2 μ g = g} :=
    isClosed_eq (W.starProjection.compLpL 2 μ).continuous continuous_id
  have hw : W.starProjection.compLpL 2 μ w = w :=
    hclosed.mem_of_tendsto hlim (Eventually.of_forall fun K => hfix (v K) (hv K))
  filter_upwards [W.starProjection.coeFn_compLpL w] with x hx
  exact W.starProjection_eq_self_iff.mp
    (hx.symm.trans (congrArg (fun g : Lp PhotonFock 2 μ => g x) hw))

end Closed

section Spatial

variable {I : Type} [Fintype I] [DecidableEq I] (V : PhysicalPFReference.Position I → ℝ)
  (C : CanonicalSectorCCR photonMeasure) (BF : StandardSymmetricFockExponential)
  {κ : ℝ} (hκ : 0 < κ)

/-- Every finite tag superposition has photons of frequency at least `κ/2`. -/
theorem tagSum_mem_half (t : Finset ℕ) (u : ℕ → Reference I V) :
    ∀ᵐ x ∂volume, inclusion I V (tagSum V C BF (PhysicalSoftTagModes.tagFamily hκ) hκ.le t u) x ∈
      generatedFockSubspace (hardOnePhoton (κ / 2)) := by
  filter_upwards [inclusion_tagSum_ae V C BF (PhysicalSoftTagModes.tagFamily hκ) hκ.le t u]
    with x hx
  exact (congrArg (fun z : PhotonFock => z ∈ generatedFockSubspace (hardOnePhoton (κ / 2)))
    hx).mpr (Submodule.sum_mem _ fun j _ =>
      tagOp_mem_generated C BF ((PhysicalSoftTagModes.tagFamily hκ).soft j)
        (mode_mem_hard_half hκ j) (hardOnePhoton_anti (half_le_self hκ.le)) _)

/-- The tagged vector has photons of frequency at least `κ/2`. -/
theorem tagged_mem_half (u : ℕ → Reference I V) {Ψ : Reference I V}
    (hΨ : HasSum (fun n => tagRef V C BF (PhysicalSoftTagModes.tagFamily hκ) hκ.le n (u n)) Ψ) :
    ∀ᵐ x ∂volume, inclusion I V Ψ x ∈ generatedFockSubspace (hardOnePhoton (κ / 2)) :=
  ae_mem_of_tendsto (generatedFockSubspace (hardOnePhoton (κ / 2)))
    (fun K => tagSum_mem_half V C BF hκ (Finset.range K) u)
    (((inclusion I V).continuous.tendsto Ψ).comp hΨ.tendsto_sum_nat)

include hκ in
/-- **Finite photon number**, `∫ N(Ψ(x)) dx ≤ (2/κ) ‖H_rad^{1/2} Ψ‖²`. -/
theorem number_lt_top_of_half (B : StandardNormalTraceBackground) (Ψ : Reference I V)
    (hhalf : ∀ᵐ x ∂volume, inclusion I V Ψ x ∈ generatedFockSubspace (hardOnePhoton (κ / 2))) :
    ∫⁻ x, photonNumberForm photonMeasure (inclusion I V Ψ x) < ⊤ := by
  have h1 : ∀ᵐ x ∂volume, photonNumberForm photonMeasure (inclusion I V Ψ x) ≤
      ENNReal.ofReal (κ / 2)⁻¹ * radiationForm (inclusion I V Ψ x) := by
    filter_upwards [hhalf] with x hx
    exact number_le_inv_mul_radiation (half_pos hκ) _
      (hardSupported_of_mem_generated (κ / 2) _ hx)
  have h2 : ∫⁻ x, radiationForm (inclusion I V Ψ x) =
      ENNReal.ofReal (‖radiation I V Ψ‖ ^ 2) :=
    (PhysicalPhotonMarginal.fullRadiationForm_rankOne B volume (inclusion I V Ψ)).symm.trans
      (PhysicalPhotonMarginal.fullRadiationForm_graph B volume (inclusion I V Ψ)
        (radiation I V Ψ) (radiation_graph I V Ψ))
  calc ∫⁻ x, photonNumberForm photonMeasure (inclusion I V Ψ x)
      ≤ ∫⁻ x, ENNReal.ofReal (κ / 2)⁻¹ * radiationForm (inclusion I V Ψ x) :=
        lintegral_mono_ae h1
    _ = ENNReal.ofReal (κ / 2)⁻¹ * ∫⁻ x, radiationForm (inclusion I V Ψ x) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := by
        rw [h2]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

end Spatial

section Physical

variable {N : ℕ} (i : Fin N) (F : Frame) (χ : ArticleCutoff)
  (C : CanonicalSectorCCR photonMeasure) (B : StandardNormalTraceBackground)
  (S : StandardClosedFormBackground) (e : ℝ)

/-- The mean photon number of a pure state is the integral of its pointwise
photon number. -/
theorem pure_number_eq (p : PureState F χ C B S e (N := N)) :
    PhysicalRemoval.number F χ 1 C B S e
        ((PhysicalPFStates.pureEmbedding i (PhysicalRemoval.potential N 1) C (full F χ N)
          (full_measurable F χ N) (bound F χ) (full_bound F χ N) B S e).toMixed p) =
      ∫⁻ x, photonNumberForm photonMeasure (p.val x) :=
  PhysicalPhotonMarginal.fullNumberForm_rankOne B volume p.val

variable (BF : StandardSymmetricFockExponential)

include BF in
/-- **The tagging step with finite photon number.** -/
theorem tagging_number {κ : ℝ} (hκ : 0 < κ) (r : MixedState F χ C B S e (N := N))
    (hsoft0 : PhysicalRemoval.softEnergy F χ 1 C B S e r κ = 0) :
    ∃ p : PureState F χ C B S e (N := N),
      (PhysicalAttainment.pureModel i F χ C B S e).density p =
        (PhysicalRemoval.model i F χ 1 C B S e).density r ∧
      (PhysicalAttainment.pureModel i F χ C B S e).energy p ≤
        (PhysicalRemoval.model i F χ 1 C B S e).energy r + tagCost N χ e κ ∧
      PhysicalRemoval.number F χ 1 C B S e
        ((PhysicalPFStates.pureEmbedding i (PhysicalRemoval.potential N 1) C (full F χ N)
          (full_measurable F χ N) (bound F χ) (full_bound F χ N) B S e).toMixed p) < ⊤ := by
  have src := Classical.choice (PhysicalPFSource.supported_source_exists N
    (PhysicalRemoval.potential N 1) B C (full F χ N) (full_measurable F χ N) (bound F χ)
    (full_bound F χ N) S e (x := r.val.val) r.val.property.1 r.val.property.2.2 r.property)
  have hu := source_hard F χ C B S e BF r hsoft0 src
  have hsum := tagged_summable (PhysicalRemoval.potential N 1) C BF
    (PhysicalSoftTagModes.tagFamily hκ) hκ.le (full F χ N)
    (PhysicalRemovalKernels.hard F χ N κ) (PhysicalRemovalKernels.soft F χ N κ)
    (full_measurable F χ N) (hard_measurable F χ N κ) (soft_measurable F χ N κ)
    (bound F χ) (bound F χ) (bound F χ) (full_bound F χ N) (hard_bound F χ N κ)
    (soft_bound F χ N κ) (fun b => ae_of_all _ (full_eq_hard_add_soft F χ N κ b))
    (fun b => ae_of_all _ (hard_mem F χ N κ b)) (fun b => ae_of_all _ (soft_mem F χ N κ b))
    e _ (bsq_card_nonneg χ κ) (ae_of_all _ (soft_sum_le F χ hκ.le)) src.vector hu
    src.mass_hasSum.summable
    (src.energy_hasSum C (full F χ N) (full_measurable F χ N) (bound F χ)
      (full_bound F χ N) S e r.val.property.2.2).summable
  have hnorm := tagged_vector_mass F χ C B S e hκ BF r src hu hsum.hasSum
  have hferm := tagged_vector_fermionic F χ C B S e hκ BF r src hsum.hasSum
  have hhalf := tagged_mem_half (PhysicalRemoval.potential N 1) C BF hκ src.vector hsum.hasSum
  refine ⟨referencePure F χ C B S e _ hnorm hferm,
    (referencePure_density i F χ C B S e _ hnorm hferm).trans
      (tagged_vector_pair i F χ C B S e hκ BF r src hu hsum.hasSum),
    (referencePure_energy i F χ C B S e _ hnorm hferm).trans_le
      (tagged_vector_energy i F χ C B S e hκ BF r src hu hsum.hasSum), ?_⟩
  exact (pure_number_eq i F χ C B S e _).trans_lt
    (number_lt_top_of_half (PhysicalRemoval.potential N 1) hκ B _ hhalf)

variable (BW : StandardWienerSegal)
  (core : CountableSpatialTestCore) (smooth : SmoothSobolevBackground)
  (C₀ : ℝ) (scaled : ScaledGradientSobolevBackground (6 + 12 * (N : ℝ)) C₀)
  (B₀ : TensorBackground Repair.SixTag) (B₁ : TensorMultilinearData B₀)
  {ι : Type*} (basis : HilbertBasis ι ℂ (recursiveLiftCandidate B₀ N).target)
  (index : ι ↪ ℕ)

include BF BW core smooth scaled B₀ B₁ basis index in
/-- **`many-electron-pure-approximation`**: for every finite-energy density
matrix `Γ` and every `ε > 0` there is a normalized fermionic `Ψ` in the form
domain with finite mean photon number, `(ρ_Ψ, j_Ψ) = (ρ_Γ, j_Γ)` and
`⟨Ψ, H^{0,0}Ψ⟩ ≤ Tr(H^{0,0}Γ) + ε`. -/
theorem pure_approximation (he : 0 ≤ e) (hC₀ : 0 ≤ C₀) (m : MixedState F χ C B S e (N := N))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : PureState F χ C B S e (N := N),
      (PhysicalAttainment.pureModel i F χ C B S e).density p =
        (PhysicalRemoval.model i F χ 1 C B S e).density m ∧
      (PhysicalAttainment.pureModel i F χ C B S e).energy p ≤
        (PhysicalRemoval.model i F χ 1 C B S e).energy m + ε ∧
      PhysicalRemoval.number F χ 1 C B S e
        ((PhysicalPFStates.pureEmbedding i (PhysicalRemoval.potential N 1) C (full F χ N)
          (full_measurable F χ N) (bound F χ) (full_bound F χ N) B S e).toMixed p) < ⊤ := by
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
      CutoffProfile.bsq photonMeasure NormalPhoton.frequency χ.profile κ) + tagCost N χ e κ)
      (𝓝[>] 0) (𝓝 0) := by
    have hb := CutoffProfile.tendsto_bsq hP.dispersion_measurable hP.dispersion_positive
      hP.cutoff_finite
    simpa using ((hsq.add hb).const_mul G).add (tagCost_tendsto i F χ C B S e)
  have hev : ∀ᶠ κ in 𝓝[>] (0 : ℝ), G * (κ ^ 2 +
      CutoffProfile.bsq photonMeasure NormalPhoton.frequency χ.profile κ) +
        tagCost N χ e κ < ε :=
    hlim (Iio_mem_nhds hε)
  have hsmall : ∀ᶠ κ in 𝓝[>] (0 : ℝ), κ ∈ Set.Ioc 0 κ₀ := Ioc_mem_nhdsGT hκ₀
  obtain ⟨κ, hκε, hκpos, hκle⟩ := (hev.and hsmall).exists
  obtain ⟨r, hpair, henergy, _, hsoft, _, _⟩ := PhysicalRemoval.optimized i F χ 1 zero_le_one
    C B S BF BW e core smooth C₀ scaled B₀ B₁ basis index he hC₀ m κ hκpos (hκle.trans hκ₀1)
  have hr := hgain κ ((PhysicalRemoval.model i F χ 1 C B S e).energy m)
    ((PhysicalRemoval.model i F χ 1 C B S e).energy r)
    (PhysicalRemoval.softEnergy F χ 1 C B S e m κ).toReal hκpos hκle ENNReal.toReal_nonneg
    henergy
  obtain ⟨p, hpd, hpe, hpn⟩ := tagging_number i F χ C B S e BF hκpos r hsoft
  refine ⟨p, hpd.trans hpair, ?_, hpn⟩
  have hs : 0 ≤ (PhysicalRemoval.softEnergy F χ 1 C B S e m κ).toReal := ENNReal.toReal_nonneg
  linarith

end Physical

end GptLean.PhysicalSoftPurification
