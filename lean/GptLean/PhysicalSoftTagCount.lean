import GptLean.PhysicalSoftTagNumber

/-!
Photon number of the soft-photon purification, for the bound
`pure-minimizing-sequence-number-bound` of `cor-many-electron-pure-functional`.

Each soft tag adds exactly one photon. Let `f_j` be orthonormal soft modes and
`u_j` hard Fock vectors. Sector `n + 1` of `∑ⱼ a†(f_j) u_j` is
`∑ⱼ a†(f_j) (u_j)_n`, whose squared norm is `∑ⱼ ‖(u_j)_n‖²`. Hence

`N(∑ⱼ a†(f_j) u_j) = ∑ⱼ (N(u_j) + ‖u_j‖²)`.

Integrating over configurations gives the mean photon number of a finite tag
superposition. The mean photon number is lower semicontinuous on `L²`, so the
tagged vector `Ψ = ∑ₙ T_{fₙ} uₙ` of a density matrix `Γ = ∑ₙ |uₙ⟩⟨uₙ|`
without soft photons satisfies `⟨Ψ, N Ψ⟩ ≤ Tr(N Γ) + 1`. Soft removal keeps
exactly the hard photons, so the pure approximants of
`many-electron-pure-approximation` satisfy `⟨Ψ, N Ψ⟩ ≤ Tr(N Γ) + 1` for the
original density matrix `Γ` (`pure_approximation_count`).
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

section Scalar

theorem ofReal_succ_mul (n : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    ENNReal.ofReal (((n : ℝ) + 1) * a) = ENNReal.ofReal ((n : ℝ) * a) + ENNReal.ofReal a := by
  rw [add_mul, one_mul, ENNReal.ofReal_add (mul_nonneg (Nat.cast_nonneg n) ha) ha]

theorem ofReal_mul_sum {ι : Type*} (s : Finset ι) (c : ℝ) (hc : 0 ≤ c) (a : ι → ℝ)
    (ha : ∀ j, 0 ≤ a j) :
    ENNReal.ofReal (c * ∑ j ∈ s, a j) = ∑ j ∈ s, ENNReal.ofReal (c * a j) := by
  rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun j _ => mul_nonneg hc (ha j)]

end Scalar

section Fock

/-- The photon number as a series over the occupied sectors `n + 1`. -/
theorem number_shift (Q : PhotonFock) :
    photonNumberForm photonMeasure Q =
      ∑' n : ℕ, ENNReal.ofReal (((n : ℝ) + 1) * ‖Q (n + 1)‖ ^ 2) := by
  change (∑' n : ℕ, ENNReal.ofReal ((n : ℝ) * ‖Q n‖ ^ 2)) = _
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [Nat.cast_zero, zero_mul, ENNReal.ofReal_zero, zero_add, Nat.cast_succ]

/-- Raising every sector by one adds the mass to the photon number. -/
theorem number_add_mass (v : PhotonFock) :
    ∑' n : ℕ, ENNReal.ofReal (((n : ℝ) + 1) * ‖v n‖ ^ 2) =
      photonNumberForm photonMeasure v + ENNReal.ofReal (‖v‖ ^ 2) := by
  have hm := coordinate_mass_hasSum (Sector photonMeasure) v
  calc ∑' n : ℕ, ENNReal.ofReal (((n : ℝ) + 1) * ‖v n‖ ^ 2)
      = ∑' n : ℕ, (ENNReal.ofReal ((n : ℝ) * ‖v n‖ ^ 2) + ENNReal.ofReal (‖v n‖ ^ 2)) :=
        tsum_congr fun n => ofReal_succ_mul n _ (sq_nonneg _)
    _ = (∑' n : ℕ, ENNReal.ofReal ((n : ℝ) * ‖v n‖ ^ 2)) +
          ∑' n : ℕ, ENNReal.ofReal (‖v n‖ ^ 2) := ENNReal.tsum_add
    _ = photonNumberForm photonMeasure v + ENNReal.ofReal (‖v‖ ^ 2) :=
        congrArg₂ (· + ·) rfl
          ((ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) hm.summable).symm.trans
            (congrArg ENNReal.ofReal hm.tsum_eq))

theorem sum_coord {ι : Type*} (s : Finset ι) (g : ι → PhotonFock) (n : ℕ) :
    (∑ j ∈ s, g j) n = ∑ j ∈ s, g j n := by
  rw [lp.coeFn_sum, Finset.sum_apply]

variable (C : CanonicalSectorCCR photonMeasure) (BF : StandardSymmetricFockExponential)
  {κ : ℝ} {ι : Type*} {f : ι → Lp ℂ 2 photonMeasure} (hF : TagFamily κ f) (s : Finset ι)
  (u : ι → PhotonFock) (hu : ∀ j, u j ∈ generatedFockSubspace (hardOnePhoton κ))

include hu in
/-- Sector `n + 1` of a tag superposition has the mass of sector `n` of the
tagged vectors. -/
theorem tag_sum_coord_norm_sq (n : ℕ) :
    ‖(∑ j ∈ s, tagOp κ C BF (hF.soft j) (u j)) (n + 1)‖ ^ 2 = ∑ j ∈ s, ‖u j n‖ ^ 2 := by
  have hc : (∑ j ∈ s, tagOp κ C BF (hF.soft j) (u j)) (n + 1) =
      ∑ j ∈ s, creationSector photonMeasure n (f j) (u j n) :=
    (sum_coord s _ (n + 1)).trans (Finset.sum_congr rfl fun j _ =>
      tagOp_succ_coord_hard κ C BF (hF.soft j) (u j) (hu j) n)
  have hi : ⟪∑ j ∈ s, creationSector photonMeasure n (f j) (u j n),
      ∑ j ∈ s, creationSector photonMeasure n (f j) (u j n)⟫_ℂ = ∑ j ∈ s, ⟪u j n, u j n⟫_ℂ := by
    refine (inner_sum_of_cross s _ _ fun j _ l _ hjl => ?_).trans
      (Finset.sum_congr rfl fun j _ => ?_)
    · exact (creation_inner C (hardOnePhoton κ) (soft_mem_hard_orthogonal κ (hF.soft j))
        (hu l) n).trans ((congrArg (· * ⟪u j n, u l n⟫_ℂ) (hF.orthogonal j l hjl)).trans
          (zero_mul _))
    · exact (creation_inner C (hardOnePhoton κ) (soft_mem_hard_orthogonal κ (hF.soft j))
        (hu j) n).trans ((congrArg (· * ⟪u j n, u j n⟫_ℂ) (hF.inner_self j)).trans (one_mul _))
  have h := congrArg Complex.re hi
  rw [re_inner_self, Complex.re_sum] at h
  exact (congrArg (fun z => ‖z‖ ^ 2) hc).trans
    (h.trans (Finset.sum_congr rfl fun j _ => re_inner_self (u j n)))

include hu in
/-- **Each tag adds one photon**, `N(∑ⱼ a†(f_j) u_j) = ∑ⱼ (N(u_j) + ‖u_j‖²)`. -/
theorem number_tag_sum :
    photonNumberForm photonMeasure (∑ j ∈ s, tagOp κ C BF (hF.soft j) (u j)) =
      ∑ j ∈ s, (photonNumberForm photonMeasure (u j) + ENNReal.ofReal (‖u j‖ ^ 2)) := by
  refine (number_shift _).trans ?_
  calc ∑' n : ℕ, ENNReal.ofReal (((n : ℝ) + 1) *
        ‖(∑ j ∈ s, tagOp κ C BF (hF.soft j) (u j)) (n + 1)‖ ^ 2)
      = ∑' n : ℕ, ∑ j ∈ s, ENNReal.ofReal (((n : ℝ) + 1) * ‖u j n‖ ^ 2) :=
        tsum_congr fun n => (congrArg (fun a => ENNReal.ofReal (((n : ℝ) + 1) * a))
          (tag_sum_coord_norm_sq C BF hF s u hu n)).trans
          (ofReal_mul_sum s _ (by positivity) (fun j => ‖u j n‖ ^ 2) fun j => sq_nonneg _)
    _ = ∑ j ∈ s, ∑' n : ℕ, ENNReal.ofReal (((n : ℝ) + 1) * ‖u j n‖ ^ 2) :=
        Summable.tsum_finsetSum fun _ _ => ENNReal.summable
    _ = _ := Finset.sum_congr rfl fun j _ => number_add_mass (u j)

end Fock

section Spatial

variable {I : Type} [Fintype I] [DecidableEq I] (V : Position I → ℝ)
  (C : CanonicalSectorCCR photonMeasure) (BF : StandardSymmetricFockExponential)

omit [DecidableEq I] in
theorem number_aemeasurable (w : WaveSpace I) :
    AEMeasurable (fun x => photonNumberForm photonMeasure (w x)) volume := by
  have h (n : ℕ) : AEMeasurable (fun x => ENNReal.ofReal ((n : ℝ) * ‖(w x) n‖ ^ 2)) volume := by
    have hs : AEStronglyMeasurable (fun x => sector (Sector photonMeasure) n (w x)) volume :=
      (sector (Sector photonMeasure) n).continuous.comp_aestronglyMeasurable
        (Lp.aestronglyMeasurable w)
    exact ((hs.norm.aemeasurable.pow_const 2).const_mul (n : ℝ)).ennreal_ofReal.congr
      (ae_of_all _ fun x => by simp only [sector_norm])
  exact AEMeasurable.tsum h

omit [DecidableEq I] in
theorem mass_lintegral (w : WaveSpace I) :
    ∫⁻ x, ENNReal.ofReal (‖w x‖ ^ 2) = ENNReal.ofReal (‖w‖ ^ 2) :=
  ((congrArg ENNReal.ofReal (norm_sq_eq_integral w)).trans
    (ofReal_integral_eq_lintegral_ofReal (integrable_norm_sq w)
      (ae_of_all _ fun _ => sq_nonneg _))).symm

omit [DecidableEq I] in
/-- The mean photon number is lower semicontinuous on `L²`. -/
theorem number_lowerSemicontinuous (B : StandardNormalTraceBackground) :
    LowerSemicontinuous (fun w : WaveSpace I => ∫⁻ x, photonNumberForm photonMeasure (w x)) := by
  have h : (fun w : WaveSpace I => ∫⁻ x, photonNumberForm photonMeasure (w x)) = fun w =>
      ⨆ n, ENNReal.ofReal ((PhysicalPhotonMarginal.fullForm B volume
        (NormalPhoton.numberForm B.normal (B.realization PhotonFock).functional)).truncation n
          ((B.realization (WaveSpace I)).rank.rankOne w)) :=
    funext fun w => (PhysicalPhotonMarginal.fullNumberForm_rankOne B volume w).symm
  rw [h]
  exact lowerSemicontinuous_iSup fun n => (ENNReal.continuous_ofReal.comp
    (((PhysicalPhotonMarginal.fullForm B volume (NormalPhoton.numberForm B.normal
      (B.realization PhotonFock).functional)).truncation n).continuous.comp
        (B.realization (WaveSpace I)).rank.continuous_rankOne)).lowerSemicontinuous

variable {κ : ℝ} {ι : Type*} [Countable ι] {f : ι → Lp ℂ 2 photonMeasure}
  (hF : TagFamily κ f) (hκ : 0 ≤ κ) (t : Finset ι) (u : ι → Reference I V)
  (hu : ∀ j, ∀ᵐ x ∂volume, inclusion I V (u j) x ∈ generatedFockSubspace (hardOnePhoton κ))

include hu in
/-- The mean photon number of a finite tag superposition. -/
theorem number_tagSum :
    ∫⁻ x, photonNumberForm photonMeasure (inclusion I V (tagSum V C BF hF hκ t u) x) =
      ∑ j ∈ t, ((∫⁻ x, photonNumberForm photonMeasure (inclusion I V (u j) x)) +
        ENNReal.ofReal (‖inclusion I V (u j)‖ ^ 2)) := by
  have h : (fun x => photonNumberForm photonMeasure (inclusion I V (tagSum V C BF hF hκ t u) x))
      =ᵐ[volume] fun x => ∑ j ∈ t, (photonNumberForm photonMeasure (inclusion I V (u j) x) +
        ENNReal.ofReal (‖inclusion I V (u j) x‖ ^ 2)) := by
    filter_upwards [inclusion_tagSum_ae V C BF hF hκ t u, ae_all_iff.mpr hu] with x h₁ h₂
    exact (congrArg (photonNumberForm photonMeasure) h₁).trans
      (number_tag_sum C BF hF t (fun j => inclusion I V (u j) x) h₂)
  refine (lintegral_congr_ae h).trans ((lintegral_finsetSum' t fun j _ =>
    (number_aemeasurable (inclusion I V (u j))).add
      ((Lp.aestronglyMeasurable _).norm.aemeasurable.pow_const 2).ennreal_ofReal).trans
    (Finset.sum_congr rfl fun j _ => ?_))
  exact (lintegral_add_left' (number_aemeasurable (inclusion I V (u j))) _).trans
    (congrArg₂ (· + ·) rfl (mass_lintegral (inclusion I V (u j))))

end Spatial

section Series

variable {I : Type} [Fintype I] [DecidableEq I] (V : Position I → ℝ)
  (C : CanonicalSectorCCR photonMeasure) (BF : StandardSymmetricFockExponential)
  {κ : ℝ} {f : ℕ → Lp ℂ 2 photonMeasure} (hF : TagFamily κ f) (hκ : 0 ≤ κ)
  (u : ℕ → Reference I V)
  (hu : ∀ j, ∀ᵐ x ∂volume, inclusion I V (u j) x ∈ generatedFockSubspace (hardOnePhoton κ))
  {Ψ : Reference I V} (hΨ : HasSum (fun n => tagRef V C BF hF hκ n (u n)) Ψ)

include hu hΨ in
/-- The tagged vector has at most the photons of the `uₙ` plus their masses. -/
theorem tagged_number_le (B : StandardNormalTraceBackground) :
    ∫⁻ x, photonNumberForm photonMeasure (inclusion I V Ψ x) ≤
      ∑' n, ((∫⁻ x, photonNumberForm photonMeasure (inclusion I V (u n) x)) +
        ENNReal.ofReal (‖inclusion I V (u n)‖ ^ 2)) := by
  have hclosed := (number_lowerSemicontinuous (I := I) B).isClosed_preimage
    (∑' n, ((∫⁻ x, photonNumberForm photonMeasure (inclusion I V (u n) x)) +
      ENNReal.ofReal (‖inclusion I V (u n)‖ ^ 2)))
  exact hclosed.mem_of_tendsto (((inclusion I V).continuous.tendsto Ψ).comp hΨ.tendsto_sum_nat)
    (Eventually.of_forall fun K => (number_tagSum V C BF hF hκ (Finset.range K) u hu).trans_le
      (ENNReal.sum_le_tsum (Finset.range K)))

end Series

section Physical

variable {N : ℕ} (i : Fin N) (F : Frame) (χ : ArticleCutoff)
  (C : CanonicalSectorCCR photonMeasure) (B : StandardNormalTraceBackground)
  (S : StandardClosedFormBackground) (e : ℝ)

/-- The mean photon number of a density matrix is the sum over a spectral source. -/
theorem number_source (r : MixedState F χ C B S e (N := N))
    (src : PhysicalPFSource.SupportedSource N (PhysicalRemoval.potential N 1) B r.val.val) :
    PhysicalRemoval.number F χ 1 C B S e r =
      ∑' n, ∫⁻ x, photonNumberForm photonMeasure
        (inclusion (Fin N × Fin 3) (PhysicalRemoval.potential N 1) (src.vector n) x) :=
  (PhysicalPhotonMarginal.fullMomentumForm_source B volume (fun _ => 1) measurable_const
    src.hasSum).trans (tsum_congr fun _ => lintegral_congr fun _ => photonMoment_one _)

/-- The hard photon number is at most the photon number. -/
theorem hardNumber_le_number (m : MixedState F χ C B S e (N := N)) (κ : ℝ) :
    PhysicalRemoval.hardNumber F χ 1 C B S e m κ ≤ PhysicalRemoval.number F χ 1 C B S e m :=
  (NormalPhoton.density_hardNumber B.normal (B.realization PhotonFock).functional κ _
    (PhysicalPhotonMarginal.marginal_positive B volume m.val.property.1)).trans_le
    ((setLIntegral_le_lintegral _ _).trans_eq
      (NormalPhoton.density_number B.normal (B.realization PhotonFock).functional _
        (PhysicalPhotonMarginal.marginal_positive B volume m.val.property.1)).symm)

section TaggedVector

variable {κ : ℝ} (hκ : 0 < κ) (BF : StandardSymmetricFockExponential)
  (r : MixedState F χ C B S e (N := N))
  (src : PhysicalPFSource.SupportedSource N (PhysicalRemoval.potential N 1) B r.val.val)
  (hu : ∀ n, ∀ᵐ x ∂volume, inclusion (Fin N × Fin 3) (PhysicalRemoval.potential N 1)
    (src.vector n) x ∈ generatedFockSubspace (hardOnePhoton κ))
  {Ψ : Reference (Fin N × Fin 3) (PhysicalRemoval.potential N 1)}
  (hΨ : HasSum (fun n => tagRef (PhysicalRemoval.potential N 1) C BF
    (PhysicalSoftTagModes.tagFamily hκ) hκ.le n (src.vector n)) Ψ)

include hu hΨ in
/-- **Photon number of the tagged vector**, `⟨Ψ, N Ψ⟩ ≤ Tr(N Γ) + 1`. -/
theorem tagged_vector_number :
    ∫⁻ x, photonNumberForm photonMeasure
        (inclusion (Fin N × Fin 3) (PhysicalRemoval.potential N 1) Ψ x) ≤
      PhysicalRemoval.number F χ 1 C B S e r + 1 :=
  (tagged_number_le (PhysicalRemoval.potential N 1) C BF (PhysicalSoftTagModes.tagFamily hκ)
    hκ.le src.vector hu hΨ B).trans_eq (ENNReal.tsum_add.trans
      (congrArg₂ (· + ·) (number_source F χ C B S e r src).symm
        ((ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) src.mass_hasSum.summable).symm.trans
          ((congrArg ENNReal.ofReal (src.mass_hasSum.tsum_eq.trans r.val.property.2.1)).trans
            ENNReal.ofReal_one))))

end TaggedVector

variable (BF : StandardSymmetricFockExponential)

include BF in
/-- **The tagging step with the photon-number bound.** -/
theorem tagging_count {κ : ℝ} (hκ : 0 < κ) (r : MixedState F χ C B S e (N := N))
    (hsoft0 : PhysicalRemoval.softEnergy F χ 1 C B S e r κ = 0) :
    ∃ p : PureState F χ C B S e (N := N),
      (PhysicalAttainment.pureModel i F χ C B S e).density p =
        (PhysicalRemoval.model i F χ 1 C B S e).density r ∧
      (PhysicalAttainment.pureModel i F χ C B S e).energy p ≤
        (PhysicalRemoval.model i F χ 1 C B S e).energy r + tagCost N χ e κ ∧
      PhysicalRemoval.number F χ 1 C B S e
          ((PhysicalPFStates.pureEmbedding i (PhysicalRemoval.potential N 1) C (full F χ N)
            (full_measurable F χ N) (bound F χ) (full_bound F χ N) B S e).toMixed p) ≤
        PhysicalRemoval.number F χ 1 C B S e r + 1 ∧
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
      (tagged_vector_energy i F χ C B S e hκ BF r src hu hsum.hasSum), ?_, ?_⟩
  · exact (pure_number_eq i F χ C B S e _).trans_le
      (tagged_vector_number F χ C B S e hκ BF r src hu hsum.hasSum)
  · exact (pure_number_eq i F χ C B S e _).trans_lt
      (number_lt_top_of_half (PhysicalRemoval.potential N 1) hκ B _ hhalf)

variable (BW : StandardWienerSegal)
  (core : CountableSpatialTestCore) (smooth : SmoothSobolevBackground)
  (C₀ : ℝ) (scaled : ScaledGradientSobolevBackground (6 + 12 * (N : ℝ)) C₀)
  (B₀ : TensorBackground Repair.SixTag) (B₁ : TensorMultilinearData B₀)
  {ι : Type*} (basis : HilbertBasis ι ℂ (recursiveLiftCandidate B₀ N).target)
  (index : ι ↪ ℕ)

include BF BW core smooth scaled B₀ B₁ basis index in
/-- **`many-electron-pure-approximation` with the photon-number bound**: for
every finite-energy density matrix `Γ` and every `ε > 0` there is a normalized
fermionic `Ψ` in the form domain with `(ρ_Ψ, j_Ψ) = (ρ_Γ, j_Γ)`,
`⟨Ψ, H^{0,0}Ψ⟩ ≤ Tr(H^{0,0}Γ) + ε`, `⟨Ψ, N Ψ⟩ ≤ Tr(N Γ) + 1` and
`⟨Ψ, N Ψ⟩ < ∞`. -/
theorem pure_approximation_count (he : 0 ≤ e) (hC₀ : 0 ≤ C₀)
    (m : MixedState F χ C B S e (N := N)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : PureState F χ C B S e (N := N),
      (PhysicalAttainment.pureModel i F χ C B S e).density p =
        (PhysicalRemoval.model i F χ 1 C B S e).density m ∧
      (PhysicalAttainment.pureModel i F χ C B S e).energy p ≤
        (PhysicalRemoval.model i F χ 1 C B S e).energy m + ε ∧
      PhysicalRemoval.number F χ 1 C B S e
          ((PhysicalPFStates.pureEmbedding i (PhysicalRemoval.potential N 1) C (full F χ N)
            (full_measurable F χ N) (bound F χ) (full_bound F χ N) B S e).toMixed p) ≤
        PhysicalRemoval.number F χ 1 C B S e m + 1 ∧
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
  obtain ⟨r, hpair, henergy, hnum, hsoft, _, _⟩ := PhysicalRemoval.optimized i F χ 1
    zero_le_one C B S BF BW e core smooth C₀ scaled B₀ B₁ basis index he hC₀ m κ hκpos
    (hκle.trans hκ₀1)
  have hr := hgain κ ((PhysicalRemoval.model i F χ 1 C B S e).energy m)
    ((PhysicalRemoval.model i F χ 1 C B S e).energy r)
    (PhysicalRemoval.softEnergy F χ 1 C B S e m κ).toReal hκpos hκle ENNReal.toReal_nonneg
    henergy
  obtain ⟨p, hpd, hpe, hpn, hfin⟩ := tagging_count i F χ C B S e BF hκpos r hsoft
  refine ⟨p, hpd.trans hpair, ?_,
    hpn.trans (add_le_add (hnum.trans_le (hardNumber_le_number F χ C B S e m κ)) le_rfl), hfin⟩
  have hs : 0 ≤ (PhysicalRemoval.softEnergy F χ 1 C B S e m κ).toReal := ENNReal.toReal_nonneg
  linarith

end Physical

end GptLean.PhysicalSoftPurification
