import GptLean.PhysicalSoftPurification
import GptLean.PhysicalPFSoftTag
import GptLean.PhysicalSoftTagModes

/-!
The tagging step of `thm-many-electron-soft-purification` on the actual
fermionic Pauli--Fierz model, and the unconditional conclusions.

Let `Γ` be a finite-energy density matrix without photons below `κ`, with a
fermionic spectral source `Γ = ∑ₙ |uₙ⟩⟨uₙ|` (unnormalized `uₙ`). Zero soft
photon energy makes every `uₙ(x)` hard. With the shell modes `fₙ` below `κ`,

`Ψ = ∑ₙ T_{fₙ} uₙ`

converges in the reference domain: the partial sums obey
`‖∑_{n∈t} T_{fₙ} uₙ‖² ≤ K² ∑_{n∈t} ((1 + c) ‖uₙ‖² + E(uₙ))` with the graph
comparison constant `K`. The limit is a normalized fermionic vector with the
density and current of `Γ` and

`E(Ψ) ≤ E(Γ) + κ + (3/2) e² · 3N · b_κ²`,

where `b_κ² = ∫_{ω<κ} χ²` bounds the squared soft kernel of each electron
coordinate. This is `TaggingInput` with a cost that vanishes as `κ → 0`, so
the exact-pair recovery `many-electron-pure-approximation`, all conclusions of
`thm-many-electron-soft-purification`, and the pure form of
`prop-zero-current-density-functional` hold without further hypotheses.
-/

noncomputable section

namespace GptLean.PhysicalSoftPurification

open MeasureTheory Filter Topology PhysicalFock PhysicalFock.SoftTag PhysicalPFReference
  PhysicalNormalTrace PhysicalClosedForms PhysicalPolarization PhysicalRemovalKernels
  PhysicalSobolevRealization PhysicalPhotonLocalizedNumber PhysicalPairDuality
  Gaussian SymmetricLift PhysicalAttainmentFunctionals PhysicalPFSoftTag
  PhysicalSourceCoordinates
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 800000

attribute [local irreducible] PhysicalPFReference.normalEnergy

section Series

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]

/-- A series whose finite partial sums are controlled by a summable
nonnegative series in square norm is summable. -/
theorem summable_of_sq_bound (g : ℕ → E) (a : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (ha : Summable a) (hnn : ∀ n, 0 ≤ a n)
    (hb : ∀ t : Finset ℕ, ‖∑ n ∈ t, g n‖ ^ 2 ≤ K * ∑ n ∈ t, a n) : Summable g := by
  apply summable_iff_vanishing_norm.mpr
  intro ε hε
  have hδ : 0 < ε ^ 2 / (K + 1) := by positivity
  obtain ⟨s₀, hs₀⟩ := summable_iff_vanishing_norm.mp ha (ε ^ 2 / (K + 1)) hδ
  refine ⟨s₀, fun t ht => ?_⟩
  have h2 : ∑ n ∈ t, a n < ε ^ 2 / (K + 1) := by
    have h := hs₀ t ht
    rwa [Real.norm_of_nonneg (Finset.sum_nonneg fun n _ => hnn n)] at h
  have h3 : ‖∑ n ∈ t, g n‖ ^ 2 < ε ^ 2 := by
    calc ‖∑ n ∈ t, g n‖ ^ 2 ≤ K * ∑ n ∈ t, a n := hb t
      _ ≤ K * (ε ^ 2 / (K + 1)) := mul_le_mul_of_nonneg_left h2.le hK
      _ < ε ^ 2 := by
          rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
          nlinarith [sq_pos_of_pos hε]
  exact lt_of_pow_lt_pow_left₀ 2 hε.le h3

/-- The diagonal of a bounded bilinear map is continuous. -/
theorem diag_continuous {Q P : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (f : Q →L[ℝ] Q →L[ℝ] P) :
    Continuous (fun q => f q q) :=
  f.continuous₂.comp (continuous_id.prodMk continuous_id)

end Series

section Generic

variable {N : ℕ} (i : Fin N) (V : PhysicalPFReference.Position (Fin N × Fin 3) → ℝ)
  (C : CanonicalSectorCCR photonMeasure) (BF : StandardSymmetricFockExponential)
  {κ : ℝ} {f : ℕ → Lp ℂ 2 photonMeasure} (hF : TagFamily κ f) (hκ : 0 ≤ κ)
  (k h s : Fin N × Fin 3 → PhysicalPFReference.Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hk : ∀ b, AEStronglyMeasurable (k b) volume)
  (hh : ∀ b, AEStronglyMeasurable (h b) volume)
  (hs : ∀ b, AEStronglyMeasurable (s b) volume)
  (Mk Mh Ms : ℝ)
  (hMk : ∀ b, ∀ᵐ x ∂volume, ‖k b x‖ ≤ Mk)
  (hMh : ∀ b, ∀ᵐ x ∂volume, ‖h b x‖ ≤ Mh)
  (hMs : ∀ b, ∀ᵐ x ∂volume, ‖s b x‖ ≤ Ms)
  (hsplit : ∀ b, ∀ᵐ x ∂volume, k b x = h b x + s b x)
  (hhard : ∀ b, ∀ᵐ x ∂volume, (h b x).val.1 ∈ hardOnePhoton κ)
  (hsoft : ∀ b, ∀ᵐ x ∂volume, (s b x).val.1 ∈ softOnePhoton κ)
  (e σ : ℝ) (hσ0 : 0 ≤ σ) (hσ : ∀ᵐ x ∂volume, ∑ b, ‖(s b x).val.1‖ ^ 2 ≤ σ)
  (u : ℕ → Reference (Fin N × Fin 3) V)
  (hu : ∀ n, ∀ᵐ x ∂volume, inclusion (Fin N × Fin 3) V (u n) x ∈
    generatedFockSubspace (hardOnePhoton κ))

private theorem sum_rearrange (t : Finset ℕ) (m E : ℕ → ℝ) (c : ℝ) :
    ∑ n ∈ t, ((1 + c) * m n + E n) = ∑ n ∈ t, m n + (∑ n ∈ t, E n + c * ∑ n ∈ t, m n) := by
  have h : ∀ n, (1 + c) * m n + E n = m n + (E n + c * m n) := fun n => by ring
  simp_rw [h, Finset.sum_add_distrib, ← Finset.mul_sum]

include hh hs Mh Ms hMh hMs hsplit hhard hsoft hσ hu in
/-- The graph norm of a finite tag superposition. -/
theorem tagSum_norm_sq_le (t : Finset ℕ) :
    ‖tagSum V C BF hF hκ t u‖ ^ 2 ≤
      (formComparisonConstant (Fin N × Fin 3) C k hk Mk hMk e * (1 + Real.sqrt 2)) ^ 2 *
        ∑ n ∈ t, ((1 + (κ + 3 * e ^ 2 * σ / 2)) * ‖inclusion (Fin N × Fin 3) V (u n)‖ ^ 2 +
          energy (Fin N × Fin 3) V C k hk Mk hMk e (u n)) := by
  have h1 := PhysicalPFSource.reference_norm_sq_le (Fin N × Fin 3) V C k hk Mk hMk e
    (tagSum V C BF hF hκ t u)
  have h2 := energy_tagSum_le V C BF hF hκ k h s hk hh hs Mk Mh Ms hMk hMh hMs hsplit hhard
    hsoft t u hu e σ hσ
  have h3 := inclusion_tagSum_norm_sq V C BF hF hκ t u hu
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
  refine le_of_le_of_eq ?_ (sum_rearrange t (fun n => ‖inclusion (Fin N × Fin 3) V (u n)‖ ^ 2)
    (fun n => energy (Fin N × Fin 3) V C k hk Mk hMk e (u n)) (κ + 3 * e ^ 2 * σ / 2)).symm
  beta_reduce
  linarith [h2, h3]

include hh hs Mh Ms hMh hMs hsplit hhard hsoft hσ0 hσ hu in
/-- **The tag series converges in the reference domain.** -/
theorem tagged_summable
    (hm : Summable (fun n => ‖inclusion (Fin N × Fin 3) V (u n)‖ ^ 2))
    (hE : Summable (fun n => energy (Fin N × Fin 3) V C k hk Mk hMk e (u n))) :
    Summable (fun n => tagRef V C BF hF hκ n (u n)) :=
  summable_of_sq_bound (fun n => tagRef V C BF hF hκ n (u n))
    (fun n => (1 + (κ + 3 * e ^ 2 * σ / 2)) * ‖inclusion (Fin N × Fin 3) V (u n)‖ ^ 2 +
      energy (Fin N × Fin 3) V C k hk Mk hMk e (u n))
    ((formComparisonConstant (Fin N × Fin 3) C k hk Mk hMk e * (1 + Real.sqrt 2)) ^ 2)
    (sq_nonneg _) ((hm.mul_left _).add hE)
    (fun n => add_nonneg (mul_nonneg (by positivity) (sq_nonneg _))
      (energy_nonneg (Fin N × Fin 3) V C k hk Mk hMk e (u n)))
    (fun t => tagSum_norm_sq_le V C BF hF hκ k h s hk hh hs Mk Mh Ms hMk hMh hMs hsplit hhard
      hsoft e σ hσ u hu t)

variable {Ψ : Reference (Fin N × Fin 3) V}

theorem tagged_tendsto (hΨ : HasSum (fun n => tagRef V C BF hF hκ n (u n)) Ψ) :
    Tendsto (fun K => tagSum V C BF hF hκ (Finset.range K) u) atTop (𝓝 Ψ) :=
  hΨ.tendsto_sum_nat

include hu in
/-- The norm of the tagged vector. -/
theorem tagged_mass {m : ℝ}
    (hm : HasSum (fun n => ‖inclusion (Fin N × Fin 3) V (u n)‖ ^ 2) m)
    (hΨ : HasSum (fun n => tagRef V C BF hF hκ n (u n)) Ψ) :
    ‖inclusion (Fin N × Fin 3) V Ψ‖ ^ 2 = m := by
  have h1 : Tendsto (fun K => ‖inclusion (Fin N × Fin 3) V
      (tagSum V C BF hF hκ (Finset.range K) u)‖ ^ 2) atTop
      (𝓝 (‖inclusion (Fin N × Fin 3) V Ψ‖ ^ 2)) :=
    (((inclusion (Fin N × Fin 3) V).continuous.norm.pow 2).tendsto Ψ).comp
      (tagged_tendsto V C BF hF hκ u hΨ)
  have h2 : Tendsto (fun K => ‖inclusion (Fin N × Fin 3) V
      (tagSum V C BF hF hκ (Finset.range K) u)‖ ^ 2) atTop (𝓝 m) :=
    hm.tendsto_sum_nat.congr fun K =>
      (inclusion_tagSum_norm_sq V C BF hF hκ (Finset.range K) u hu).symm
  exact tendsto_nhds_unique h1 h2

include hh hs Mh Ms hMh hMs hsplit hhard hsoft hσ0 hσ hu in
/-- **The energy of the tagged vector.** -/
theorem tagged_energy_le {E m : ℝ}
    (hE : HasSum (fun n => energy (Fin N × Fin 3) V C k hk Mk hMk e (u n)) E)
    (hm : HasSum (fun n => ‖inclusion (Fin N × Fin 3) V (u n)‖ ^ 2) m)
    (hΨ : HasSum (fun n => tagRef V C BF hF hκ n (u n)) Ψ) :
    energy (Fin N × Fin 3) V C k hk Mk hMk e Ψ ≤ E + (κ + 3 * e ^ 2 * σ / 2) * m := by
  have hc : 0 ≤ κ + 3 * e ^ 2 * σ / 2 := by positivity
  have hcont : Continuous (energy (Fin N × Fin 3) V C k hk Mk hMk e) :=
    (((continuous_const.mul (continuous_finsetSum _ fun b _ =>
      (covariant (Fin N × Fin 3) V C k hk Mk hMk e b).continuous.norm.pow 2)).add
        ((radiation (Fin N × Fin 3) V).continuous.norm.pow 2)).add
          ((potential (Fin N × Fin 3) V).continuous.norm.pow 2)).congr fun _ => rfl
  refine le_of_tendsto' ((hcont.tendsto Ψ).comp (tagged_tendsto V C BF hF hκ u hΨ)) fun K => ?_
  exact (energy_tagSum_le V C BF hF hκ k h s hk hh hs Mk Mh Ms hMk hMh hMs hsplit hhard hsoft
    (Finset.range K) u hu e σ hσ).trans (add_le_add
      (sum_le_hasSum _ (fun n _ => energy_nonneg (Fin N × Fin 3) V C k hk Mk hMk e (u n)) hE)
      (mul_le_mul_of_nonneg_left (sum_le_hasSum _ (fun n _ => sq_nonneg _) hm) hc))

/-- **The tagged vector is fermionic.** -/
theorem tagged_fermionic
    (hferm : ∀ n, inclusion (Fin N × Fin 3) V (u n) ∈
      PhysicalElectronicFermions.fermionicSubspace N PhotonFock)
    (hΨ : HasSum (fun n => tagRef V C BF hF hκ n (u n)) Ψ) :
    inclusion (Fin N × Fin 3) V Ψ ∈ PhysicalElectronicFermions.fermionicSubspace N PhotonFock := by
  have hmem : ∀ K, inclusion (Fin N × Fin 3) V (tagSum V C BF hF hκ (Finset.range K) u) ∈
      PhysicalElectronicFermions.fermionicSubspace N PhotonFock := fun K => by
    rw [inclusion_tagSum V C BF hF hκ (Finset.range K) u]
    exact Submodule.sum_mem _ fun n _ =>
      (PhysicalElectronicFermions.mem_fermionicSubspace_iff N PhotonFock _).mpr
        (PhysicalElectronicFermions.fiberOperator_character N PhotonFock
          (tagOp κ C BF (hF.soft n)) _
          ((PhysicalElectronicFermions.mem_fermionicSubspace_iff N PhotonFock _).mp (hferm n)))
  exact (PhysicalElectronicFermions.fermionicSubspace_closed N PhotonFock).mem_of_tendsto
    (((inclusion (Fin N × Fin 3) V).continuous.tendsto Ψ).comp
      (tagged_tendsto V C BF hF hκ u hΨ)) (Eventually.of_forall hmem)

theorem vectorPair_density_test (t : PhysicalPairSpace.SpatialTest)
    (w : Reference (Fin N × Fin 3) V) :
    PhysicalPairSpace.spatialDensityTest t (PhysicalPFPairSeries.vectorPair i V C k hk Mk hMk e w) =
      (N : ℝ) * ∫ z, t.weight ((split i) z).1 * ‖inclusion (Fin N × Fin 3) V w z‖ ^ 2 :=
  (PhysicalPairSpace.spatialDensityTest_eq t _).trans
    (PhysicalSourcePair.tested_density_ofWaveFunction i
      (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V w))
      (fun a => covariant (Fin N × Fin 3) V C k hk Mk hMk e (i, a) w)
      t.weight t.measurable (ae_of_all _ t.bounded))

theorem vectorPair_current_test (b : Fin 3) (t : PhysicalPairSpace.SpatialTest)
    (w : Reference (Fin N × Fin 3) V) :
    PhysicalPairSpace.spatialCurrentTest b t
        (PhysicalPFPairSeries.vectorPair i V C k hk Mk hMk e w) =
      (N : ℝ) * ∫ z, t.weight ((split i) z).1 *
        (⟪inclusion (Fin N × Fin 3) V w z,
          covariant (Fin N × Fin 3) V C k hk Mk hMk e (i, b) w z⟫_ℂ).re :=
  (PhysicalPairSpace.spatialCurrentTest_eq b t _).trans
    (PhysicalSourcePair.tested_current_ofWaveFunction i
      (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V w))
      (fun a => covariant (Fin N × Fin 3) V C k hk Mk hMk e (i, a) w) b
      t.weight t.measurable (ae_of_all _ t.bounded))

include hh hs Mh Ms hMh hMs hsplit hhard hsoft hu in
/-- **The pair of a finite tag superposition is the sum of the pairs.** -/
theorem vectorPair_tagSum (t : Finset ℕ) :
    PhysicalPFPairSeries.vectorPair i V C k hk Mk hMk e (tagSum V C BF hF hκ t u) =
      ∑ n ∈ t, PhysicalPFPairSeries.vectorPair i V C k hk Mk hMk e (u n) := by
  apply PhysicalPairSpace.pair_eq_of_spatial_test_maps
  · intro τ
    have hw : AEStronglyMeasurable (fun z => τ.weight ((split i) z).1) volume :=
      τ.measurable.comp_fst.comp_measurePreserving (split_measurePreserving i)
    have hc : ∀ᵐ z ∂volume, |τ.weight ((split i) z).1| ≤ 1 :=
      ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using τ.bounded ((split i) z).1
    have hsum := tested_sum_of_ae _ hw 1 hc
      (inclusion (Fin N × Fin 3) V (tagSum V C BF hF hκ t u))
      (inclusion (Fin N × Fin 3) V (tagSum V C BF hF hκ t u)) t
      (fun n => inclusion (Fin N × Fin 3) V (u n)) (fun n => inclusion (Fin N × Fin 3) V (u n))
      (density_tagSum_ae V C BF hF hκ t u hu)
    have hconv (w : WaveSpace (Fin N × Fin 3)) :
        ∫ z, τ.weight ((split i) z).1 * (⟪w z, w z⟫_ℂ).re =
          ∫ z, τ.weight ((split i) z).1 * ‖w z‖ ^ 2 :=
      integral_congr_ae (ae_of_all _ fun z =>
        congrArg (τ.weight ((split i) z).1 * ·) (re_inner_self (w z)))
    calc PhysicalPairSpace.spatialDensityTest τ
          (PhysicalPFPairSeries.vectorPair i V C k hk Mk hMk e (tagSum V C BF hF hκ t u))
        = (N : ℝ) * ∫ z, τ.weight ((split i) z).1 *
            ‖inclusion (Fin N × Fin 3) V (tagSum V C BF hF hκ t u) z‖ ^ 2 :=
          vectorPair_density_test i V C k hk Mk hMk e τ _
      _ = (N : ℝ) * ∑ n ∈ t, ∫ z, τ.weight ((split i) z).1 *
            ‖inclusion (Fin N × Fin 3) V (u n) z‖ ^ 2 :=
          congrArg ((N : ℝ) * ·) ((hconv _).symm.trans
            (hsum.trans (Finset.sum_congr rfl fun n _ => hconv _)))
      _ = ∑ n ∈ t, (N : ℝ) * ∫ z, τ.weight ((split i) z).1 *
            ‖inclusion (Fin N × Fin 3) V (u n) z‖ ^ 2 := Finset.mul_sum _ _ _
      _ = ∑ n ∈ t, PhysicalPairSpace.spatialDensityTest τ
            (PhysicalPFPairSeries.vectorPair i V C k hk Mk hMk e (u n)) :=
          Finset.sum_congr rfl fun n _ => (vectorPair_density_test i V C k hk Mk hMk e τ _).symm
      _ = _ := (map_sum _ _ _).symm
  · intro b τ
    have hw : AEStronglyMeasurable (fun z => τ.weight ((split i) z).1) volume :=
      τ.measurable.comp_fst.comp_measurePreserving (split_measurePreserving i)
    have hc : ∀ᵐ z ∂volume, |τ.weight ((split i) z).1| ≤ 1 :=
      ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using τ.bounded ((split i) z).1
    have hsum := tested_sum_of_ae _ hw 1 hc
      (inclusion (Fin N × Fin 3) V (tagSum V C BF hF hκ t u))
      (covariant (Fin N × Fin 3) V C k hk Mk hMk e (i, b) (tagSum V C BF hF hκ t u)) t
      (fun n => inclusion (Fin N × Fin 3) V (u n))
      (fun n => covariant (Fin N × Fin 3) V C k hk Mk hMk e (i, b) (u n))
      (current_tagSum_ae V C BF hF hκ k h s hk hh hs Mk Mh Ms hMk hMh hMs hsplit hhard hsoft
        t u hu e (i, b))
    calc PhysicalPairSpace.spatialCurrentTest b τ
          (PhysicalPFPairSeries.vectorPair i V C k hk Mk hMk e (tagSum V C BF hF hκ t u))
        = (N : ℝ) * ∫ z, τ.weight ((split i) z).1 *
            (⟪inclusion (Fin N × Fin 3) V (tagSum V C BF hF hκ t u) z,
              covariant (Fin N × Fin 3) V C k hk Mk hMk e (i, b)
                (tagSum V C BF hF hκ t u) z⟫_ℂ).re :=
          vectorPair_current_test i V C k hk Mk hMk e b τ _
      _ = (N : ℝ) * ∑ n ∈ t, ∫ z, τ.weight ((split i) z).1 *
            (⟪inclusion (Fin N × Fin 3) V (u n) z,
              covariant (Fin N × Fin 3) V C k hk Mk hMk e (i, b) (u n) z⟫_ℂ).re :=
          congrArg ((N : ℝ) * ·) hsum
      _ = ∑ n ∈ t, (N : ℝ) * ∫ z, τ.weight ((split i) z).1 *
            (⟪inclusion (Fin N × Fin 3) V (u n) z,
              covariant (Fin N × Fin 3) V C k hk Mk hMk e (i, b) (u n) z⟫_ℂ).re :=
          Finset.mul_sum _ _ _
      _ = ∑ n ∈ t, PhysicalPairSpace.spatialCurrentTest b τ
            (PhysicalPFPairSeries.vectorPair i V C k hk Mk hMk e (u n)) :=
          Finset.sum_congr rfl fun n _ =>
            (vectorPair_current_test i V C k hk Mk hMk e b τ _).symm
      _ = _ := (map_sum _ _ _).symm

theorem vectorPair_continuous :
    Continuous (fun w => PhysicalPFPairSeries.vectorPair i V C k hk Mk hMk e w) :=
  (@diag_continuous (Reference (PhysicalPFPairSeries.Index N) V) PhysicalPairSpace.Pair _
    (PhysicalPFPairSeries.referenceRealSpace V) _ _
    (PhysicalPFPairSeries.pairForm i V C k hk Mk hMk e)).congr fun w =>
      PhysicalPFPairSeries.pairForm_diagonal i V C k hk Mk hMk e w

include hh hs Mh Ms hMh hMs hsplit hhard hsoft hu in
/-- **The tagged vector has the pair of the source.** -/
theorem tagged_pair {d : PhysicalPairSpace.Pair}
    (hd : HasSum (fun n => PhysicalPFPairSeries.vectorPair i V C k hk Mk hMk e (u n)) d)
    (hΨ : HasSum (fun n => tagRef V C BF hF hκ n (u n)) Ψ) :
    PhysicalPFPairSeries.vectorPair i V C k hk Mk hMk e Ψ = d := by
  have hcont := vectorPair_continuous i V C k hk Mk hMk e
  have h1 := (hcont.tendsto Ψ).comp (tagged_tendsto V C BF hF hκ u hΨ)
  have h2 : Tendsto (fun K => PhysicalPFPairSeries.vectorPair i V C k hk Mk hMk e
      (tagSum V C BF hF hκ (Finset.range K) u)) atTop (𝓝 d) :=
    hd.tendsto_sum_nat.congr fun K =>
      (vectorPair_tagSum i V C BF hF hκ k h s hk hh hs Mk Mh Ms hMk hMh hMs hsplit hhard hsoft
        e u hu (Finset.range K)).symm
  exact tendsto_nhds_unique h1 h2

end Generic

section Physical

variable {N : ℕ} (i : Fin N) (F : Frame) (χ : ArticleCutoff)
  (C : CanonicalSectorCCR photonMeasure) (B : StandardNormalTraceBackground)
  (S : StandardClosedFormBackground) (e : ℝ)

/-- Each electron coordinate has soft kernel norm at most `b_κ`. -/
theorem soft_norm_sq_le {κ : ℝ} (hκ : 0 ≤ κ) (j : Fin N × Fin 3)
    (x : PhysicalPFReference.Position (Fin N × Fin 3)) :
    ‖(PhysicalRemovalKernels.soft F χ N κ j x).val.1‖ ^ 2 ≤
      CutoffProfile.bsq photonMeasure NormalPhoton.frequency χ.profile κ := by
  rw [PhysicalRemovalKernels.soft_eq_label F χ N κ hκ j x,
    derivativeKernel_fst_norm_sq F χ hκ j.2 [] (particle x j.1)]
  calc (∫ p, ‖softDerivativeKernel Prod.fst [] κ (particle x j.1) (base F χ j.2) p‖ ^ 2
        ∂photonMeasure)
      = ∫ p, ‖softBase Prod.fst κ (base F χ j.2) p‖ ^ 2 ∂photonMeasure :=
        integral_congr_ae (ae_of_all _ fun p => congrArg (· ^ 2)
          (norm_softDerivativeKernel_nil Prod.fst κ (particle x j.1) (base F χ j.2) p))
    _ ≤ _ := softBase_integral_le_bsq F χ j.2 κ

/-- The energy cost of the tagging step. -/
def tagCost (N : ℕ) (χ : ArticleCutoff) (e κ : ℝ) : ℝ :=
  κ + 3 * e ^ 2 * ((Fintype.card (Fin N × Fin 3) : ℝ) *
    CutoffProfile.bsq photonMeasure NormalPhoton.frequency χ.profile κ) / 2

include i F C B S in
theorem tagCost_tendsto : Tendsto (tagCost N χ e) (𝓝[>] 0) (𝓝 0) := by
  have hP := PhysicalRemoval.moments i F χ 1 C B S e
  have hb := CutoffProfile.tendsto_bsq hP.dispersion_measurable hP.dispersion_positive
    hP.cutoff_finite
  have hid : Tendsto (fun κ : ℝ => κ) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have h := hid.add (((hb.const_mul (Fintype.card (Fin N × Fin 3) : ℝ)).const_mul
    (3 * e ^ 2)).div_const 2)
  have h0 : (0 : ℝ) + 3 * e ^ 2 * ((Fintype.card (Fin N × Fin 3) : ℝ) * 0) / 2 = 0 := by ring
  rw [h0] at h
  exact h

theorem soft_sum_le {κ : ℝ} (hκ : 0 ≤ κ) (x : PhysicalPFReference.Position (Fin N × Fin 3)) :
    ∑ b, ‖(PhysicalRemovalKernels.soft F χ N κ b x).val.1‖ ^ 2 ≤
      (Fintype.card (Fin N × Fin 3) : ℝ) *
        CutoffProfile.bsq photonMeasure NormalPhoton.frequency χ.profile κ :=
  (Finset.sum_le_sum fun b _ => soft_norm_sq_le F χ hκ b x).trans_eq
    (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul])

theorem bsq_card_nonneg (κ : ℝ) :
    0 ≤ (Fintype.card (Fin N × Fin 3) : ℝ) *
      CutoffProfile.bsq photonMeasure NormalPhoton.frequency χ.profile κ :=
  mul_nonneg (Nat.cast_nonneg _) (CutoffProfile.bsq_nonneg κ)

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
theorem tagged_vector_mass :
    ‖inclusion (Fin N × Fin 3) (PhysicalRemoval.potential N 1) Ψ‖ ^ 2 = 1 :=
  (tagged_mass (PhysicalRemoval.potential N 1) C BF (PhysicalSoftTagModes.tagFamily hκ)
    hκ.le src.vector hu src.mass_hasSum hΨ).trans r.val.property.2.1

include hΨ in
theorem tagged_vector_fermionic :
    inclusion (Fin N × Fin 3) (PhysicalRemoval.potential N 1) Ψ ∈
      PhysicalElectronicFermions.fermionicSubspace N PhotonFock :=
  tagged_fermionic (PhysicalRemoval.potential N 1) C BF (PhysicalSoftTagModes.tagFamily hκ)
    hκ.le src.vector src.fermionic hΨ

include hu hΨ in
theorem tagged_vector_energy :
    energy (Fin N × Fin 3) (PhysicalRemoval.potential N 1) C (full F χ N)
        (full_measurable F χ N) (bound F χ) (full_bound F χ N) e Ψ ≤
      (PhysicalRemoval.model i F χ 1 C B S e).energy r + tagCost N χ e κ := by
  have henergy := tagged_energy_le (PhysicalRemoval.potential N 1) C BF
    (PhysicalSoftTagModes.tagFamily hκ) hκ.le (full F χ N)
    (PhysicalRemovalKernels.hard F χ N κ) (PhysicalRemovalKernels.soft F χ N κ)
    (full_measurable F χ N) (hard_measurable F χ N κ) (soft_measurable F χ N κ)
    (bound F χ) (bound F χ) (bound F χ) (full_bound F χ N) (hard_bound F χ N κ)
    (soft_bound F χ N κ) (fun b => ae_of_all _ (full_eq_hard_add_soft F χ N κ b))
    (fun b => ae_of_all _ (hard_mem F χ N κ b)) (fun b => ae_of_all _ (soft_mem F χ N κ b))
    e _ (bsq_card_nonneg χ κ) (ae_of_all _ (soft_sum_le F χ hκ.le)) src.vector hu
    (src.energy_hasSum C (full F χ N) (full_measurable F χ N) (bound F χ)
      (full_bound F χ N) S e r.val.property.2.2) src.mass_hasSum hΨ
  have htrace : (B.realization (WaveSpace (Fin N × Fin 3))).rank.trace r.val.val = 1 :=
    r.val.property.2.1
  refine henergy.trans_eq ?_
  simp only [htrace, mul_one]
  rfl

include hu hΨ in
theorem tagged_vector_pair :
    PhysicalPFPairSeries.vectorPair i (PhysicalRemoval.potential N 1) C (full F χ N)
        (full_measurable F χ N) (bound F χ) (full_bound F χ N) e Ψ =
      (PhysicalRemoval.model i F χ 1 C B S e).density r :=
  tagged_pair i (PhysicalRemoval.potential N 1) C BF (PhysicalSoftTagModes.tagFamily hκ)
    hκ.le (full F χ N) (PhysicalRemovalKernels.hard F χ N κ)
    (PhysicalRemovalKernels.soft F χ N κ)
    (full_measurable F χ N) (hard_measurable F χ N κ) (soft_measurable F χ N κ)
    (bound F χ) (bound F χ) (bound F χ) (full_bound F χ N) (hard_bound F χ N κ)
    (soft_bound F χ N κ) (fun b => ae_of_all _ (full_eq_hard_add_soft F χ N κ b))
    (fun b => ae_of_all _ (hard_mem F χ N κ b)) (fun b => ae_of_all _ (soft_mem F χ N κ b))
    e src.vector hu
    (PhysicalPFSpectral.mixed_pair_hasSum i (PhysicalRemoval.potential N 1) C (full F χ N)
      (full_measurable F χ N) (bound F χ) (full_bound F χ N) B S e r src.toSource) hΨ

end TaggedVector

/-- The pure state of a normalized fermionic reference vector. -/
def referencePure (Ψ : Reference (Fin N × Fin 3) (PhysicalRemoval.potential N 1))
    (hnorm : ‖inclusion (Fin N × Fin 3) (PhysicalRemoval.potential N 1) Ψ‖ ^ 2 = 1)
    (hferm : inclusion (Fin N × Fin 3) (PhysicalRemoval.potential N 1) Ψ ∈
      PhysicalElectronicFermions.fermionicSubspace N PhotonFock) :
    PureState F χ C B S e (N := N) :=
  ⟨inclusion (Fin N × Fin 3) (PhysicalRemoval.potential N 1) Ψ,
    (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).mp (hnorm.trans (one_pow 2).symm),
    (PhysicalElectronicFermions.projection_eq_self_iff N PhotonFock _).mpr
      ((PhysicalElectronicFermions.mem_fermionicSubspace_iff N PhotonFock _).mp hferm),
    (normalEnergy_rankOne (Fin N × Fin 3) (PhysicalRemoval.potential N 1) C
      (full F χ N) (full_measurable F χ N) (bound F χ) (full_bound F χ N) B S e Ψ).trans_lt
        ENNReal.ofReal_lt_top⟩

theorem referencePure_energy (Ψ : Reference (Fin N × Fin 3) (PhysicalRemoval.potential N 1))
    (hnorm : ‖inclusion (Fin N × Fin 3) (PhysicalRemoval.potential N 1) Ψ‖ ^ 2 = 1)
    (hferm : inclusion (Fin N × Fin 3) (PhysicalRemoval.potential N 1) Ψ ∈
      PhysicalElectronicFermions.fermionicSubspace N PhotonFock) :
    (PhysicalAttainment.pureModel i F χ C B S e).energy (referencePure F χ C B S e Ψ hnorm hferm) =
      energy (Fin N × Fin 3) (PhysicalRemoval.potential N 1) C (full F χ N)
        (full_measurable F χ N) (bound F χ) (full_bound F χ N) e Ψ :=
  (congrArg ENNReal.toReal (normalEnergy_rankOne (Fin N × Fin 3) (PhysicalRemoval.potential N 1)
    C (full F χ N) (full_measurable F χ N) (bound F χ) (full_bound F χ N) B S e Ψ)).trans
    (ENNReal.toReal_ofReal (energy_nonneg (Fin N × Fin 3) (PhysicalRemoval.potential N 1) C
      (full F χ N) (full_measurable F χ N) (bound F χ) (full_bound F χ N) e Ψ))

theorem referencePure_density (Ψ : Reference (Fin N × Fin 3) (PhysicalRemoval.potential N 1))
    (hnorm : ‖inclusion (Fin N × Fin 3) (PhysicalRemoval.potential N 1) Ψ‖ ^ 2 = 1)
    (hferm : inclusion (Fin N × Fin 3) (PhysicalRemoval.potential N 1) Ψ ∈
      PhysicalElectronicFermions.fermionicSubspace N PhotonFock) :
    (PhysicalAttainment.pureModel i F χ C B S e).density
        (referencePure F χ C B S e Ψ hnorm hferm) =
      PhysicalPFPairSeries.vectorPair i (PhysicalRemoval.potential N 1) C (full F χ N)
        (full_measurable F χ N) (bound F χ) (full_bound F χ N) e Ψ :=
  PhysicalPFSpectral.pure_pair_eq i (PhysicalRemoval.potential N 1) C (full F χ N)
    (full_measurable F χ N) (bound F χ) (full_bound F χ N) B S e
    (referencePure F χ C B S e Ψ hnorm hferm) Ψ rfl

/-- A fermionic spectral source without soft photons is hard. -/
theorem source_hard (BF : StandardSymmetricFockExponential) {κ : ℝ}
    (r : MixedState F χ C B S e (N := N))
    (hsoft0 : PhysicalRemoval.softEnergy F χ 1 C B S e r κ = 0)
    (src : PhysicalPFSource.SupportedSource N (PhysicalRemoval.potential N 1) B r.val.val)
    (n : ℕ) :
    ∀ᵐ x ∂volume, inclusion (Fin N × Fin 3) (PhysicalRemoval.potential N 1) (src.vector n) x ∈
      generatedFockSubspace (hardOnePhoton κ) :=
  (PhysicalSoftTagModes.source_hardSupported B volume κ src.hasSum hsoft0 n).mono
    fun _ hx => mem_generated_of_hardSupported BF κ _ hx

variable (BF : StandardSymmetricFockExponential)

include BF in
/-- **The tagging step of `thm-many-electron-soft-purification`.** -/
theorem tagging_input : TaggingInput i F χ C B S e (tagCost N χ e) := by
  intro κ hκ _ r hsoft0
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
  exact ⟨referencePure F χ C B S e _ hnorm hferm,
    (referencePure_density i F χ C B S e _ hnorm hferm).trans
      (tagged_vector_pair i F χ C B S e hκ BF r src hu hsum.hasSum),
    (referencePure_energy i F χ C B S e _ hnorm hferm).trans_le
      (tagged_vector_energy i F χ C B S e hκ BF r src hu hsum.hasSum)⟩

variable (BW : StandardWienerSegal)
  (core : CountableSpatialTestCore) (smooth : SmoothSobolevBackground)
  (C₀ : ℝ) (scaled : ScaledGradientSobolevBackground (6 + 12 * (N : ℝ)) C₀)
  (B₀ : TensorBackground Repair.SixTag) (B₁ : TensorMultilinearData B₀)
  {ι : Type*} (basis : HilbertBasis ι ℂ (recursiveLiftCandidate B₀ N).target)
  (index : ι ↪ ℕ) (Sob : StandardHomogeneousSobolev)
  (Rellich : PhysicalRellichFourier.StandardSupportedHalfRellich)
  (Hardy : StandardFractionalHardy)
  (hLp : StandardFiniteDimensionalLpRepresentation) (hFM : StandardDualFenchelMoreau)

include BF BW core smooth scaled B₀ B₁ basis index in
/-- **`many-electron-pure-approximation`**: for every finite-energy density
matrix and every `ε > 0` there is a pure state with exactly the same density
and current and energy below `E + ε`. -/
theorem exact_recovery (he : 0 ≤ e) (hC₀ : 0 ≤ C₀) :
    DFT.ExactRecovery (PhysicalAttainment.pureModel i F χ C B S e)
      (PhysicalRemoval.model i F χ 1 C B S e) :=
  exactRecovery_of_tagging i F χ C B S e BF BW core smooth C₀ scaled B₀ B₁ basis index he hC₀
    (tagCost_tendsto i F χ C B S e) (tagging_input i F χ C B S e BF)

include BF BW core smooth scaled B₀ B₁ basis index Sob Rellich Hardy hLp hFM in
/-- **`thm-many-electron-soft-purification`.** `F_LL = F̃_L = F_L` at every
pair, the pure and mixed representability classes coincide, and at every pair
the pure infimum is attained exactly when the mixed problem has a rank-one
minimizer. -/
theorem many_electron_soft_purification (he : 0 ≤ e) (hC₀ : 0 ≤ C₀) :
    (∀ d, pureFunctional i F χ C B S e d = mixedFunctional i F χ C B S e d) ∧
    (∀ d, pureFunctional i F χ C B S e d = liebFunctional i F χ C B S e d) ∧
    Set.range (PhysicalAttainment.pureModel i F χ C B S e).density =
      Set.range (PhysicalRemoval.model i F χ 1 C B S e).density ∧
    (∀ d, DFT.Attained (PhysicalAttainment.pureModel i F χ C B S e) d ↔
      ∃ m, m ∈ Set.range (PhysicalPFStates.pureEmbedding i (PhysicalRemoval.potential N 1) C
          (full F χ N) (full_measurable F χ N) (bound F χ) (full_bound F χ N) B S e).toMixed ∧
        (PhysicalRemoval.model i F χ 1 C B S e).density m = d ∧
        ((PhysicalRemoval.model i F χ 1 C B S e).energy m : EReal) =
          DFT.search (PhysicalRemoval.model i F χ 1 C B S e) d) :=
  soft_purification i F χ C B S e BF BW core smooth C₀ scaled B₀ B₁ basis index Sob Rellich
    Hardy hLp hFM he hC₀ (tagCost_tendsto i F χ C B S e) (tagging_input i F χ C B S e BF)

include BF BW core smooth scaled B₀ B₁ basis index Sob Rellich Hardy hLp hFM in
/-- **`zero-current-pure-density-search`**: at zero current the pure
functional is the pure density-only search and equals the Lieb functional. -/
theorem pure_zero_current (he : 0 ≤ e) (hC₀ : 0 ≤ C₀) (ρ : PhysicalPairSpace.Density) :
    pureFunctional i F χ C B S e (ρ, 0) =
        PhysicalZeroCurrent.densityPureFunctional i F χ C B S e ρ ∧
      pureFunctional i F χ C B S e (ρ, 0) = liebFunctional i F χ C B S e (ρ, 0) :=
  pure_zero_current_of_tagging i F χ C B S e BF BW core smooth C₀ scaled B₀ B₁ basis index Sob
    Rellich Hardy hLp hFM he hC₀ (tagCost_tendsto i F χ C B S e)
    (tagging_input i F χ C B S e BF) ρ

end Physical

end GptLean.PhysicalSoftPurification
