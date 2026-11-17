import GptLean.PhysicalSoftTagCount

/-!
`cor-many-electron-pure-functional` on the actual fermionic Pauli--Fierz model
of the attainment theorem.

By `thm-many-electron-soft-purification`, `F_LL = F̃_L = F_L`. Hence:

* `F_LL` is proper, convex and norm lower semicontinuous on the pair space. The
  internal energy is nonnegative, the fermionic vacuum seed has finite energy,
  density matrices can be mixed, and the mixed search is lower semicontinuous
  by the attainment theorem;
* `unrestricted-pure-mixed-PF-class`: the pure and mixed representability
  classes coincide and equal the domain of `F_L`, so the pure class is convex;
* for every mixed minimizer `Γ_*` at a pair, there are normalized pure states
  `Ψ_j` with exactly that pair and `⟨Ψ_j, H^{0,0} Ψ_j⟩ → F_LL`, whose photon
  numbers satisfy `⟨Ψ_j, N Ψ_j⟩ ≤ 1 + Tr(N Γ_*) ≤ 1 + C (1 + F_L)`
  (`pure-minimizing-sequence-number-bound`). The constant `C` is chosen before
  the pair.

The states `Ψ_j` are soft-photon purifications of `Γ_*` with energy error
`1/(j+1)`. Soft removal keeps only the hard photons of `Γ_*`, and tagging adds
one photon per spectral vector, so `⟨Ψ_j, N Ψ_j⟩ ≤ 1 + Tr(N Γ_*)`
(`PhysicalSoftPurification.pure_approximation_count`). The second inequality
is the optimizer bound of `thm-unrestricted-attainment`.
-/

noncomputable section

namespace GptLean.PhysicalPureFunctional

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

/-- `F_LL` never takes the value `-∞`, since the internal energy is nonnegative. -/
theorem pureFunctional_ne_bot (d : Pair) : pureFunctional i F χ C B S e d ≠ ⊥ :=
  DFT.search_ne_bot (PhysicalAttainment.pureModel i F χ C B S e) 0
    (fun _ => ENNReal.toReal_nonneg) d

/-- The normalized fermionic vacuum seed, as a density matrix. -/
abbrev seed : MixedState F χ C B S e (N := N) :=
  PhysicalPFSeed.mixed N 1 zero_le_one C (full F χ N) (full_measurable F χ N) (bound F χ)
    (full_bound F χ N) B S e

theorem mixedFunctional_seed_lt_top :
    mixedFunctional i F χ C B S e
        ((PhysicalRemoval.model i F χ 1 C B S e).density (seed F χ C B S e)) < ⊤ :=
  (DFT.search_le (PhysicalRemoval.model i F χ 1 C B S e) (s := seed F χ C B S e) rfl).trans_lt
    (EReal.coe_lt_top _)

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
/-- `F_LL = F̃_L`, from the exact-pair recovery. -/
theorem pure_eq_mixed (he : 0 ≤ e) (hC₀ : 0 ≤ C₀) (d : Pair) :
    pureFunctional i F χ C B S e d = mixedFunctional i F χ C B S e d :=
  DFT.pure_eq_mixed _ _ (PhysicalPFStates.pureEmbedding i (PhysicalRemoval.potential N 1) C
    (full F χ N) (full_measurable F χ N) (bound F χ) (full_bound F χ N) B S e)
    (PhysicalSoftPurification.exact_recovery i F χ C B S e BF BW core smooth C₀ scaled B₀ B₁
      basis index he hC₀) d

include BF BW core smooth scaled B₀ B₁ basis index in
/-- **`F_LL` is proper**: it is nowhere `-∞` and finite at the vacuum seed. -/
theorem pureFunctional_proper (he : 0 ≤ e) (hC₀ : 0 ≤ C₀) :
    (∀ d, pureFunctional i F χ C B S e d ≠ ⊥) ∧ ∃ d, pureFunctional i F χ C B S e d ≠ ⊤ :=
  ⟨pureFunctional_ne_bot i F χ C B S e,
    ⟨(PhysicalRemoval.model i F χ 1 C B S e).density (seed F χ C B S e),
      ((pure_eq_mixed i F χ C B S e BF BW core smooth C₀ scaled B₀ B₁ basis index he hC₀
        _).trans_lt (mixedFunctional_seed_lt_top i F χ C B S e)).ne⟩⟩

include BF BW core smooth scaled B₀ B₁ basis index in
/-- **`F_LL` is convex**, since `F_LL = F̃_L` and density matrices can be mixed. -/
theorem pureFunctional_convex (he : 0 ≤ e) (hC₀ : 0 ≤ C₀) :
    DFT.ConvexEpigraph (pureFunctional i F χ C B S e) := by
  have h : pureFunctional i F χ C B S e = mixedFunctional i F χ C B S e :=
    funext (pure_eq_mixed i F χ C B S e BF BW core smooth C₀ scaled B₀ B₁ basis index he hC₀)
  rw [h]
  exact PhysicalZeroCurrent.mixedFunctional_convex i F χ C B S e

include BF BW core smooth scaled B₀ B₁ basis index Sob Rellich Hardy hLp hFM in
/-- **`F_LL` is norm lower semicontinuous**, since `F_LL = F̃_L`. -/
theorem pureFunctional_lowerSemicontinuous (he : 0 ≤ e) (hC₀ : 0 ≤ C₀) :
    LowerSemicontinuous (pureFunctional i F χ C B S e) := by
  obtain ⟨_, _, _, _, hlsc, _⟩ := unrestricted_attainment i F χ C B S e BF BW core smooth C₀
    scaled B₀ B₁ basis index Sob Rellich Hardy hLp hFM he hC₀
  have h : pureFunctional i F χ C B S e = mixedFunctional i F χ C B S e :=
    funext (pure_eq_mixed i F χ C B S e BF BW core smooth C₀ scaled B₀ B₁ basis index he hC₀)
  rw [h]
  exact hlsc

include BF BW core smooth scaled B₀ B₁ basis index Sob Rellich Hardy hLp hFM in
/-- **`unrestricted-pure-mixed-PF-class`.** The pure and mixed representability
classes coincide and equal the domain of `F_L`. In particular the pure class
is convex. -/
theorem pure_mixed_class (he : 0 ≤ e) (hC₀ : 0 ≤ C₀) :
    Set.range (PhysicalAttainment.pureModel i F χ C B S e).density =
        Set.range (PhysicalRemoval.model i F χ 1 C B S e).density ∧
      Set.range (PhysicalRemoval.model i F χ 1 C B S e).density =
        {d | liebFunctional i F χ C B S e d < ⊤} ∧
      Convex ℝ (Set.range (PhysicalAttainment.pureModel i F χ C B S e).density) := by
  obtain ⟨_, _, _, _, _, heq⟩ := unrestricted_attainment i F χ C B S e BF BW core smooth C₀
    scaled B₀ B₁ basis index Sob Rellich Hardy hLp hFM he hC₀
  have recovery := PhysicalSoftPurification.exact_recovery i F χ C B S e BF BW core smooth C₀
    scaled B₀ B₁ basis index he hC₀
  let emb := PhysicalPFStates.pureEmbedding i (PhysicalRemoval.potential N 1) C
    (full F χ N) (full_measurable F χ N) (bound F χ) (full_bound F χ N) B S e
  exact ⟨DFT.pure_mixed_representability _ _ emb recovery,
    Set.ext fun d => (mixedFunctional_lt_top_iff i F χ C B S e d).symm.trans
      (iff_of_eq (congrArg (· < ⊤) (heq d))),
    DFT.pure_range_convex _ _ emb recovery
      (PhysicalPFStates.mixedModel_mixtureClosed i (PhysicalRemoval.potential N 1) C
        (full F χ N) (full_measurable F χ N) (bound F χ) (full_bound F χ N) B S e)⟩

include BF BW core smooth scaled B₀ B₁ basis index Sob Rellich Hardy hLp hFM in
/-- **Pure minimizing sequences with bounded photon number.** One constant
`C`, chosen before the pair, has the following property. Let `Γ_*` be a
minimizer of the mixed search at `d`. Then there are normalized fermionic
pure states `Ψ_j` with pair `d`, `⟨Ψ_j, H^{0,0} Ψ_j⟩ → F_LL(d)`,
`⟨Ψ_j, N Ψ_j⟩ ≤ 1 + Tr(N Γ_*)` and `Tr(N Γ_*) ≤ C (1 + F_L(d))`. -/
theorem pure_minimizing_sequence (he : 0 ≤ e) (hC₀ : 0 ≤ C₀) :
    ∃ Cnumber : ℝ, 0 ≤ Cnumber ∧
      ∀ (d : Pair) (m : MixedState F χ C B S e (N := N)),
        (PhysicalRemoval.model i F χ 1 C B S e).density m = d →
        ((PhysicalRemoval.model i F χ 1 C B S e).energy m : EReal) =
          mixedFunctional i F χ C B S e d →
        ∃ p : ℕ → PureState F χ C B S e (N := N),
          (∀ j, (PhysicalAttainment.pureModel i F χ C B S e).density (p j) = d) ∧
          Tendsto (fun j => ((PhysicalAttainment.pureModel i F χ C B S e).energy (p j) : EReal))
            atTop (𝓝 (pureFunctional i F χ C B S e d)) ∧
          (∀ j, PhysicalRemoval.number F χ 1 C B S e
              ((PhysicalPFStates.pureEmbedding i (PhysicalRemoval.potential N 1) C
                (full F χ N) (full_measurable F χ N) (bound F χ) (full_bound F χ N) B S e).toMixed
                  (p j)) ≤
            1 + PhysicalRemoval.number F χ 1 C B S e m) ∧
          PhysicalRemoval.number F χ 1 C B S e m ≤
            ENNReal.ofReal (Cnumber * (1 + (liebFunctional i F χ C B S e d).toReal)) := by
  obtain ⟨Cnumber, hC, _, hnumber, _, heq⟩ := unrestricted_attainment i F χ C B S e BF BW core
    smooth C₀ scaled B₀ B₁ basis index Sob Rellich Hardy hLp hFM he hC₀
  refine ⟨Cnumber, hC, fun d m hm hmin => ?_⟩
  have happrox := fun j : ℕ => PhysicalSoftPurification.pure_approximation_count i F χ C B S e
    BF BW core smooth C₀ scaled B₀ B₁ basis index he hC₀ m (Nat.one_div_pos_of_nat (n := j))
  choose p hpd hpe hpn _ using happrox
  have hpure : pureFunctional i F χ C B S e d =
      (((PhysicalRemoval.model i F χ 1 C B S e).energy m : ℝ) : EReal) :=
    (pure_eq_mixed i F χ C B S e BF BW core smooth C₀ scaled B₀ B₁ basis index he hC₀ d).trans
      hmin.symm
  have hlow : ∀ j, (PhysicalRemoval.model i F χ 1 C B S e).energy m ≤
      (PhysicalAttainment.pureModel i F χ C B S e).energy (p j) := fun j =>
    EReal.coe_le_coe_iff.mp (hpure.symm.trans_le
      (DFT.search_le (PhysicalAttainment.pureModel i F χ C B S e) ((hpd j).trans hm)))
  have hup : Tendsto (fun j : ℕ => (PhysicalRemoval.model i F χ 1 C B S e).energy m +
      1 / ((j : ℝ) + 1)) atTop (𝓝 ((PhysicalRemoval.model i F χ 1 C B S e).energy m)) := by
    simpa only [add_zero] using
      (tendsto_const_nhds (x := (PhysicalRemoval.model i F χ 1 C B S e).energy m)).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hreal : Tendsto (fun j => (PhysicalAttainment.pureModel i F χ C B S e).energy (p j))
      atTop (𝓝 ((PhysicalRemoval.model i F χ 1 C B S e).energy m)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup hlow hpe
  have hopt : (mixedInternalEnergy F χ C B S e m : EReal) =
      mixedFunctional i F χ C B S e ((PhysicalRemoval.model i F χ 1 C B S e).density m) :=
    (mixedModel_energy_coe i F χ C B S e m).symm.trans
      (hmin.trans (congrArg (mixedFunctional i F χ C B S e) hm.symm))
  refine ⟨p, fun j => (hpd j).trans hm, ?_, fun j => (hpn j).trans_eq (add_comm _ _),
    (hnumber m hopt).trans_eq (congrArg (fun z : EReal => ENNReal.ofReal (Cnumber * (1 + z.toReal)))
      ((congrArg (mixedFunctional i F χ C B S e) hm).trans (heq d)))⟩
  rw [hpure]
  exact (continuous_coe_real_ereal.tendsto _).comp hreal

include BF BW core smooth scaled B₀ B₁ basis index Sob Rellich Hardy hLp hFM in
/-- **`cor-many-electron-pure-functional`.**
1. `F_LL` is proper, convex and norm lower semicontinuous on the pair space.
2. The pure and mixed representability classes coincide and equal the domain
   of `F_L` (`unrestricted-pure-mixed-PF-class`); the pure class is convex.
3. At every pair with a mixed minimizer `Γ_*`, there are pure states with that
   exact pair, energies converging to `F_LL`, and photon numbers at most
   `1 + Tr(N Γ_*) ≤ 1 + C (1 + F_L)` (`pure-minimizing-sequence-number-bound`). -/
theorem many_electron_pure_functional (he : 0 ≤ e) (hC₀ : 0 ≤ C₀) :
    ((∀ d, pureFunctional i F χ C B S e d ≠ ⊥) ∧ (∃ d, pureFunctional i F χ C B S e d ≠ ⊤) ∧
      DFT.ConvexEpigraph (pureFunctional i F χ C B S e) ∧
      LowerSemicontinuous (pureFunctional i F χ C B S e)) ∧
    (Set.range (PhysicalAttainment.pureModel i F χ C B S e).density =
        Set.range (PhysicalRemoval.model i F χ 1 C B S e).density ∧
      Set.range (PhysicalRemoval.model i F χ 1 C B S e).density =
        {d | liebFunctional i F χ C B S e d < ⊤} ∧
      Convex ℝ (Set.range (PhysicalAttainment.pureModel i F χ C B S e).density)) ∧
    ∃ Cnumber : ℝ, 0 ≤ Cnumber ∧
      ∀ (d : Pair) (m : MixedState F χ C B S e (N := N)),
        (PhysicalRemoval.model i F χ 1 C B S e).density m = d →
        ((PhysicalRemoval.model i F χ 1 C B S e).energy m : EReal) =
          mixedFunctional i F χ C B S e d →
        ∃ p : ℕ → PureState F χ C B S e (N := N),
          (∀ j, (PhysicalAttainment.pureModel i F χ C B S e).density (p j) = d) ∧
          Tendsto (fun j => ((PhysicalAttainment.pureModel i F χ C B S e).energy (p j) : EReal))
            atTop (𝓝 (pureFunctional i F χ C B S e d)) ∧
          (∀ j, PhysicalRemoval.number F χ 1 C B S e
              ((PhysicalPFStates.pureEmbedding i (PhysicalRemoval.potential N 1) C
                (full F χ N) (full_measurable F χ N) (bound F χ) (full_bound F χ N) B S e).toMixed
                  (p j)) ≤
            1 + PhysicalRemoval.number F χ 1 C B S e m) ∧
          PhysicalRemoval.number F χ 1 C B S e m ≤
            ENNReal.ofReal (Cnumber * (1 + (liebFunctional i F χ C B S e d).toReal)) :=
  ⟨⟨(pureFunctional_proper i F χ C B S e BF BW core smooth C₀ scaled B₀ B₁ basis index he
      hC₀).1,
    (pureFunctional_proper i F χ C B S e BF BW core smooth C₀ scaled B₀ B₁ basis index he
      hC₀).2,
    pureFunctional_convex i F χ C B S e BF BW core smooth C₀ scaled B₀ B₁ basis index he hC₀,
    pureFunctional_lowerSemicontinuous i F χ C B S e BF BW core smooth C₀ scaled B₀ B₁ basis
      index Sob Rellich Hardy hLp hFM he hC₀⟩,
    pure_mixed_class i F χ C B S e BF BW core smooth C₀ scaled B₀ B₁ basis index Sob Rellich
      Hardy hLp hFM he hC₀,
    pure_minimizing_sequence i F χ C B S e BF BW core smooth C₀ scaled B₀ B₁ basis index Sob
      Rellich Hardy hLp hFM he hC₀⟩

end GptLean.PhysicalPureFunctional
