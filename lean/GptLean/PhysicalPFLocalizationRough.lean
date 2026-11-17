import GptLean.PhysicalFockChannelReference
import GptLean.PhysicalPFComparison
import GptLean.PhysicalPFLocalizationTests

/-!
Uniform physical energy transport uses the actual free channel bound and
the proved two-way Pauli–Fierz/free comparisons. This provides finite
energy for the complete mixed output without any compactness input.
-/

noncomputable section

namespace GptLean.PhysicalPFLocalization

open MeasureTheory Filter Topology Gaussian PhysicalFock PhysicalPFReference
  PhysicalNormalTrace PhysicalClosedForms PhotonLocalization PhotonLocalizationChannel
  PhotonLocalizationFormBounds PhotonLocalizationPhysicalKernels PhysicalPFSource
open PhysicalNormalTrace.StandardNormalTraceBackground
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000
set_option Elab.async false

private theorem finite_domain_bound {H D : Type*} (f g : H → ℝ≥0∞)
    (ι : D → H) (c : ℝ≥0∞) (hc : c ≠ 0)
    (hfinite : ∀ v, g v < ⊤ → ∃ q, ι q = v)
    (hbound : ∀ q, f (ι q) ≤ c * g (ι q)) (v : H) :
    f v ≤ c * g v := by
  by_cases hv : g v < ⊤
  · obtain ⟨q, hq⟩ := hfinite v hv
    exact hq ▸ hbound q
  · have ht : g v = ⊤ := top_unique (not_lt.mp hv)
    simp only [ht, ENNReal.mul_top hc, le_top]

private theorem triple_energy_bound {a b c d : ℝ≥0∞} {A B C : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hab : a ≤ ENNReal.ofReal A * b)
    (hbc : b ≤ ENNReal.ofReal B * c)
    (hcd : c ≤ ENNReal.ofReal C * d) :
    a ≤ ENNReal.ofReal (A * B * C) * d := by
  apply (hab.trans (mul_le_mul_right
    (hbc.trans (mul_le_mul_right hcd _)) _)).trans_eq
  rw [ENNReal.ofReal_mul (mul_nonneg hA hB), ENNReal.ofReal_mul hA]
  simp only [mul_assoc]

private theorem normalized_energy_estimate {a b : ℝ≥0∞} {c E t : ℝ}
    (hc : 0 ≤ c) (h : a ≤ ENNReal.ofReal c * (b + ENNReal.ofReal t))
    (ht : t = 1) (hb : b ≤ ENNReal.ofReal E) :
    a ≤ ENNReal.ofReal (c * (max E 0 + 1)) := by
  apply h.trans
  rw [ht, ENNReal.ofReal_mul hc,
    ENNReal.ofReal_add (le_max_right E 0) zero_le_one]
  exact mul_le_mul_right (add_le_add
    (hb.trans (ENNReal.ofReal_le_ofReal (le_max_left E 0))) le_rfl) _

variable {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  (Bsob : SobolevMultiplierBackground Q) (J : Lp ℂ 2 photonMeasure ≃ₗᵢ[ℝ] Q)
  (hmult : ∀ (χ : FieldSpace → ℝ) (_hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (_hc : HasCompactSupport χ)
    (hχm : AEStronglyMeasurable χ (volume : Measure FieldSpace))
    (hb : ∀ᵐ y ∂(volume : Measure FieldSpace), |χ y| ≤ 1) a w,
    physicalRadiationCoordinates.representative J a w →
    physicalRadiationCoordinates.representative J
      (PhotonKernelLocalization.l2Multiplier χ hχm hb a) (Bsob.multiplier χ w))
  (BF : StandardSymmetricFockExponential) (C : CanonicalSectorCCR photonMeasure)
  (B : StandardNormalTraceBackground) (N : ℕ) (S : StandardClosedFormBackground)

include hmult C in
theorem free_channel_bound (m : ℕ) {x : B.Trace (FullHilbert N)}
    (hx : x ∈ (B.realization (FullHilbert N)).rank.positive) :
    (PhysicalFreeForm.normalEnergy (Fin N × Fin 3) B S).expectation
      (B.normal.extend (physicalKraus BF N m) x) ≤
      ENNReal.ofReal (radiationMultiplierConstant Bsob) *
        (PhysicalFreeForm.normalEnergy (Fin N × Fin 3) B S).expectation x := by
  apply channel_form_le B.normal
    (PhysicalFreeForm.normalEnergy (Fin N × Fin 3) B S)
    (PhysicalFreeForm.normalEnergy (Fin N × Fin 3) B S)
    (fun _ hx => hx) (physicalKraus BF N m) _ hx
  refine finite_domain_bound
    (fun v : FullHilbert N => ∑' a,
      (PhysicalFreeForm.normalEnergy (Fin N × Fin 3) B S).expectation
        ((B.realization (FullHilbert N)).rank.rankOne (physicalKraus BF N m v a)))
    (fun v : FullHilbert N =>
      (PhysicalFreeForm.normalEnergy (Fin N × Fin 3) B S).expectation
        ((B.realization (FullHilbert N)).rank.rankOne v))
    (PhysicalFreeForm.inclusion (Fin N × Fin 3))
    (ENNReal.ofReal (radiationMultiplierConstant Bsob))
    (ENNReal.ofReal_ne_zero_iff.mpr (radiationMultiplierConstant_pos Bsob)) ?_ ?_
  · intro v hv
    exact (PhysicalFreeForm.normalEnergy_finite_iff (Fin N × Fin 3) B S v).mp hv
  · intro q
    exact physicalKraus_free_tsum_bound Bsob J hmult BF C B N m S q

variable
  (κ : (Fin N × Fin 3) → Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)

def roughConstant : ℝ :=
  PhysicalPFComparison.reverseConstant N 1 zero_le_one C κ hκ M hbound e *
    radiationMultiplierConstant Bsob *
      PhysicalPFComparison.forwardConstant N 1 C κ hκ M hbound e

theorem roughConstant_pos : 0 < roughConstant Bsob C N κ hκ M hbound e :=
  mul_pos (mul_pos (PhysicalPFComparison.reverseConstant_pos N 1 zero_le_one C κ hκ M hbound e)
    (radiationMultiplierConstant_pos Bsob))
      (PhysicalPFComparison.forwardConstant_pos N 1 C κ hκ M hbound e)

include hmult in
theorem pf_channel_bound (m : ℕ) {x : B.Trace (FullHilbert N)}
    (hx : x ∈ (B.realization (FullHilbert N)).rank.positive) :
    (PhysicalPFDecomposition.energy N B S C κ hκ M hbound e).expectation
      (B.normal.extend (physicalKraus BF N m) x) ≤
      ENNReal.ofReal (roughConstant Bsob C N κ hκ M hbound e) *
        ((PhysicalPFDecomposition.energy N B S C κ hκ M hbound e).expectation x +
          ENNReal.ofReal ((B.realization (FullHilbert N)).rank.trace x)) := by
  have hp := PhysicalPFComparison.normal_pf_le_free N 1 zero_le_one C κ hκ M hbound B S e
    (B.normal.positive (physicalKraus BF N m) hx)
  have ho := free_channel_bound Bsob J hmult BF C B N S m hx
  have hi := PhysicalPFComparison.normal_free_le_pf_add_mass N 1 C κ hκ M hbound B S e hx
  exact triple_energy_bound
    (PhysicalPFComparison.reverseConstant_pos N 1 zero_le_one C κ hκ M hbound e).le
    (radiationMultiplierConstant_pos Bsob).le hp ho hi

include hmult in
theorem pf_channel_finite (m : ℕ) {x : B.Trace (FullHilbert N)}
    (hx : x ∈ (B.realization (FullHilbert N)).rank.positive)
    (he : (PhysicalPFDecomposition.energy N B S C κ hκ M hbound e).expectation x < ⊤) :
    (PhysicalPFDecomposition.energy N B S C κ hκ M hbound e).expectation
      (B.normal.extend (physicalKraus BF N m) x) < ⊤ :=
  (pf_channel_bound Bsob J hmult BF C B N S κ hκ M hbound e m hx).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.mpr ⟨he, ENNReal.ofReal_lt_top⟩))

include hmult in
theorem control_channel_finite (m : ℕ) {x : B.Trace (FullHilbert N)}
    (hx : x ∈ (B.realization (FullHilbert N)).rank.positive)
    (he : (currentControl (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N)
      C κ hκ M hbound B S e).expectation x < ⊤) :
    (currentControl (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N)
      C κ hκ M hbound B S e).expectation
        (B.normal.extend (physicalKraus BF N m) x) < ⊤ := by
  apply (currentControl_finite_iff (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N)
    C κ hκ M hbound B S e (B.normal.positive (physicalKraus BF N m) hx)).mpr
  apply pf_channel_finite Bsob J hmult BF C B N S κ hκ M hbound e m hx
  exact (currentControl_finite_iff (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N)
    C κ hκ M hbound B S e hx).mp he

include hmult in
theorem normalized_energy_bound (m : ℕ) {x : B.Trace (FullHilbert N)}
    (hx : x ∈ (B.realization (FullHilbert N)).rank.positive)
    (hmass : (B.realization (FullHilbert N)).rank.trace x = 1)
    (E : ℝ) (hE : (PhysicalPFDecomposition.energy N B S C κ hκ M hbound e).expectation x ≤
      ENNReal.ofReal E) :
    (PhysicalPFDecomposition.energy N B S C κ hκ M hbound e).expectation
      (B.normal.extend (physicalKraus BF N m) x) ≤
        ENNReal.ofReal (roughConstant Bsob C N κ hκ M hbound e * (max E 0 + 1)) := by
  exact normalized_energy_estimate
    (roughConstant_pos Bsob C N κ hκ M hbound e).le
    (pf_channel_bound Bsob J hmult BF C B N S κ hκ M hbound e m hx) hmass hE

include hmult in
/-- The complete density source uses the actual channel and the derived
output energy bound. No output-domain assumption remains. -/
theorem density_source_exists (i : Fin N) (t : PhysicalPairSpace.SmoothSpatialTest)
    (m : ℕ) (v : FullHilbert N)
    (hv : (currentControl (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N)
      C κ hκ M hbound B S e).expectation ((B.realization (FullHilbert N)).rank.rankOne v) < ⊤) :
    Nonempty (TestedCurrentSource (A := (B.realization (FullHilbert N)).rank)
      (control := currentControl (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N)
        C κ hκ M hbound B S e)
      (current := PhysicalPFStates.testObservable i (PhysicalCovariantKinetic.potential N)
        C κ hκ M hbound B S e (.inl t))
      (physicalKraus BF N m) v (testOperator i (.inl t)) (fun _ => 0) e 0 0) := by
  have ho := control_channel_finite Bsob J hmult BF C B N S κ hκ M hbound e m
    ((B.realization (FullHilbert N)).rank.rankOne_positive v) hv
  have heq := congrArg
    (currentControl (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N)
      C κ hκ M hbound B S e).expectation
    (B.normal.extend_rankOne (physicalKraus BF N m) v)
  have hpure := heq.symm.le.trans_lt ho
  exact ⟨densitySource i (PhysicalCovariantKinetic.potential N) C κ hκ M hbound B S e
    t (physicalKraus BF N m) v hv hpure⟩

end GptLean.PhysicalPFLocalization
