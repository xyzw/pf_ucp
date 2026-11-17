import GptLean.PhysicalPFLocalizationTests
import GptLean.PhysicalBoundedScalar
import GptLean.PhysicalFockPhysicalProfiles
import GptLean.PhysicalFockSpatialFieldParts

/-!
Compact scalar tests restrict the actual tail field to a bounded spatial
region. The resulting estimate uses the proved profile errors and the
physical radiation and mass control, without a tested-current assumption.
-/

noncomputable section
namespace GptLean.PhysicalPFLocalization

open MeasureTheory PhysicalFock PhysicalPFReference PhysicalPFSource PhysicalPFStates
  PhysicalPairSpace PhysicalNormalTrace PhysicalClosedForms PhysicalSourceCoordinates
  PhysicalSourcePair SymmetricLift PhotonLocalizationPhysicalKernels
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000
set_option Elab.async false

private theorem scalar_map_eq {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : E →L[ℂ] F) (c : ℂ) {u v : E} {y z w : F}
    (h₁ : y = L v) (h₂ : v = c • u) (h₃ : z = c • w) (h₄ : w = L u) :
    y = z := by
  exact h₁.trans ((congrArg L h₂).trans
    ((L.map_smul c u).trans ((congrArg (fun t : F => c • t) h₄.symm).trans h₃.symm)))

private theorem real_smul_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {c : ℝ} {u v : E} (h : v = (c : ℂ) • u) (hc : c = 0) : v = 0 := by
  rw [h, hc, Complex.ofReal_zero, zero_smul]

private theorem norm_le_of_operator_eq {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {A B : E →L[ℂ] F} (h : A = B) (u : E) {r : ℝ} (hu : ‖A u‖ ≤ r) :
    ‖B u‖ ≤ r :=
  (congrArg (fun L : E →L[ℂ] F => ‖L u‖) h).symm.le.trans hu

private theorem tested_control_algebra {a b r ε : ℝ} (ha : a ≤ r) (hb : b ≤ r)
    (hε : 0 ≤ ε) : ε * (2 * a + b) ≤ ε * 3 * r := by
  calc
    ε * (2 * a + b) ≤ ε * (2 * r + r) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left ha (by norm_num)) hb) hε
    _ = ε * 3 * r := by ring

section Scalar
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
  (C : CanonicalSectorCCR photonMeasure)
  (κ : X → WeightedPhotonKernel) (hκ : AEStronglyMeasurable κ μ)
  (M : ℝ) (hb : ∀ᵐ x ∂μ, ‖κ x‖ ≤ M)
  (f : X → ℝ) (hf : AEStronglyMeasurable f μ)
  (hfbound : ∀ᵐ x ∂μ, |f x| ≤ 1)

private theorem scalar_field_commute (u : SpatialRadiationGraph μ) :
    spatialField μ C κ hκ M hb (PhysicalBoundedScalar.multiplier μ f hf 1 hfbound u) =
      PhysicalBoundedScalar.multiplier μ f hf 1 hfbound (spatialField μ C κ hκ M hb u) := by
  apply Lp.ext
  filter_upwards [spatialField_ae μ C κ hκ M hb
      (PhysicalBoundedScalar.multiplier μ f hf 1 hfbound u),
    PhysicalBoundedScalar.multiplier_ae μ f hf 1 hfbound u,
    PhysicalBoundedScalar.multiplier_ae μ f hf 1 hfbound (spatialField μ C κ hκ M hb u),
    spatialField_ae μ C κ hκ M hb u] with x h₁ h₂ h₃ h₄
  exact scalar_map_eq (kernelField C (κ x)) (f x : ℂ) h₁ h₂ h₃ h₄

/-- Only the kernel on the support of the test enters this estimate. -/
theorem tested_field_bound (ε : ℝ) (hε : 0 ≤ ε)
    (hn : ∀ᵐ x ∂μ, f x ≠ 0 → ‖(κ x).val.2‖ ≤ ε)
    (hl : ∀ᵐ x ∂μ, f x ≠ 0 → ‖(κ x).val.1‖ ≤ ε)
    (u : SpatialRadiationGraph μ) :
    ‖PhysicalBoundedScalar.multiplier μ f hf 1 hfbound (spatialField μ C κ hκ M hb u)‖ ≤
      ε * (2 * ‖spatialRadiationDerivative μ u‖ + ‖spatialRadiationInclusion μ u‖) := by
  let v := PhysicalBoundedScalar.multiplier μ f hf 1 hfbound u
  have hs : ∀ᵐ x ∂μ, v x ≠ 0 → f x ≠ 0 := by
    filter_upwards [PhysicalBoundedScalar.multiplier_ae μ f hf 1 hfbound u] with x hx
    intro hv hz
    apply hv
    exact real_smul_zero hx hz
  have h := spatialField_supported_norm_le μ C κ hκ M hb ε hε v
    (by filter_upwards [hs, hn] with x hs hn using fun hv => hn (hs hv))
    (by filter_upwards [hs, hl] with x hs hl using fun hv => hl (hs hv))
  have hd : ‖spatialRadiationDerivative μ v‖ ≤ ‖spatialRadiationDerivative μ u‖ := by
    have he := PhysicalBoundedScalar.multiplier_compLpL μ f hf 1 hfbound
      radiationGraphDerivative u
    exact (congrArg norm he).le.trans
      ((PhysicalBoundedScalar.multiplier_norm_le μ f hf 1 hfbound
        (spatialRadiationDerivative μ u)).trans_eq (one_mul _))
  have hi : ‖spatialRadiationInclusion μ v‖ ≤ ‖spatialRadiationInclusion μ u‖ := by
    have he := PhysicalBoundedScalar.multiplier_compLpL μ f hf 1 hfbound
      radiationGraphInclusion u
    exact (congrArg norm he).le.trans
      ((PhysicalBoundedScalar.multiplier_norm_le μ f hf 1 hfbound
        (spatialRadiationInclusion μ u)).trans_eq (one_mul _))
  have hnorm := (congrArg norm (scalar_field_commute μ C κ hκ M hb f hf hfbound u)).symm.le.trans h
  exact hnorm.trans (mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hd (by norm_num)) hi) hε)

end Scalar

private theorem exists_test_radius (t : SmoothSpatialTest) :
    ∃ R : ℕ, ∀ x, t.weight x ≠ 0 → ‖x‖ ≤ R := by
  obtain ⟨r, hr⟩ := t.compact.isCompact.isBounded.subset_closedBall 0
  obtain ⟨R, hR⟩ := exists_nat_ge r
  refine ⟨R, fun x hx => ?_⟩
  have h := hr (subset_tsupport t.weight hx)
  exact (by simpa only [Metric.mem_closedBall, dist_zero_right] using h : ‖x‖ ≤ r).trans hR

def testRadius (t : SmoothSpatialTest) : ℕ := (exists_test_radius t).choose

theorem testRadius_bound (t : SmoothSpatialTest) (x : PhysicalPairSpace.Position)
    (hx : t.weight x ≠ 0) : ‖x‖ ≤ testRadius t :=
  (exists_test_radius t).choose_spec x hx

variable {N : ℕ} (i : Fin N) (t : SmoothSpatialTest)

private def testedWeight (x : SymmetricLift.Configuration N) : ℝ := t.weight ((split i) x).1

private theorem testedWeight_measurable : AEStronglyMeasurable (testedWeight i t) volume :=
  (t.smooth.continuous.comp (continuous_fst.comp (split i).continuous)).aestronglyMeasurable

private theorem testedWeight_bound : ∀ᵐ x ∂volume, |testedWeight i t x| ≤ 1 :=
  ae_of_all _ fun x => by simpa only [testedWeight, Real.norm_eq_abs] using t.bounded ((split i) x).1

private theorem tested_multiplier_eq :
    PhysicalBoundedScalar.multiplier (H := PhotonFock) volume (testedWeight i t)
      (testedWeight_measurable i t) 1 (testedWeight_bound i t) =
        spatialMultiplier i t.toBoundedSpatialTest :=
  PhysicalBoundedScalar.multiplier_eq_realL2 (F := PhotonFock) volume (testedWeight i t)
    (testedWeight_measurable i t) 1 (testedWeight_bound i t)

variable {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  (F : FormFactors photonMeasure (Fin 3)) (hF : F.momentum = Prod.fst)
  (J : Lp ℂ 2 photonMeasure ≃ₗᵢ[ℝ] Z) (Bsob : SobolevMultiplierBackground Z)
  (hmult : ∀ (χ : Gaussian.FieldSpace → ℝ) (_hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (_hc : HasCompactSupport χ)
    (hχm : AEStronglyMeasurable χ (volume : Measure Gaussian.FieldSpace))
    (hb : ∀ᵐ y ∂(volume : Measure Gaussian.FieldSpace), |χ y| ≤ 1) a w,
    physicalRadiationCoordinates.representative J a w →
    physicalRadiationCoordinates.representative J
      (PhotonKernelLocalization.l2Multiplier χ hχm hb a) (Bsob.multiplier χ w))

def tailKernel (m : ℕ) (b : Fin 3) (x : SymmetricLift.Configuration N) : WeightedPhotonKernel :=
  profileMomentumKernel physicalRadiationCoordinates J rfl
    (PhysicalProfiles.tailProfile F hF J Bsob hmult m) (b, particle x i)

theorem tailKernel_measurable (m : ℕ) (b : Fin 3) :
    AEStronglyMeasurable (tailKernel i F hF J Bsob hmult m b) volume :=
  ((profileMomentumKernel_continuous physicalRadiationCoordinates J rfl
    (PhysicalProfiles.tailProfile F hF J Bsob hmult m)).comp
      (continuous_const.prodMk (particleLinear i).continuous_of_finiteDimensional)).aestronglyMeasurable

def tailKernelBound (m : ℕ) : ℝ :=
  profileKernelBound physicalRadiationCoordinates J (PhysicalProfiles.tailProfile F hF J Bsob hmult m)

theorem tailKernel_bound (m : ℕ) (b : Fin 3) :
    ∀ᵐ x ∂volume, ‖tailKernel i F hF J Bsob hmult m b x‖ ≤ tailKernelBound F hF J Bsob hmult m :=
  ae_of_all _ fun x => profileMomentumKernel_bound physicalRadiationCoordinates J rfl
    (PhysicalProfiles.tailProfile F hF J Bsob hmult m) (b, particle x i)

/-- The actual Fourier tail tested in one particle coordinate. -/
theorem spatialMultiplier_tailField_bound (C : CanonicalSectorCCR photonMeasure)
    (m : ℕ) (b : Fin 3) (u : SpatialRadiationGraph (volume : Measure (SymmetricLift.Configuration N))) :
    ‖spatialMultiplier i t.toBoundedSpatialTest
      (spatialField volume C (tailKernel i F hF J Bsob hmult m b)
        (tailKernel_measurable i F hF J Bsob hmult m b) (tailKernelBound F hF J Bsob hmult m)
        (tailKernel_bound i F hF J Bsob hmult m b) u)‖ ≤
      PhysicalProfiles.cutoffError F J Bsob (testRadius t) m *
        (2 * ‖spatialRadiationDerivative volume u‖ + ‖spatialRadiationInclusion volume u‖) := by
  have hr (x : SymmetricLift.Configuration N) (hx : testedWeight i t x ≠ 0) : ‖particle x i‖ ≤ testRadius t := by
    rw [← split_fst_eq_particle i x]
    exact testRadius_bound t _ hx
  have h := tested_field_bound volume C (tailKernel i F hF J Bsob hmult m b)
    (tailKernel_measurable i F hF J Bsob hmult m b) (tailKernelBound F hF J Bsob hmult m)
    (tailKernel_bound i F hF J Bsob hmult m b) (testedWeight i t)
    (testedWeight_measurable i t) (testedWeight_bound i t)
    (PhysicalProfiles.cutoffError F J Bsob (testRadius t) m)
    (PhysicalProfiles.cutoffError_nonneg F J Bsob (testRadius t) m)
    (ae_of_all _ fun x hx =>
      (profileMomentumKernel_negative_norm physicalRadiationCoordinates J rfl
        (PhysicalProfiles.tailProfile F hF J Bsob hmult m) (b, particle x i)).le.trans
          (PhysicalProfiles.cutoff_components F hF J Bsob hmult (testRadius t) m
            (b, particle x i) (hr x hx)).2.1)
    (ae_of_all _ fun x hx =>
      (profileMomentumKernel_l2_norm physicalRadiationCoordinates J rfl
        (PhysicalProfiles.tailProfile F hF J Bsob hmult m) (b, particle x i)).le.trans
          (PhysicalProfiles.cutoff_components F hF J Bsob hmult (testRadius t) m
            (b, particle x i) (hr x hx)).1) u
  exact norm_le_of_operator_eq (tested_multiplier_eq i t) _ h

variable (V : PhysicalPFReference.Position (Fin N × Fin 3) → ℝ)
  (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → PhysicalPFReference.Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hκ : ∀ q, AEStronglyMeasurable (κ q) volume)
  (M : ℝ) (hbound : ∀ q, ∀ᵐ x ∂volume, ‖κ q x‖ ≤ M)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground) (e : ℝ)

/-- The physical tested tail estimate in the exact current-control norm. -/
theorem tested_tail_control (m : ℕ) (b : Fin 3)
    (u : Reference (Fin N × Fin 3) V) :
    ‖spatialMultiplier i t.toBoundedSpatialTest
      (spatialField volume C (tailKernel i F hF J Bsob hmult m b)
        (tailKernel_measurable i F hF J Bsob hmult m b) (tailKernelBound F hF J Bsob hmult m)
        (tailKernel_bound i F hF J Bsob hmult m b) (radiationSource (Fin N × Fin 3) V u))‖ ≤
      PhysicalProfiles.cutoffError F J Bsob (testRadius t) m * 3 *
        Real.sqrt ((currentControl (Fin N × Fin 3) V C κ hκ M hbound B S e).expectation
          ((B.realization (WaveSpace (Fin N × Fin 3))).rank.rankOne
            (inclusion (Fin N × Fin 3) V u))).toReal := by
  have h := spatialMultiplier_tailField_bound i t F hF J Bsob hmult C m b
    (radiationSource (Fin N × Fin 3) V u)
  have hr := radiation_norm_le_sqrt_control (Fin N × Fin 3) V C κ hκ M hbound B S e u
  have hm := norm_le_sqrt_control (Fin N × Fin 3) V C κ hκ M hbound B S e
    (inclusion (Fin N × Fin 3) V u)
    (control_rankOne_finite (Fin N × Fin 3) V C κ hκ M hbound B S e u)
  have hr' : ‖spatialRadiationDerivative volume
      (radiationSource (Fin N × Fin 3) V u)‖ ≤
      Real.sqrt ((currentControl (Fin N × Fin 3) V C κ hκ M hbound B S e).expectation
        ((B.realization (WaveSpace (Fin N × Fin 3))).rank.rankOne
          (inclusion (Fin N × Fin 3) V u))).toReal := hr
  have hm' := (congrArg norm (radiation_matches (Fin N × Fin 3) V u)).le.trans hm
  exact h.trans (tested_control_algebra hr' hm'
    (PhysicalProfiles.cutoffError_nonneg F J Bsob (testRadius t) m))

end GptLean.PhysicalPFLocalization
