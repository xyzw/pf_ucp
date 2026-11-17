import GptLean.PhysicalPFLocalizationKinetic
import GptLean.PhysicalPFElectronicCutoff

/-!
The selected electronic multiplier supplies the geometric support needed
by the actual photon dilation. Thus the common kinetic source is built
for every finite-energy input, with no source support premise.
-/

noncomputable section
namespace GptLean.PhysicalPFLocalization

open MeasureTheory Gaussian PhysicalFock PhysicalPFReference PhysicalNormalTrace PhysicalClosedForms
  PhotonLocalization PhotonLocalizationChannel PhotonLocalizationPhysicalKernels SymmetricLift
open PhysicalNormalTrace.StandardNormalTraceBackground
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000
set_option Elab.async false

private theorem real_smul_zero_of_zero {H : Type*} [AddCommMonoid H] [Module ℂ H]
    {a : ℝ} (ha : a = 0) (v : H) : (a : ℂ) • v = 0 := by
  rw [ha, Complex.ofReal_zero, zero_smul]

private theorem finite_domain_lift {H Q : Type*} (inc : Q → H) (E : H → ℝ≥0∞)
    (finite_iff : ∀ v, E v < ⊤ ↔ ∃ q, inc q = v)
    (P : H → Prop) (hP : ∀ q, P (inc q)) {v : H} (hv : E v < ⊤) : P v := by
  obtain ⟨q, hq⟩ := (finite_iff v).mp hv
  exact (congrArg P hq).mp (hP q)

local instance radiationNormedSpace : NormedSpace ℂ RadiationGraphSpace :=
  radiationRoot.graph.normedSpace

variable (N : ℕ)

private def selectedReference (l : ℕ)
    (u : Reference (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N)) :
    Reference (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N) :=
  PhysicalPFScalarMultiplier.multiply (PhysicalCovariantKinetic.potential N)
    (PhysicalElectronicScalars.branch N l (PhysicalElectronicScalars.selected N)) u

theorem selectedReference_support (l : ℕ)
    (u : Reference (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N))
    (j : Fin N × Fin 3) :
    ∀ᵐ x ∂volume,
      radiationSource (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N)
        (selectedReference N l u) x ≠ 0 → ‖particle x j.1‖ ≤ (2 * (l + 1) : ℕ) := by
  let a := PhysicalElectronicScalars.branch N l (PhysicalElectronicScalars.selected N)
  have h := PhysicalBoundedScalar.multiplier_ae volume a.weight
    a.differentiable.continuous.aestronglyMeasurable a.bound (ae_of_all _ a.bounded)
    (radiationSource (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N) u)
  filter_upwards [h] with x hx
  intro hu
  have hr : x ∈ electronicConfigurationRegion ((l : ℝ) + 1) := by
    by_contra hnot
    apply hu
    change (PhysicalBoundedScalar.multiplier volume a.weight
      a.differentiable.continuous.aestronglyMeasurable a.bound (ae_of_all _ a.bounded)
      (radiationSource (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N) u)) x = 0
    have hz : a.weight x = 0 := PhysicalElectronicScalars.selected_support N l x hnot
    exact hx.trans (real_smul_zero_of_zero hz _)
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using hr j.1

variable {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  (F : FormFactors photonMeasure (Fin 3)) (hF : F.momentum = Prod.fst)
  (J : Lp ℂ 2 photonMeasure ≃ₗᵢ[ℝ] Z) (Bsob : SobolevMultiplierBackground Z)
  (hmult : ∀ (χ : FieldSpace → ℝ) (_hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (_hc : HasCompactSupport χ)
    (hχm : AEStronglyMeasurable χ (volume : Measure FieldSpace))
    (hb : ∀ᵐ y ∂(volume : Measure FieldSpace), |χ y| ≤ 1) a w,
    physicalRadiationCoordinates.representative J a w →
    physicalRadiationCoordinates.representative J
      (PhotonKernelLocalization.l2Multiplier χ hχm hb a) (Bsob.multiplier χ w))
  (BF : StandardSymmetricFockExponential) (C : CanonicalSectorCCR photonMeasure)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground) (e : ℝ)

include hmult in
private theorem selectedKineticSource_reference (l m : ℕ)
    (u : Reference (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N)) :
    Nonempty (KineticDilationSource (A := (B.realization (FullHilbert N)).rank) (ι := Fin N × Fin 3)
      (PhysicalCovariantKinetic.normalEnergy N C (PhysicalProfiles.particleKernel F hF J N)
        (PhysicalProfiles.particleKernel_measurable F hF J N) (PhysicalProfiles.kernelBound F hF J)
        (PhysicalProfiles.particleKernel_bound F hF J N) e B S)
      (physicalControl F hF J C B S N e) (physicalKraus BF N m)
      ((PhysicalElectronicScalars.branch N l (PhysicalElectronicScalars.selected N)).multiplier
        (inclusion (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N) u))
      e (PhysicalProfiles.cutoffError F J Bsob (2 * (l + 1)) m) 3 (derivativeConstant N)) := by
  let q := PhysicalCoulombReferenceCore.forget N 1 (selectedReference N l u)
  have hs (j : Fin N × Fin 3) : ∀ᵐ x ∂volume,
      PhysicalFreeReferenceCore.radiationSource (Fin N × Fin 3) q x ≠ 0 →
        ‖particle x j.1‖ ≤ (2 * (l + 1) : ℕ) := selectedReference_support N l u j
  have hvq : PhysicalFreeForm.inclusion (Fin N × Fin 3) q =
      (PhysicalElectronicScalars.branch N l (PhysicalElectronicScalars.selected N)).multiplier
        (inclusion (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N) u) :=
    PhysicalPFScalarMultiplier.value_multiply (PhysicalCovariantKinetic.potential N)
      (PhysicalElectronicScalars.branch N l (PhysicalElectronicScalars.selected N)) u
  let sourceAt := fun w : FullHilbert N =>
    KineticDilationSource (A := (B.realization (FullHilbert N)).rank) (ι := Fin N × Fin 3)
      (PhysicalCovariantKinetic.normalEnergy N C (PhysicalProfiles.particleKernel F hF J N)
        (PhysicalProfiles.particleKernel_measurable F hF J N) (PhysicalProfiles.kernelBound F hF J)
        (PhysicalProfiles.particleKernel_bound F hF J N) e B S)
      (physicalControl F hF J C B S N e) (physicalKraus BF N m) w
      e (PhysicalProfiles.cutoffError F J Bsob (2 * (l + 1)) m) 3 (derivativeConstant N)
  have hsource : Nonempty (sourceAt (PhysicalFreeForm.inclusion (Fin N × Fin 3) q)) :=
    ⟨kineticSource F hF J Bsob hmult BF C B S N e (2 * (l + 1)) m q hs⟩
  exact (congrArg (fun w : FullHilbert N => Nonempty (sourceAt w)) hvq).mp hsource

include hmult in
/-- Every finite physical input gives the selected, supported kinetic source. -/
theorem selectedKineticSource (l m : ℕ) (v : FullHilbert N)
    (hv : (normalEnergy (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N)
      C (PhysicalProfiles.particleKernel F hF J N) (PhysicalProfiles.particleKernel_measurable F hF J N)
      (PhysicalProfiles.kernelBound F hF J) (PhysicalProfiles.particleKernel_bound F hF J N) B S e).expectation
        ((B.realization (FullHilbert N)).rank.rankOne v) < ⊤) :
    Nonempty (KineticDilationSource (A := (B.realization (FullHilbert N)).rank) (ι := Fin N × Fin 3)
      (PhysicalCovariantKinetic.normalEnergy N C (PhysicalProfiles.particleKernel F hF J N)
        (PhysicalProfiles.particleKernel_measurable F hF J N) (PhysicalProfiles.kernelBound F hF J)
        (PhysicalProfiles.particleKernel_bound F hF J N) e B S)
      (physicalControl F hF J C B S N e) (physicalKraus BF N m)
      ((PhysicalElectronicScalars.branch N l (PhysicalElectronicScalars.selected N)).multiplier v)
      e (PhysicalProfiles.cutoffError F J Bsob (2 * (l + 1)) m) 3 (derivativeConstant N)) := by
  let P := fun w : FullHilbert N => Nonempty
    (KineticDilationSource (A := (B.realization (FullHilbert N)).rank) (ι := Fin N × Fin 3)
      (PhysicalCovariantKinetic.normalEnergy N C (PhysicalProfiles.particleKernel F hF J N)
        (PhysicalProfiles.particleKernel_measurable F hF J N) (PhysicalProfiles.kernelBound F hF J)
        (PhysicalProfiles.particleKernel_bound F hF J N) e B S)
      (physicalControl F hF J C B S N e) (physicalKraus BF N m)
      ((PhysicalElectronicScalars.branch N l (PhysicalElectronicScalars.selected N)).multiplier w)
      e (PhysicalProfiles.cutoffError F J Bsob (2 * (l + 1)) m) 3 (derivativeConstant N))
  exact finite_domain_lift
    (H := FullHilbert N)
    (Q := Reference (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N))
    (inclusion (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N))
    (fun w => (normalEnergy (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N)
      C (PhysicalProfiles.particleKernel F hF J N) (PhysicalProfiles.particleKernel_measurable F hF J N)
      (PhysicalProfiles.kernelBound F hF J) (PhysicalProfiles.particleKernel_bound F hF J N) B S e).expectation
        ((B.realization (FullHilbert N)).rank.rankOne w))
    (PhysicalPFRadiation.normalEnergy_rankOne_finite_iff
      (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N)
      C (PhysicalProfiles.particleKernel F hF J N) (PhysicalProfiles.particleKernel_measurable F hF J N)
      (PhysicalProfiles.kernelBound F hF J) (PhysicalProfiles.particleKernel_bound F hF J N) B S e)
    P (fun u => selectedKineticSource_reference N F hF J Bsob hmult BF C B S e l m u) hv

end GptLean.PhysicalPFLocalization
