import GptLean.PhysicalPFLocalizationTestedField
import GptLean.PhysicalPFLocalizationRough
import GptLean.PhysicalPFLocalizationKinetic

/-!
The current source uses the actual output reference vectors, the proved
covariant Kraus identity, and vacuum orthogonality. Compact test errors
come from the actual Fourier tail estimate.
-/

noncomputable section
namespace GptLean.PhysicalPFLocalization

open MeasureTheory Filter Topology PhysicalFock PhysicalPFReference PhysicalPFSource PhysicalPFStates PhysicalNormalTrace
  PhysicalClosedForms PhysicalPairSpace PhotonLocalization PhotonLocalizationChannel
  PhotonLocalizationPhysicalKernels SymmetricLift
open PhysicalNormalTrace.StandardNormalTraceBackground
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000
set_option Elab.async false

private theorem finite_domain_lift {H Q : Type*} (inc : Q → H) (E : H → ℝ≥0∞)
    (finite_iff : ∀ v, E v < ⊤ ↔ ∃ q, inc q = v)
    (P : H → Prop) (hP : ∀ q, P (inc q)) {v : H} (hv : E v < ⊤) : P v := by
  obtain ⟨q, hq⟩ := (finite_iff v).mp hv
  exact (congrArg P hq).mp (hP q)

private theorem sparse_field_bound {H ι : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [DecidableEq ι]
    (j : ι) (c ε B r : ℝ) (L : H →L[ℂ] H) (f : ι → H)
    (hc : 0 ≤ c) (h : ‖L (f j)‖ ≤ ε * B * r) :
    ∀ q, ‖(if q = j then c • L else 0) (f q)‖ ≤
      (if q = j then c else 0) * ε * B * r := by
  intro q
  by_cases hq : q = j
  · simp only [hq, ite_true, smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    exact (mul_le_mul_of_nonneg_left h hc).trans_eq (by ring)
  · simp only [hq, ite_false, zero_apply, norm_zero, zero_mul, le_refl]

private theorem inner_smul_zero {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (c : ℂ) {u v : H} (h : ⟪u, v⟫_ℂ = 0) : ⟪u, c • v⟫_ℂ = 0 := by
  rw [inner_smul_right, h, mul_zero]

variable {N : ℕ} (i : Fin N)

def currentWeight (b : Fin 3) (q : Fin N × Fin 3) : ℝ := if q = (i, b) then N else 0

theorem currentWeight_nonneg (b : Fin 3) (q : Fin N × Fin 3) : 0 ≤ currentWeight i b q := by
  unfold currentWeight
  split <;> positivity

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
  (BF : StandardSymmetricFockExponential) (C : CanonicalSectorCCR photonMeasure)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground) (e : ℝ)

include hmult in
set_option maxHeartbeats 200000 in
theorem currentSource (b : Fin 3) (t : SmoothSpatialTest) (m : ℕ)
    (u : Reference (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N)) :
    Nonempty (TestedCurrentSource (A := (B.realization (FullHilbert N)).rank)
      (control := physicalControl F hF J C B S N e)
      (current := testObservable i (PhysicalCovariantKinetic.potential N) C
        (PhysicalProfiles.particleKernel F hF J N) (PhysicalProfiles.particleKernel_measurable F hF J N)
        (PhysicalProfiles.kernelBound F hF J) (PhysicalProfiles.particleKernel_bound F hF J N) B S e
        (.inr (b, t)))
      (physicalKraus BF N m) (inclusion (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N) u)
      (testOperator i (.inr (b, t))) (currentWeight i b) e
      (PhysicalProfiles.cutoffError F J Bsob (testRadius t) m) 3) := by
  classical
  let g := PhysicalProfiles.particleKernel F hF J N
  let hg := PhysicalProfiles.particleKernel_measurable F hF J N
  let L := PhysicalProfiles.kernelBound F hF J
  let hL := PhysicalProfiles.particleKernel_bound F hF J N
  let q := PhysicalCoulombReferenceCore.forget N 1 u
  let r := radiationSource (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N) u
  let U := physicalKraus BF N m
  let κ := fun (j : Fin N × Fin 3) (x : SymmetricLift.Configuration N) =>
    PhysicalProfiles.channelKernel F hF J Bsob hmult m (j.2, particle x j.1)
  have hκ (j : Fin N × Fin 3) : AEStronglyMeasurable (κ j) volume :=
    ((PhysicalProfiles.channelKernel_continuous F hF J Bsob hmult m).comp
      (continuous_const.prodMk (particleLinear j.1).continuous_of_finiteDimensional)).aestronglyMeasurable
  let A := PhysicalProfiles.channelKernelBound F hF J Bsob hmult m
  have hA (j : Fin N × Fin 3) : ∀ᵐ x ∂volume, ‖κ j x‖ ≤ A :=
    ae_of_all _ fun x => PhysicalProfiles.channelKernel_bound F hF J Bsob hmult m (j.2, particle x j.1)
  let k := fun j : Fin N × Fin 3 => tailKernel j.1 F hF J Bsob hmult m j.2
  let hk := fun j : Fin N × Fin 3 => tailKernel_measurable j.1 F hF J Bsob hmult m j.2
  let K := tailKernelBound F hF J Bsob hmult m
  let hK := fun j : Fin N × Fin 3 => tailKernel_bound j.1 F hF J Bsob hmult m j.2
  let d := fun j => covariant (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N) C g hg L hL e j u
  let f := fun j => spatialField volume C (k j) (hk j) K (hK j) r
  let vac := fun j => spatialChannelVacuum volume BF C (physicalSplit m) (κ j) (hκ j) A (hA j) r
  let noise := fun j => (-(e : ℂ)) • vac j
  let loc := fun j => U (d j + (e : ℂ) • f j) + noise j
  have hgraph (a : ℕ) (j : Fin N × Fin 3) :
      covariant (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N) C g hg L hL e j
        (physicalOutputCoulombReference Bsob J hmult BF C B N m q a) = loc j a := by
    have h := physicalOutput_covariant N C g hg L hL e Bsob J hmult BF B m
      κ hκ A hA k hk K hK (fun _ => ae_of_all _ fun _ => rfl)
      (fun _ => ae_of_all _ fun _ => rfl) q a j
    change _ = U (d j + (e : ℂ) • f j) a - (e : ℂ) • vac j a at h
    exact h.trans (by
      change _ = _ + ((-(e : ℂ)) • vac j) a
      simp only [neg_smul, lp.coeFn_neg, lp.coeFn_smul, Pi.neg_apply, Pi.smul_apply, sub_eq_add_neg])
  have hv := control_rankOne_finite (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N)
    C g hg L hL B S e u
  have hout := control_channel_finite Bsob J hmult BF C B N S g hg L hL e m
    ((B.realization (FullHilbert N)).rank.rankOne_positive
      (inclusion (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N) u)) hv
  have hout_eq := congrArg (physicalControl F hF J C B S N e).expectation
    (B.normal.extend_rankOne U
      (inclusion (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N) u))
  have hpure := hout_eq.symm.le.trans_lt hout
  refine ⟨{
    derivative := d
    field := f
    noise := noise
    localized := loc
    mass_le := norm_le_sqrt_control (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N)
      C g hg L hL B S e _ hv
    tested_field_le := ?_
    graph := fun _ => rfl
    orthogonality := ?_
    output_finite := hpure
    original_form := testObservable_rankOne i (PhysicalCovariantKinetic.potential N)
      C g hg L hL B S e (.inr (b, t)) u
    coordinate_form := ?_ }⟩
  · exact sparse_field_bound (i, b) (N : ℝ) _ _ _
      (spatialMultiplier i t.toBoundedSpatialTest) f (Nat.cast_nonneg N)
      (tested_tail_control i t F hF J Bsob hmult (PhysicalCovariantKinetic.potential N)
        C g hg L hL B S e m b u)
  · intro j w
    exact inner_smul_zero (-(e : ℂ))
      (spatialChannelVacuum_orthogonal volume BF C (physicalSplit m) (κ j) (hκ j) A (hA j) r w)
  · intro a
    have he := testObservable_rankOne i (PhysicalCovariantKinetic.potential N) C g hg L hL B S e
      (.inr (b, t)) (physicalOutputCoulombReference Bsob J hmult BF C B N m q a)
    have hvout : inclusion (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N)
        (physicalOutputCoulombReference Bsob J hmult BF C B N m q a) =
        U (inclusion (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N) u) a :=
      physicalOutputCoulombReference_value Bsob J hmult BF C B N m q a
    have hleft := congrArg (fun w : FullHilbert N =>
      (testObservable i (PhysicalCovariantKinetic.potential N) C g hg L hL B S e
        (.inr (b, t))).value ((B.realization (FullHilbert N)).rank.rankOne w)) hvout
    have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
      (fun j _ => congrArg (testOperator i (.inr (b, t)) j) (hgraph a j))
    have hright := congrArg Complex.re
      (congrArg₂ (fun v w : FullHilbert N => ⟪v, w⟫_ℂ) hvout hsum)
    exact hleft.symm.trans (he.trans hright)

include hmult in
/-- Finite actual control supplies the common-domain input reference. -/
theorem current_source_exists (b : Fin 3) (t : SmoothSpatialTest) (m : ℕ)
    (v : FullHilbert N)
    (hv : (physicalControl F hF J C B S N e).expectation
      ((B.realization (FullHilbert N)).rank.rankOne v) < ⊤) :
    Nonempty (TestedCurrentSource (A := (B.realization (FullHilbert N)).rank)
      (control := physicalControl F hF J C B S N e)
      (current := testObservable i (PhysicalCovariantKinetic.potential N) C
        (PhysicalProfiles.particleKernel F hF J N) (PhysicalProfiles.particleKernel_measurable F hF J N)
        (PhysicalProfiles.kernelBound F hF J) (PhysicalProfiles.particleKernel_bound F hF J N) B S e
        (.inr (b, t)))
      (physicalKraus BF N m) v (testOperator i (.inr (b, t))) (currentWeight i b) e
      (PhysicalProfiles.cutoffError F J Bsob (testRadius t) m) 3) := by
  have he := (currentControl_finite_iff (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N)
    C (PhysicalProfiles.particleKernel F hF J N) (PhysicalProfiles.particleKernel_measurable F hF J N)
    (PhysicalProfiles.kernelBound F hF J) (PhysicalProfiles.particleKernel_bound F hF J N) B S e
    ((B.realization (FullHilbert N)).rank.rankOne_positive v)).mp hv
  let P := fun w : FullHilbert N => Nonempty
    (TestedCurrentSource (A := (B.realization (FullHilbert N)).rank)
      (control := physicalControl F hF J C B S N e)
      (current := testObservable i (PhysicalCovariantKinetic.potential N) C
        (PhysicalProfiles.particleKernel F hF J N) (PhysicalProfiles.particleKernel_measurable F hF J N)
        (PhysicalProfiles.kernelBound F hF J) (PhysicalProfiles.particleKernel_bound F hF J N) B S e
        (.inr (b, t)))
      (physicalKraus BF N m) w (testOperator i (.inr (b, t))) (currentWeight i b) e
      (PhysicalProfiles.cutoffError F J Bsob (testRadius t) m) 3)
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
    P (fun u => currentSource i F hF J Bsob hmult BF C B S e b t m u) he

def testEpsilon : SmoothPairTest → ℕ → ℝ
  | .inl _ => fun _ => 0
  | .inr (_, t) => PhysicalProfiles.cutoffError F J Bsob (testRadius t)

def testFieldConstant : SmoothPairTest → ℝ
  | .inl _ => 0
  | .inr _ => 3

def testWeightConstant : SmoothPairTest → (Fin N × Fin 3) → ℝ
  | .inl _ => fun _ => 0
  | .inr (b, _) => currentWeight i b

theorem testEpsilon_nonneg (t : SmoothPairTest) (m : ℕ) : 0 ≤ testEpsilon F J Bsob t m := by
  cases t with
  | inl _ => exact le_rfl
  | inr t => exact PhysicalProfiles.cutoffError_nonneg F J Bsob (testRadius t.2) m

theorem testEpsilon_zero (t : SmoothPairTest) :
    Filter.Tendsto (testEpsilon F J Bsob t) Filter.atTop (nhds 0) := by
  cases t with
  | inl _ => exact tendsto_const_nhds
  | inr t => exact PhysicalProfiles.cutoffError_zero F J Bsob (testRadius t.2)

theorem testFieldConstant_nonneg (t : SmoothPairTest) : 0 ≤ testFieldConstant t := by
  cases t <;> norm_num [testFieldConstant]

theorem testWeightConstant_nonneg (t : SmoothPairTest) (q : Fin N × Fin 3) :
    0 ≤ testWeightConstant i t q := by
  cases t with
  | inl _ => exact le_rfl
  | inr t => exact currentWeight_nonneg i t.1 q

include hmult in
/-- All density/current source data come from the same physical channel. -/
theorem test_source_exists (t : SmoothPairTest) (m : ℕ) (v : FullHilbert N)
    (hv : (physicalControl F hF J C B S N e).expectation
      ((B.realization (FullHilbert N)).rank.rankOne v) < ⊤) :
    Nonempty (TestedCurrentSource (A := (B.realization (FullHilbert N)).rank)
      (control := physicalControl F hF J C B S N e)
      (current := testObservable i (PhysicalCovariantKinetic.potential N) C
        (PhysicalProfiles.particleKernel F hF J N) (PhysicalProfiles.particleKernel_measurable F hF J N)
        (PhysicalProfiles.kernelBound F hF J) (PhysicalProfiles.particleKernel_bound F hF J N) B S e t)
      (physicalKraus BF N m) v (testOperator i t) (testWeightConstant i t) e
      (testEpsilon F J Bsob t m) (testFieldConstant t)) := by
  cases t with
  | inl t =>
    exact density_source_exists Bsob J hmult BF C B N S
      (PhysicalProfiles.particleKernel F hF J N) (PhysicalProfiles.particleKernel_measurable F hF J N)
      (PhysicalProfiles.kernelBound F hF J) (PhysicalProfiles.particleKernel_bound F hF J N) e i t m v hv
  | inr t => exact current_source_exists i F hF J Bsob hmult BF C B S e t.1 t.2 m v hv

end GptLean.PhysicalPFLocalization
