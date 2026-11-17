import PfHk.PauliFormTopology
import PfHk.PauliPhysicalFormBounds

/-! Closedness of the physical Pauli form on its common spin--photon
reference domain. The coefficient classes provide the lower bound and
coercivity. Completeness follows from the already complete ordinary
electronic and radiation graph, with convergence in the actual L2 space. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliClosedForm

open MeasureTheory Filter Topology GptLean GptLean.PhysicalFock
  GptLean.PhysicalPFReference GptLean.PhysicalPairDuality
  PfHk.PauliGroundState PfHk.PauliFormBounds PfHk.PauliFormTopology
  PfHk.PhysicalCommonFormDomain PfHk.PauliPhysicalFormBounds

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000

section Completeness

variable {Q H : Type*} [NormedAddCommGroup Q] [CompleteSpace Q]
  [NormedAddCommGroup H]

/-- The usual Cauchy condition for the squared norm of a positive form. -/
def FormCauchy (q : Q → ℝ) (u : ℕ → Q) : Prop :=
  ∀ ε > 0, ∃ m : ℕ, ∀ i ≥ m, ∀ j ≥ m, q (u i - u j) < ε

/-- The sequential closed-form criterion on an embedded domain. The
shifted form dominates the actual Hilbert norm and every form-Cauchy
sequence has a limit in the same domain in both norms. -/
def IsClosedOn (J : Q → H) (q : Q → ℝ) : Prop :=
  ∃ b : ℝ,
    (∀ u, ‖J u‖ ^ 2 ≤ q u + b * ‖J u‖ ^ 2) ∧
    ∀ u : ℕ → Q, FormCauchy (fun z => q z + b * ‖J z‖ ^ 2) u →
      ∃ v : Q, Tendsto (fun n => J (u n)) atTop (𝓝 (J v)) ∧
        Tendsto (fun n => q (u n - v) + b * ‖J (u n - v)‖ ^ 2) atTop (𝓝 0)

theorem complete_of_coercive (q : Q → ℝ) (hq : Continuous q) (hq0 : q 0 = 0)
    (K : ℝ) (hK : 0 < K) (hcoercive : ∀ z, ‖z‖ ^ 2 ≤ K * q z)
    (u : ℕ → Q) (hu : FormCauchy q u) :
    ∃ v : Q, Tendsto u atTop (𝓝 v) ∧
      Tendsto (fun n => q (u n - v)) atTop (𝓝 0) := by
  have hc : CauchySeq u := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨m, hm⟩ := hu (ε ^ 2 / K) (div_pos (sq_pos_of_pos hε) hK)
    refine ⟨m, fun i hi j hj => ?_⟩
    have h := mul_lt_mul_of_pos_left (hm i hi j hj) hK
    have hb := hcoercive (u i - u j)
    have heq : K * (ε ^ 2 / K) = ε ^ 2 := mul_div_cancel₀ _ (ne_of_gt hK)
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (u i - u j)]
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨v, hv, ?_⟩
  have hdiff : Tendsto (fun n => u n - v) atTop (𝓝 (0 : Q)) := by
    simpa only [sub_self] using hv.sub_const v
  simpa only [hq0, Function.comp_def] using (hq.tendsto 0).comp hdiff

end Completeness

variable {N : ℕ}

attribute [local irreducible] referenceSubspace inclusion ordinary radiation
  PhysicalPFReference.field rawCovariant rawContraction PhysicalLocalEnergy.externalCovariant
  PhysicalLocalEnergy.roughMultiply rawForm rawEnergy normSquared ordinaryEnergy radiationEnergy
  pauliEnergy recoveryFactor massFactor PauliPhysicalFormBounds.lowerMass
  PauliPhysicalFormBounds.fullMass PauliPhysicalFormBounds.constants

variable (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hκ : ∀ q, AEStronglyMeasurable (κ q) volume)
  (M : ℝ) (hκbound : ∀ q, ∀ᵐ X ∂volume, ‖κ q X‖ ≤ M) (e : ℝ)
  (A : VectorPotential) (v : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)

def shift : ℝ :=
  lowerMass (N := N) A v c hc e M + fullMass (N := N) A v c hc e M + 1

def shiftedEnergy (u : Ref N) : ℝ :=
  rawEnergy C κ hκ M hκbound e (vector A) (positive v c) (negative v c) u
      (PauliCoefficientBounds.domain A v c hc u) +
    shift (N := N) M e A v c hc * normSquared u

theorem shiftedEnergy_ge_mass (u : Ref N) :
    normSquared u ≤ shiftedEnergy C κ hκ M hκbound e A v c hc u := by
  have h := semibounded C κ hκ M hκbound e A v c hc u
  have hn := normSquared_nonneg u
  have hf := mul_nonneg (fullMass_nonneg (N := N) M e A v c hc) hn
  unfold shiftedEnergy shift
  nlinarith only [h, hf]

theorem shiftedEnergy_coercive (u : Ref N) :
    ‖u‖ ^ 2 ≤ 16 * (recoveryFactor N e M + 1) *
      shiftedEnergy C κ hκ M hκbound e A v c hc u := by
  have hr : 0 ≤ recoveryFactor N e M := by unfold recoveryFactor; positivity
  have ha := lowerMass_nonneg (N := N) A v c hc e M
  have hb := fullMass_nonneg (N := N) M e A v c hc
  have hcoeff : 4 * (fullMass (N := N) A v c hc e M + 1) ≤
      16 * (recoveryFactor N e M + 1) * shift (N := N) M e A v c hc := by
    unfold shift
    nlinarith [mul_nonneg hr ha, mul_nonneg hr hb]
  have hcm := mul_le_mul_of_nonneg_right hcoeff (normSquared_nonneg u)
  have hfull := PauliPhysicalFormBounds.full_energy_bound C κ hκ M hκbound e A v c hc u
  have href := reference_norm_sq_le u
  have hp := pauliEnergy_nonneg C κ hκ M hκbound e (vector A) (positive v c) (negative v c)
    u (PauliCoefficientBounds.domain A v c hc u)
  unfold shiftedEnergy
  nlinarith only [hcm, hfull, href, hp]

theorem shiftedEnergy_continuous :
    Continuous (shiftedEnergy C κ hκ M hκbound e A v c hc) :=
  (rawEnergy_continuous C κ hκ M hκbound e (vector A) (positive v c) (negative v c)
    (PauliCoefficientBounds.domain A v c hc)).add
    (normSquared_continuous.const_mul (shift (N := N) M e A v c hc))

theorem shiftedEnergy_zero : shiftedEnergy C κ hκ M hκbound e A v c hc 0 = 0 := by
  have he := rawEnergy_zero C κ hκ M hκbound e (vector A) (positive v c) (negative v c)
    (PauliCoefficientBounds.domain A v c hc)
  have hn : normSquared (0 : Ref N) = 0 := by simp [normSquared]
  simp only [shiftedEnergy, he, hn, mul_zero, add_zero]

theorem shiftedEnergy_eq_L2 (u : Ref N) :
    shiftedEnergy C κ hκ M hκbound e A v c hc u =
      rawEnergy C κ hκ M hκbound e (vector A) (positive v c) (negative v c) u
        (PauliCoefficientBounds.domain A v c hc u) +
      shift (N := N) M e A v c hc * ‖PauliReference.wave u‖ ^ 2 := by
  have hn : normSquared u = ‖PauliReference.wave u‖ ^ 2 := by
    unfold normSquared
    exact (PauliReference.wave_norm_sq u).symm
  exact congrArg (fun t : ℝ =>
    rawEnergy C κ hκ M hκbound e (vector A) (positive v c) (negative v c) u
      (PauliCoefficientBounds.domain A v c hc u) + shift (N := N) M e A v c hc * t) hn

attribute [local irreducible] shiftedEnergy PauliReference.wave

/-- The physical Pauli form is closed and lower semibounded. No multiplier
or physical closedness assumption is supplied beyond the coefficient
classes and the actual photon field bound. -/
theorem isClosedOn :
    IsClosedOn (PauliReference.wave (N := N))
      (fun u => rawEnergy C κ hκ M hκbound e (vector A) (positive v c) (negative v c) u
        (PauliCoefficientBounds.domain A v c hc u)) := by
  refine ⟨shift (N := N) M e A v c hc, ?_, ?_⟩
  · intro u
    simpa only [PauliReference.wave_norm_sq, shiftedEnergy, normSquared] using
      shiftedEnergy_ge_mass C κ hκ M hκbound e A v c hc u
  · intro u hu
    have hu' : FormCauchy (shiftedEnergy C κ hκ M hκbound e A v c hc) u := by
      simpa only [FormCauchy, PauliReference.wave_norm_sq, shiftedEnergy, normSquared] using hu
    have hK : 0 < 16 * (recoveryFactor N e M + 1) := by unfold recoveryFactor; positivity
    have hex := complete_of_coercive (Q := Ref N)
      (shiftedEnergy C κ hκ M hκbound e A v c hc)
      (shiftedEnergy_continuous C κ hκ M hκbound e A v c hc)
      (shiftedEnergy_zero C κ hκ M hκbound e A v c hc)
      _ hK (shiftedEnergy_coercive C κ hκ M hκbound e A v c hc) u hu'
    let z := Classical.choose hex
    have hz := (Classical.choose_spec hex).1
    have hq := (Classical.choose_spec hex).2
    refine ⟨z, ?_, ?_⟩
    · exact ((wave_continuous (N := N)).tendsto z).comp hz
    · have he : (fun n => shiftedEnergy C κ hκ M hκbound e A v c hc (u n - z)) =
          (fun n => rawEnergy C κ hκ M hκbound e (vector A) (positive v c) (negative v c)
            (u n - z) (PauliCoefficientBounds.domain A v c hc (u n - z)) +
            shift (N := N) M e A v c hc * ‖PauliReference.wave (u n - z)‖ ^ 2) :=
        funext fun n => shiftedEnergy_eq_L2 C κ hκ M hκbound e A v c hc (u n - z)
      exact Eq.mp (congrArg (fun f : ℕ → ℝ => Tendsto f atTop (𝓝 0)) he) hq

/-- The common form domain is the range of the same actual spin--photon
reference inclusion for every admissible external coefficient. -/
def physicalDomain : Set (PauliReference.Wave N) := Set.range (PauliReference.wave (N := N))

theorem mem_physicalDomain (hc : 0 ≤ c) (ψ : PauliReference.Wave N) :
    ψ ∈ physicalDomain (N := N) ↔ ∃ u : Ref N,
      PauliReference.wave u = ψ ∧ Domain (vector A) (positive v c) (negative v c) u := by
  constructor
  · intro h
    let u := Classical.choose h
    have hu := Classical.choose_spec h
    exact ⟨u, hu, PauliCoefficientBounds.domain A v c hc u⟩
  · intro h
    let u := Classical.choose h
    have hu := Classical.choose_spec h
    exact ⟨u, hu.1⟩

open GptLean.PhysicalPolarization PfHk.CenteredPhysicalReference

theorem physical_energy_eq_raw (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
    (F : Frame) (χ : ArticleCutoff) (A : VectorPotential) (v : ScalarPotential)
    (c : ℝ) (hc : 0 ≤ c) (u : Ref N) :
    PauliGroundState.energy C e F χ A v c hc u =
      rawEnergy C (profile F χ 0) (profile_measurable F χ 0) (profileBound F χ)
        (profile_bound F χ 0) e (vector A) (positive v c) (negative v c) u
        (PauliCoefficientBounds.domain A v c hc u) := by
  unfold PauliGroundState.energy PauliGroundState.form rawEnergy
  rfl

/-- The public closedness endpoint for the actual physical Pauli energy. -/
theorem physical_closed (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
    (F : Frame) (χ : ArticleCutoff) (A : VectorPotential) (v : ScalarPotential)
    (c : ℝ) (hc : 0 ≤ c) :
    IsClosedOn (PauliReference.wave (N := N)) (PauliGroundState.energy C e F χ A v c hc) := by
  have he : (fun u : Ref N =>
      rawEnergy C (profile F χ 0) (profile_measurable F χ 0) (profileBound F χ)
        (profile_bound F χ 0) e (vector A) (positive v c) (negative v c) u
        (PauliCoefficientBounds.domain A v c hc u)) = PauliGroundState.energy C e F χ A v c hc :=
    funext fun u => (physical_energy_eq_raw C e F χ A v c hc u).symm
  exact (congrArg (IsClosedOn (PauliReference.wave (N := N))) he).mp
    (isClosedOn C (profile F χ 0) (profile_measurable F χ 0) (profileBound F χ)
      (profile_bound F χ 0) e A v c hc)

theorem physical_semibounded (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
    (F : Frame) (χ : ArticleCutoff) (A : VectorPotential) (v : ScalarPotential)
    (c : ℝ) (hc : 0 ≤ c) (u : Ref N) :
    -(lowerMass (N := N) A v c hc e (profileBound F χ)) * normSquared u ≤
      PauliGroundState.energy C e F χ A v c hc u := by
  rw [physical_energy_eq_raw]
  exact PauliPhysicalFormBounds.semibounded C (profile F χ 0) (profile_measurable F χ 0)
    (profileBound F χ) (profile_bound F χ 0) e A v c hc u

def physicalShiftedEnergy (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
    (F : Frame) (χ : ArticleCutoff) (A : VectorPotential) (v : ScalarPotential)
    (c : ℝ) (hc : 0 ≤ c) (u : Ref N) : ℝ :=
  PauliGroundState.energy C e F χ A v c hc u +
    shift (N := N) (profileBound F χ) e A v c hc * normSquared u

theorem physicalShiftedEnergy_eq (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
    (F : Frame) (χ : ArticleCutoff) (A : VectorPotential) (v : ScalarPotential)
    (c : ℝ) (hc : 0 ≤ c) (u : Ref N) :
    physicalShiftedEnergy C e F χ A v c hc u =
      shiftedEnergy C (profile F χ 0) (profile_measurable F χ 0) (profileBound F χ)
        (profile_bound F χ 0) e A v c hc u := by
  unfold physicalShiftedEnergy shiftedEnergy
  rw [physical_energy_eq_raw]

theorem physicalShiftedEnergy_ge_mass (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
    (F : Frame) (χ : ArticleCutoff) (A : VectorPotential) (v : ScalarPotential)
    (c : ℝ) (hc : 0 ≤ c) (u : Ref N) :
    normSquared u ≤ physicalShiftedEnergy C e F χ A v c hc u := by
  rw [physicalShiftedEnergy_eq]
  exact shiftedEnergy_ge_mass C (profile F χ 0) (profile_measurable F χ 0)
    (profileBound F χ) (profile_bound F χ 0) e A v c hc u

end PfHk.PauliClosedForm

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
