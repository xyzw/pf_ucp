import PfHk.PauliCommonFormDomain

/-! The common closed Pauli form on the joint position--spin fermionic
sector. Antisymmetry is expressed in the actual spin--photon L2 space,
whose permutation equalizers are closed. Form limits therefore retain
the same fermionic condition. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliFermionicClosedForm

open MeasureTheory Filter Topology GptLean GptLean.PhysicalFock
  GptLean.PhysicalPFReference GptLean.PhysicalPairDuality
  PfHk.PauliSpin PfHk.PauliGroundState PfHk.PauliClosedForm
  PfHk.PauliFormBounds PfHk.PauliFormTopology PfHk.PhysicalCommonFormDomain

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

private theorem closed_equalizers {P S Q H : Type*} [TopologicalSpace Q]
    [TopologicalSpace H] [T2Space H] (L R : P → S → Q → H)
    (hL : ∀ p s, Continuous (L p s)) (hR : ∀ p s, Continuous (R p s)) :
    IsClosed {u | ∀ p s, L p s u = R p s u} := by
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun p => isClosed_iInter fun s => isClosed_eq (hL p s) (hR p s)

variable {N : ℕ}
attribute [local irreducible] referenceSubspace inclusion
  shiftedEnergy physicalShiftedEnergy normSquared ordinaryEnergy radiationEnergy

def left (π : Equiv.Perm (Fin N)) (s : SpinIndex N) :
    PauliReference.Wave N →L[ℂ] WaveSpace (Fin N × Fin 3) :=
  (PhysicalReferencePermutation.pull (Q := PhotonFock) π).toContinuousLinearMap.comp
    (FiniteFiberL2.coordinate (fun n => s (π.symm n)))

def right (π : Equiv.Perm (Fin N)) (s : SpinIndex N) :
    PauliReference.Wave N →L[ℂ] WaveSpace (Fin N × Fin 3) :=
  PhysicalElectronicFermions.signCharacter N π • FiniteFiberL2.coordinate s

/-- Joint position--spin antisymmetry in the physical Hilbert space. -/
def JointFermionic (ψ : PauliReference.Wave N) : Prop :=
  ∀ π s, left π s ψ = right π s ψ

theorem jointFermionic_closed : IsClosed {ψ : PauliReference.Wave N | JointFermionic ψ} :=
  closed_equalizers (fun π s => left π s) (fun π s => right π s)
    (fun π s => (left π s).continuous) (fun π s => (right π s).continuous)

theorem left_wave (π : Equiv.Perm (Fin N)) (s : SpinIndex N) (u : Ref N) :
    left π s (PauliReference.wave u) =
      inclusion (Fin N × Fin 3) (fun _ => 0) (jointPermutation π u s) := by
  have hcoord : FiniteFiberL2.coordinate (fun n => s (π.symm n)) (PauliReference.wave u) =
      inclusion (Fin N × Fin 3) (fun _ => 0) (u (fun n => s (π.symm n))) :=
    FiniteFiberL2.coordinate_bundle _ _
  exact (congrArg (PhysicalReferencePermutation.pull (Q := PhotonFock) π) hcoord).trans
    (PhysicalReferencePermutation.inclusion_permutation π (u (fun n => s (π.symm n)))).symm

theorem right_wave (π : Equiv.Perm (Fin N)) (s : SpinIndex N) (u : Ref N) :
    right π s (PauliReference.wave u) = PhysicalElectronicFermions.signCharacter N π •
      inclusion (Fin N × Fin 3) (fun _ => 0) (u s) :=
  congrArg (fun w : WaveSpace (Fin N × Fin 3) =>
    PhysicalElectronicFermions.signCharacter N π • w) (FiniteFiberL2.coordinate_bundle _ s)

attribute [local irreducible] left right PauliReference.wave

theorem wave_fermionic_iff (u : Ref N) : JointFermionic (PauliReference.wave u) ↔ Fermionic u := by
  constructor
  · intro h π
    funext s
    apply inclusion_injective (Fin N × Fin 3) (fun _ => 0)
    exact (left_wave π s u).symm.trans ((h π s).trans
      ((right_wave π s u).trans
        ((inclusion (Fin N × Fin 3) (fun _ => 0)).map_smul
          (PhysicalElectronicFermions.signCharacter N π) (u s)).symm))
  · intro h π s
    have he := congrArg (fun w : Ref N => inclusion (Fin N × Fin 3) (fun _ => 0) (w s)) (h π)
    exact (left_wave π s u).trans (he.trans
      (((inclusion (Fin N × Fin 3) (fun _ => 0)).map_smul
        (PhysicalElectronicFermions.signCharacter N π) (u s)).trans (right_wave π s u).symm))

theorem fermionic_closed_in_reference : IsClosed {u : Ref N | Fermionic u} := by
  have he : {u : Ref N | Fermionic u} =
      PauliReference.wave ⁻¹' {ψ : PauliReference.Wave N | JointFermionic ψ} := by
    ext u
    exact (wave_fermionic_iff u).symm
  exact Eq.mpr (congrArg (fun S : Set (Ref N) => IsClosed S) he)
    ((jointFermionic_closed (N := N)).preimage (wave_continuous (N := N)))

/-- The common physical form domain including joint antisymmetry. -/
def fermionicDomain : Set (PauliReference.Wave N) :=
  {ψ | ∃ u : Ref N, Fermionic u ∧ PauliReference.wave u = ψ}

theorem fermionicDomain_iff (ψ : PauliReference.Wave N) :
    ψ ∈ fermionicDomain (N := N) ↔
      PauliCommonFormDomain.ElectronicRadiationDomain ψ ∧ JointFermionic ψ := by
  constructor
  · intro h
    let u := Classical.choose h
    have hu := Classical.choose_spec h
    exact ⟨(PauliCommonFormDomain.physicalDomain_iff ψ).mp ⟨u, hu.2⟩,
      hu.2 ▸ (wave_fermionic_iff u).mpr hu.1⟩
  · intro h
    have hex := (PauliCommonFormDomain.physicalDomain_iff ψ).mpr h.1
    let u := Classical.choose hex
    have hu := Classical.choose_spec hex
    exact ⟨u, (wave_fermionic_iff u).mp (hu.symm ▸ h.2), hu⟩

theorem fermionicDomain_coefficients (A : VectorPotential) (v : ScalarPotential)
    (c : ℝ) (hc : 0 ≤ c) (ψ : PauliReference.Wave N) :
    ψ ∈ fermionicDomain (N := N) ↔ ∃ u : Ref N,
      Fermionic u ∧ PauliReference.wave u = ψ ∧
        Domain (vector A) (positive v c) (negative v c) u := by
  constructor
  · intro h
    let u := Classical.choose h
    have hu := Classical.choose_spec h
    exact ⟨u, hu.1, hu.2, PauliCoefficientBounds.domain A v c hc u⟩
  · intro h
    let u := Classical.choose h
    have hu := Classical.choose_spec h
    exact ⟨u, hu.1, hu.2.1⟩

variable (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hκ : ∀ q, AEStronglyMeasurable (κ q) volume)
  (M : ℝ) (hκbound : ∀ q, ∀ᵐ X ∂volume, ‖κ q X‖ ≤ M) (e : ℝ)
  (A : VectorPotential) (v : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)

/-- Shifted-form Cauchy sequences in the actual fermionic sector converge
inside that same sector in both the physical L2 and form norms. -/
theorem fermionic_complete (u : ℕ → Ref N) (hF : ∀ n, Fermionic (u n))
    (hu : FormCauchy (shiftedEnergy C κ hκ M hκbound e A v c hc) u) :
    ∃ z : Ref N, Fermionic z ∧
      Tendsto (fun n => PauliReference.wave (u n)) atTop (𝓝 (PauliReference.wave z)) ∧
      Tendsto (fun n => shiftedEnergy C κ hκ M hκbound e A v c hc (u n - z)) atTop (𝓝 0) := by
  have hK : 0 < 16 * (recoveryFactor N e M + 1) := by unfold recoveryFactor; positivity
  have hex := complete_of_coercive (Q := Ref N)
    (shiftedEnergy C κ hκ M hκbound e A v c hc)
    (shiftedEnergy_continuous C κ hκ M hκbound e A v c hc)
    (shiftedEnergy_zero C κ hκ M hκbound e A v c hc)
    _ hK (shiftedEnergy_coercive C κ hκ M hκbound e A v c hc) u hu
  let z := Classical.choose hex
  have hzRef := (Classical.choose_spec hex).1
  have hq := (Classical.choose_spec hex).2
  have hz : Tendsto (fun n => PauliReference.wave (u n)) atTop (𝓝 (PauliReference.wave z)) :=
    ((wave_continuous (N := N)).tendsto z).comp hzRef
  have hzF : JointFermionic (PauliReference.wave z) := (jointFermionic_closed (N := N)).mem_of_tendsto hz
    (Eventually.of_forall fun n => (wave_fermionic_iff (u n)).mpr (hF n))
  exact ⟨z, (wave_fermionic_iff z).mp hzF, hz, hq⟩

open GptLean.PhysicalPolarization PfHk.CenteredPhysicalReference

/-- Closedness on the paper's joint fermionic domain for the actual
physical Pauli energy and profile, with no stronger UV hypothesis. -/
theorem physical_fermionic_complete (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
    (F : Frame) (χ : ArticleCutoff) (A : VectorPotential) (v : ScalarPotential)
    (c : ℝ) (hc : 0 ≤ c) (u : ℕ → Ref N) (hF : ∀ n, Fermionic (u n))
    (hu : FormCauchy (physicalShiftedEnergy C e F χ A v c hc) u) :
    ∃ z : Ref N, Fermionic z ∧
      Tendsto (fun n => PauliReference.wave (u n)) atTop (𝓝 (PauliReference.wave z)) ∧
      Tendsto (fun n => physicalShiftedEnergy C e F χ A v c hc (u n - z)) atTop (𝓝 0) := by
  have hu' : FormCauchy
      (shiftedEnergy C (profile F χ 0) (profile_measurable F χ 0) (profileBound F χ)
        (profile_bound F χ 0) e A v c hc) u := by
    simpa only [FormCauchy, physicalShiftedEnergy_eq] using hu
  have hex := fermionic_complete C (profile F χ 0) (profile_measurable F χ 0)
    (profileBound F χ) (profile_bound F χ 0) e A v c hc u hF hu'
  let z := Classical.choose hex
  have hs := Classical.choose_spec hex
  exact ⟨z, hs.1, hs.2.1, by simpa only [physicalShiftedEnergy_eq] using hs.2.2⟩

end PfHk.PauliFermionicClosedForm

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
