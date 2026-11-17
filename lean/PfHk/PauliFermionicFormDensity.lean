import PfHk.PauliFormDensity
import PfHk.PauliFermionicClosedForm
import PfHk.PauliGroundStateWeak
import PfHk.PauliPermutation

/-! The common Pauli form domain is dense in the physical jointly
antisymmetric Hilbert space. Finite signed averages on the reference
space and the physical L2 space intertwine with the actual inclusion. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliFermionicFormDensity

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  PfHk.PauliSpin PfHk.PauliGroundState PfHk.PauliFermionicClosedForm
  PfHk.KatoRellichBackground PfHk.PhysicalExternalOperator

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000
set_option maxErrors 1

private def bundleLinear {S X H : Type*} [Fintype S] [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (μ : Measure X) :
    (S → Lp H 2 μ) →L[ℂ] Lp (FiniteFiberL2.Fiber (S := S) (H := H)) 2 μ :=
  FiniteFiberL2.isometry.toContinuousLinearMap.comp
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : S => Lp H 2 μ)).symm.toContinuousLinearMap

private theorem average_intertwines {G Q H : Type*} [Group G] [Fintype G]
    [AddCommGroup Q] [Module ℂ Q] [AddCommGroup H] [Module ℂ H]
    (J : Q →ₗ[ℂ] H) (ρ : G → Q →ₗ[ℂ] Q) (T : G → H →ₗ[ℂ] H)
    (h : ∀ g u, T g (J u) = J (ρ g u)) (u : Q) :
    FiniteFormReduction.average T (J u) = J (FiniteFormReduction.average ρ u) := by
  simp only [FiniteFormReduction.average_apply, map_smul, map_sum]
  exact congrArg ((Fintype.card G : ℂ)⁻¹ • ·)
    (Finset.sum_congr rfl fun g _ => h g u)

private theorem average_twist_continuous {G H : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    (T : G → H →L[ℂ] H) (s : G → ℂ) :
    Continuous (FiniteFormReduction.average
      (SignTwistedReduction.twist (fun g => (T g).toLinearMap) s)) := by
  let P : H →L[ℂ] H := (Fintype.card G : ℂ)⁻¹ • ∑ g, s g • T g
  have h : (FiniteFormReduction.average
      (SignTwistedReduction.twist (fun g => (T g).toLinearMap) s) : H → H) = P := by
    funext x
    simp only [FiniteFormReduction.average_apply, SignTwistedReduction.twist_apply,
      P, smul_apply, sum_apply]
    rfl
  rw [h]
  exact P.continuous

private theorem average_twist_intertwines {G Q H : Type*} [Group G] [Fintype G]
    [AddCommGroup Q] [Module ℂ Q] [AddCommGroup H] [Module ℂ H]
    (J : Q →ₗ[ℂ] H) (ρ : G → Q →ₗ[ℂ] Q) (T : G → H →ₗ[ℂ] H)
    (s : G → ℂ) (h : ∀ g u, T g (J u) = J (ρ g u)) (u : Q) :
    FiniteFormReduction.average (SignTwistedReduction.twist T s) (J u) =
      J (FiniteFormReduction.average (SignTwistedReduction.twist ρ s) u) := by
  apply average_intertwines J (SignTwistedReduction.twist ρ s)
    (SignTwistedReduction.twist T s)
  intro g z
  simp only [SignTwistedReduction.twist_apply, map_smul]
  exact congrArg (s g • ·) (h g z)

private theorem closure_eq_of_projection {Q H : Type*} [TopologicalSpace H]
    (J : Q → H) (P : H → H) (D S : Set H)
    (hJ : DenseRange J) (hP : Continuous P) (hS : IsClosed S)
    (hDS : D ⊆ S) (hPD : ∀ u, P (J u) ∈ D) (hfix : ∀ x ∈ S, P x = x) :
    closure D = S := by
  apply Set.Subset.antisymm (closure_minimal hDS hS)
  intro x hx
  have himage : P '' Set.range J ⊆ D := by
    rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
    exact hPD u
  have hp := mem_closure_image hP.continuousAt (hJ x)
  exact (hfix x hx) ▸ closure_mono himage hp

variable {N : ℕ}
attribute [local instance] PauliGroundStateWeak.referenceAddCommGroup
  PauliGroundStateWeak.referenceModule PauliGroundStateWeak.referenceSMul
attribute [local irreducible] referenceSubspace inclusion PauliReference.wave
  PauliGroundStateWeak.permutation PauliGroundStateWeak.waveLinear

/-- The actual joint position and spin permutation on physical L2 waves. -/
def wavePermutation (π : Equiv.Perm (Fin N)) :
    PauliReference.Wave N →L[ℂ] PauliReference.Wave N :=
  (bundleLinear volume).comp (ContinuousLinearMap.pi fun s => left π s)

theorem wavePermutation_apply (π : Equiv.Perm (Fin N)) (ψ : PauliReference.Wave N) :
    wavePermutation π ψ = FiniteFiberL2.bundle (fun s => left π s ψ) := rfl

theorem wavePermutation_wave (π : Equiv.Perm (Fin N)) (u : Ref N) :
    wavePermutation π (PauliReference.wave u) = PauliReference.wave (jointPermutation π u) := by
  have hb : FiniteFiberL2.bundle
      (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (jointPermutation π u s)) =
      PauliReference.wave (jointPermutation π u) := by
    unfold PauliReference.wave
    rfl
  exact (wavePermutation_apply π (PauliReference.wave u)).trans
    ((congrArg (FiniteFiberL2.bundle (S := SpinIndex N) (H := PhotonFock) (μ := volume))
      (funext fun s => left_wave π s u)).trans hb)

theorem wavePermutation_fermionic (π : Equiv.Perm (Fin N))
    (ψ : PauliReference.Wave N) (hψ : JointFermionic ψ) :
    wavePermutation π ψ = PhysicalElectronicFermions.signCharacter N π • ψ := by
  have hcoord : (fun s => left π s ψ) =
      PhysicalElectronicFermions.signCharacter N π • (fun s => FiniteFiberL2.coordinate s ψ) := by
    funext s
    exact hψ π s
  exact (wavePermutation_apply π ψ).trans
    ((congrArg (FiniteFiberL2.bundle (S := SpinIndex N) (H := PhotonFock) (μ := volume)) hcoord).trans
      ((FiniteFiberL2.bundle_smul _ _).trans
        (congrArg (PhysicalElectronicFermions.signCharacter N π • ·)
          (FiniteFiberL2.bundle_coordinate ψ))))

attribute [local irreducible] wavePermutation

/-- Signed finite averaging on the actual physical Hilbert space. -/
def waveAverage : PauliReference.Wave N →ₗ[ℂ] PauliReference.Wave N :=
  FiniteFormReduction.average
    (SignTwistedReduction.twist (fun π => (wavePermutation π).toLinearMap)
      (PhysicalElectronicFermions.signCharacter N))

theorem waveAverage_continuous : Continuous (waveAverage (N := N)) :=
  average_twist_continuous wavePermutation (PhysicalElectronicFermions.signCharacter N)

theorem waveAverage_eq_self (ψ : PauliReference.Wave N) (hψ : JointFermionic ψ) :
    waveAverage ψ = ψ :=
  FiniteFormReduction.average_eq_self _
    ((SignTwistedReduction.fixed_iff
      (fun π => (wavePermutation π).toLinearMap)
      (PhysicalElectronicFermions.signCharacter N) PhysicalFermionicAverage.sign_square ψ).mpr
        (fun π => wavePermutation_fermionic π ψ hψ))

/-- The same signed average preserves the electronic and radiation domain. -/
def referenceAverage : Ref N →ₗ[ℂ] Ref N :=
  FiniteFormReduction.average
    (SignTwistedReduction.twist PauliGroundStateWeak.permutation
      (PhysicalElectronicFermions.signCharacter N))

theorem referenceAverage_fermionic (u : Ref N) : Fermionic (referenceAverage u) := by
  have hmul (π σ : Equiv.Perm (Fin N)) (z : Ref N) :
      PauliGroundStateWeak.permutation π (PauliGroundStateWeak.permutation σ z) =
        PauliGroundStateWeak.permutation (σ * π) z :=
    (PauliGroundStateWeak.permutation_apply π (PauliGroundStateWeak.permutation σ z)).trans
      ((congrArg (jointPermutation π) (PauliGroundStateWeak.permutation_apply σ z)).trans
        ((PauliPermutation.joint_mul π σ z).trans
          (PauliGroundStateWeak.permutation_apply (σ * π) z).symm))
  apply (PauliGroundStateWeak.mem_sector_iff _).mp
  exact FiniteFormReduction.average_fixed _
    (SignTwistedReduction.twist_mul PauliGroundStateWeak.permutation
      (PhysicalElectronicFermions.signCharacter N) hmul PhysicalFermionicAverage.sign_mul) u

private theorem wavePermutation_waveLinear (π : Equiv.Perm (Fin N)) (z : Ref N) :
    wavePermutation π (PauliGroundStateWeak.waveLinear (N := N) z) =
      PauliGroundStateWeak.waveLinear (N := N) (PauliGroundStateWeak.permutation π z) :=
  (congrArg (wavePermutation π) (PauliGroundStateWeak.waveLinear_apply z)).trans
    ((wavePermutation_wave π z).trans
      ((congrArg (PauliReference.wave (N := N))
        (PauliGroundStateWeak.permutation_apply π z).symm).trans
          (PauliGroundStateWeak.waveLinear_apply (PauliGroundStateWeak.permutation π z)).symm))

private theorem waveAverage_waveLinear (u : Ref N) :
    waveAverage (PauliGroundStateWeak.waveLinear (N := N) u) =
      PauliGroundStateWeak.waveLinear (N := N) (referenceAverage u) := by
  unfold waveAverage referenceAverage
  exact average_twist_intertwines (PauliGroundStateWeak.waveLinear (N := N))
    (PauliGroundStateWeak.permutation (N := N))
    (fun π => (wavePermutation π).toLinearMap)
    (PhysicalElectronicFermions.signCharacter N) wavePermutation_waveLinear u

theorem waveAverage_wave (u : Ref N) :
    waveAverage (PauliReference.wave u) = PauliReference.wave (referenceAverage u) := by
  exact (congrArg waveAverage (PauliGroundStateWeak.waveLinear_apply u)).symm.trans
    ((waveAverage_waveLinear u).trans (PauliGroundStateWeak.waveLinear_apply (referenceAverage u)))

attribute [local irreducible] waveAverage referenceAverage

variable (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hκ : ∀ q, AEStronglyMeasurable (κ q) volume)
  (M : ℝ) (hκbound : ∀ q, ∀ᵐ X ∂volume, ‖κ q X‖ ≤ M) (e : ℝ)
  (hSA : SelfAdjointGraph
    (freeHilbertGraph (fun _ => 0) C κ hκ M hκbound e))

include C κ hκ M hκbound e hSA

/-- Density of the actual fermionic form domain in the joint fermionic
Hilbert sector, expressed as equality of ambient L2 closures. -/
theorem closure_fermionicDomain :
    closure (fermionicDomain (N := N)) = {ψ : PauliReference.Wave N | JointFermionic ψ} := by
  apply closure_eq_of_projection (PauliReference.wave (N := N)) waveAverage
    (fermionicDomain (N := N)) {ψ : PauliReference.Wave N | JointFermionic ψ}
    (PauliFormDensity.wave_denseRange C κ hκ M hκbound e hSA)
    waveAverage_continuous jointFermionic_closed
  · rintro _ ⟨u, hu, rfl⟩
    exact (wave_fermionic_iff u).mpr hu
  · intro u
    exact ⟨referenceAverage u, referenceAverage_fermionic u, (waveAverage_wave u).symm⟩
  · intro ψ hψ
    exact waveAverage_eq_self ψ hψ

/-- The paper's H1 and radiation form domain is dense after imposing
joint position and spin antisymmetry. -/
theorem closure_electronicRadiation_fermionic :
    closure {ψ : PauliReference.Wave N |
      PauliCommonFormDomain.ElectronicRadiationDomain ψ ∧ JointFermionic ψ} =
      {ψ : PauliReference.Wave N | JointFermionic ψ} := by
  have h : {ψ : PauliReference.Wave N |
      PauliCommonFormDomain.ElectronicRadiationDomain ψ ∧ JointFermionic ψ} =
      fermionicDomain (N := N) := by
    ext ψ
    exact (fermionicDomain_iff ψ).symm
  exact (congrArg (closure : Set (PauliReference.Wave N) → Set (PauliReference.Wave N)) h).trans
    (closure_fermionicDomain C κ hκ M hκbound e hSA)

end PfHk.PauliFermionicFormDensity

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
