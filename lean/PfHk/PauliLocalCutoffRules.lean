import PfHk.PauliFlatCutoff
import PfHk.PauliOrbitalCutoffLocality

/-! Form identities used to localize a Pauli weak equation. All
derivative terms are the existing physical orbital commutator. -/

noncomputable section
namespace PfHk.PauliLocalCutoffRules

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.ElectronicH1Multiplier PfHk.PauliSpin PfHk.PauliGroundState
  PfHk.PauliLocalEnergy PfHk.PhysicalLocalEnergy PfHk.PhysicalCutoffCommutator
  PfHk.SmoothCutoffBounds
open scoped InnerProductSpace

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 40000

theorem magnetic_cancel {Q₁ Q₂ O₁ O₂ B₁ B₂ F₁ F₂ T : ℂ}
    (h₁ : Q₁ = O₁ + B₁ + F₁) (h₂ : Q₂ = O₂ + B₂ + F₂)
    (hB : B₁ = B₂) (hF : F₁ = F₂) (hO : O₁ = O₂ + T) : Q₁ = Q₂ + T := by
  rw [h₁, h₂, hB, hF, hO]
  ring

theorem eigen_source_pairing {J H : Type*} [Fintype J]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (E : ℂ) (z u f : J → H) :
    (∑ s, inner ℂ (z s) (E • u s + f s)) =
      E * (∑ s, inner ℂ (z s) (u s)) + ∑ s, inner ℂ (z s) (f s) := by
  simp only [inner_add_right, inner_smul_right, Finset.sum_add_distrib, Finset.mul_sum]

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed GptLean.SymmetricLift.TensorHilbert.inner
attribute [local irreducible] referenceSubspace inclusion radiation roughMultiply
  externalCovariant externalForm rawForm PauliOrbitalForm.form
  PhysicalPFScalarMultiplier.multiply DifferentiableMultiplier.multiplier
  DifferentiableMultiplier.derivativeMultiplier PauliLocalEnergy.localize

variable {N : ℕ}

theorem localized_supported_radius {O : Position (Fin N × Fin 3)}
    (family : BufferedFamily O) {r R : ℝ} (hr : 0 < r) (hR : 2 * r ≤ R)
    (u : Ref N) (s : SpinIndex N) :
    ∀ᵐ X ∂volume, X ∉ Metric.ball O R →
      inclusion (Fin N × Fin 3) (fun _ => 0) (localize (family.cutoff r).scalar u s) X = 0 := by
  unfold localize
  exact (localized_supported (fun _ => 0) (family.cutoff r).scalar
    (BufferedCutoffLocality.cutoff_supported family hr) (u s)).mono fun X hX hnot =>
      hX (fun hx => hnot (Metric.mem_ball.mpr ((Metric.mem_ball.mp hx).trans_le hR)))

theorem mass_cutoff_pairing (a : DifferentiableMultiplier (Fin N × Fin 3)) (z u : Ref N) :
    mass (N := N) (localize a z) u = mass (N := N) z (localize a u) := by
  unfold mass localize
  exact Finset.sum_congr rfl fun s _ =>
    (scalar_multiplier_pair (H := PhotonFock) a _ _ _ _
      (PhysicalPFScalarMultiplier.value_multiply (fun _ => 0) a (z s))
      (PhysicalPFScalarMultiplier.value_multiply (fun _ => 0) a (u s))).symm

variable (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hκ : ∀ q, AEStronglyMeasurable (κ q) volume)
  (M : ℝ) (hκbound : ∀ q, ∀ᵐ X ∂volume, ‖κ q X‖ ≤ M) (e : ℝ)
  (A : (Fin N × Fin 3) → Position (Fin N × Fin 3) → ℝ)
  (positive negative : Position (Fin N × Fin 3) → ℝ)

theorem raw_hermitian (z u : Ref N) (hz : Domain A positive negative z)
    (hu : Domain A positive negative u) :
    star (rawForm C κ hκ M hκbound e A positive negative z u hz hu) =
      rawForm C κ hκ M hκbound e A positive negative u z hu hz := by
  change starRingEnd ℂ (rawForm C κ hκ M hκbound e A positive negative z u hz hu) = _
  simp only [rawForm, map_sub, map_add, map_mul, map_sum, inner_conj_symm,
    map_div₀, map_one, map_ofNat]

theorem orbital_hermitian (z u : Ref N) (hz : Domain A positive negative z)
    (hu : Domain A positive negative u) :
    star (PauliOrbitalForm.form C κ hκ M hκbound e A positive negative z u hz hu) =
      PauliOrbitalForm.form C κ hκ M hκbound e A positive negative u z hu hz := by
  change starRingEnd ℂ (PauliOrbitalForm.form C κ hκ M hκbound e A positive negative z u hz hu) = _
  simp only [PauliOrbitalForm.form, externalForm, map_sub, map_add, map_mul, map_sum,
    inner_conj_symm, map_div₀, map_one, map_ofNat]

theorem rawForm_localize_right (a : TwiceDifferentiableMultiplier (Fin N × Fin 3))
    (z u : Ref N) (hz : Domain A positive negative z) (hu : Domain A positive negative u)
    (hfix : ∀ s, a.scalar.multiplier (inclusion (Fin N × Fin 3) (fun _ => 0) (z s)) =
      inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
    (hfirst : ∀ i s, (a.derivative i).multiplier
      (inclusion (Fin N × Fin 3) (fun _ => 0) (z s)) = 0)
    (hsecond : ∀ i j s, (a.derivative i).derivativeMultiplier j
      (inclusion (Fin N × Fin 3) (fun _ => 0) (z s)) = 0) :
    rawForm C κ hκ M hκbound e A positive negative z (localize a.scalar u)
      hz (domain_localize hu a.scalar) = rawForm C κ hκ M hκbound e A positive negative z u hz hu := by
  have h := congrArg (star : ℂ → ℂ)
    (PauliFlatCutoff.rawForm_localize_left C κ hκ M hκbound e A positive negative
      a u z hu hz hfix hfirst hsecond)
  exact (raw_hermitian C κ hκ M hκbound e A positive negative
    (localize a.scalar u) z (domain_localize hu a.scalar) hz).symm.trans
    (h.trans (raw_hermitian C κ hκ M hκbound e A positive negative u z hu hz))

theorem orbitalForm_localize_right (a : TwiceDifferentiableMultiplier (Fin N × Fin 3))
    (z u : Ref N) (hz : Domain A positive negative z) (hu : Domain A positive negative u)
    (hfix : ∀ s, a.scalar.multiplier (inclusion (Fin N × Fin 3) (fun _ => 0) (z s)) =
      inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
    (hfirst : ∀ i s, (a.derivative i).multiplier
      (inclusion (Fin N × Fin 3) (fun _ => 0) (z s)) = 0)
    (hsecond : ∀ i s, (a.derivative i).derivativeMultiplier i
      (inclusion (Fin N × Fin 3) (fun _ => 0) (z s)) = 0) :
    PauliOrbitalForm.form C κ hκ M hκbound e A positive negative z (localize a.scalar u)
      hz (domain_localize hu a.scalar) =
      PauliOrbitalForm.form C κ hκ M hκbound e A positive negative z u hz hu := by
  have h := congrArg (star : ℂ → ℂ)
    (PauliOrbitalCutoffLocality.form_localize_left C κ hκ M hκbound e A positive negative
      a u z hu hz hfix hfirst hsecond)
  exact (orbital_hermitian C κ hκ M hκbound e A positive negative
    (localize a.scalar u) z (domain_localize hu a.scalar) hz).symm.trans
    (h.trans (orbital_hermitian C κ hκ M hκbound e A positive negative u z hu hz))

def commutator (a : TwiceDifferentiableMultiplier (Fin N × Fin 3))
    (u : Ref N) (hu : Domain A positive negative u) : SpinIndex N → WaveSpace (Fin N × Fin 3) :=
  fun s => PhysicalCutoffCommutator.commutator (fun _ => 0) C κ hκ M hκbound e
    A positive negative a (u s) (hu s)

theorem orbital_form_commutator (a : TwiceDifferentiableMultiplier (Fin N × Fin 3))
    (z u : Ref N) (hz : Domain A positive negative z) (hu : Domain A positive negative u) :
    PauliOrbitalForm.form C κ hκ M hκbound e A positive negative z (localize a.scalar u)
      hz (domain_localize hu a.scalar) =
    PauliOrbitalForm.form C κ hκ M hκbound e A positive negative (localize a.scalar z) u
      (domain_localize hz a.scalar) hu +
      ∑ s, inner ℂ (inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
        (commutator C κ hκ M hκbound e A positive negative a u hu s) := by
  unfold PauliOrbitalForm.form localize commutator
  exact (Finset.sum_congr rfl fun s _ =>
    PhysicalCutoffCommutator.form_commutator (fun _ => 0) C κ hκ M hκbound e
      A positive negative a (u s) (z s) (hu s) (hz s)).trans Finset.sum_add_distrib

end PfHk.PauliLocalCutoffRules
attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed GptLean.SymmetricLift.TensorHilbert.inner
