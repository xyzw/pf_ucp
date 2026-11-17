import PfHk.PhysicalOneParticleState

/-! Vanishing radiation energy puts an actual reference vector in the
photon vacuum. A fixed nonzero electronic factor then leaves only one
global complex phase. -/

noncomputable section

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PhysicalReferenceVacuum

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  PfHk.PhysicalOneParticleState

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000

attribute [local irreducible] inclusion radiation PhysicalPFReference.referenceSubspace

/-- Zero radiation coordinate forces a vacuum vector in almost every
electronic fiber, using the actual radiation-root graph. -/
theorem ae_vacuum_of_radiation_zero (BF : StandardSymmetricFockExponential)
    (u : Ref) (hu : radiation Index (fun _ => 0) u = 0) :
    ∀ᵐ X ∂volume, ∃ z : ℂ,
      PhysicalFullVacuum.fiberInsertion z = inclusion Index (fun _ => 0) u X := by
  have hz : ∀ᵐ X ∂volume, radiation Index (fun _ => 0) u X = 0 := by
    filter_upwards [Lp.coeFn_zero PhotonFock 2 (volume : Measure (Position Index))]
      with X hX
    exact (congrArg (fun w : WaveSpace Index => w X) hu).trans hX
  filter_upwards [radiation_graph Index (fun _ => 0) u, hz] with X hgraph hzero
  have henergy := radiationGraph_energy
    (⟨(inclusion Index (fun _ => 0) u X, radiation Index (fun _ => 0) u X), hgraph⟩ :
      RadiationGraphSpace)
  have hform : radiationForm (inclusion Index (fun _ => 0) u X) = 0 := by
    change radiationForm (inclusion Index (fun _ => 0) u X) =
      ENNReal.ofReal (‖radiation Index (fun _ => 0) u X‖ ^ 2) at henergy
    simpa only [hzero, norm_zero, zero_pow (by decide : 2 ≠ 0), ENNReal.ofReal_zero]
      using henergy
  exact (PhysicalFullVacuum.radiation_zero_iff_scalar BF _).mp hform

/-- Abstract scalar-fiber algebra, before specialization to the physical
Fock and reference-space instances. -/
private theorem phase_of_scalar_fibers {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [(ae μ).NeBot]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (ψ ψ₀ : Lp H 2 μ) (Ω : H) (φ : X → ℝ)
    (hφ : ∀ x, φ x ≠ 0)
    (hψ₀ : ψ₀ =ᵐ[μ] fun x => (φ x : ℂ) • Ω)
    (hu : ‖ψ‖ = 1) (h₀ : ‖ψ₀‖ = 1)
    (v : H) (hv : ψ =ᵐ[μ] fun x => (φ x : ℂ) • v)
    (hvac : ∀ᵐ x ∂μ, ∃ z : ℂ, z • Ω = ψ x) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ψ = c • ψ₀ := by
  obtain ⟨x, ⟨z, hz⟩, hx⟩ := (hvac.and hv).exists
  have hφx : (φ x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hφ x)
  let c : ℂ := (φ x : ℂ)⁻¹ * z
  have hvc : v = c • Ω := by
    calc
      v = (φ x : ℂ)⁻¹ • ((φ x : ℂ) • v) := (inv_smul_smul₀ hφx v).symm
      _ = (φ x : ℂ)⁻¹ • (z • Ω) :=
        congrArg (fun w : H => (φ x : ℂ)⁻¹ • w) (hz.trans hx).symm
      _ = c • Ω := smul_smul _ _ _
  have heq : ψ = c • ψ₀ := by
    apply Lp.ext
    filter_upwards [hv, hψ₀, Lp.coeFn_smul c ψ₀] with y hy hzero hs
    rw [hy, hvc, hs, Pi.smul_apply, hzero]
    exact smul_comm _ _ _
  refine ⟨c, ?_, heq⟩
  have hn : ‖c • ψ₀‖ = ‖c‖ :=
    (norm_smul c ψ₀).trans ((congrArg (fun r : ℝ => ‖c‖ * r) h₀).trans (mul_one _))
  exact (hu.symm.trans ((congrArg norm heq).trans hn)).symm

/-- An electronic ground-space factor and zero radiation energy determine
the normalized physical wave function up to a single constant phase. -/
theorem phase_of_electronic_factor (BF : StandardSymmetricFockExponential)
    (u : Ref) (ψ₀ : WaveSpace Index) (φ : Position Index → ℝ)
    (hφ : ∀ X, φ X ≠ 0)
    (hψ₀ : ψ₀ =ᵐ[volume] fun X => (φ X : ℂ) • PhysicalFullVacuum.vacuum)
    (hu : ‖inclusion Index (fun _ => 0) u‖ = 1) (h₀ : ‖ψ₀‖ = 1)
    (hr : radiation Index (fun _ => 0) u = 0)
    (v : PhotonFock)
    (hv : inclusion Index (fun _ => 0) u =ᵐ[volume] fun X => (φ X : ℂ) • v) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ inclusion Index (fun _ => 0) u = c • ψ₀ := by
  exact phase_of_scalar_fibers volume (inclusion Index (fun _ => 0) u) ψ₀
    PhysicalFullVacuum.vacuum φ hφ hψ₀ hu h₀ v hv
    (ae_vacuum_of_radiation_zero BF u hr)

end PfHk.PhysicalReferenceVacuum

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
