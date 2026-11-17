import PfHk.PauliWeakGaugeState
import PfHk.PauliPairCovariance
import PfHk.PauliExternalEnergyPairing
import PfHk.PauliCurrentGroundState

/-! Weak phases act on the actual spin-summed density and Pauli current
by preserving the density and adding its product with the weak gradient. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliWeakGauge

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.SymmetricLift GptLean.TransformationsGauge GptLean.PhysicalPairSpace
  GptLean.PhysicalPolarization PfHk.PauliGroundState PfHk.CenteredPhysicalReference

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 60000

private theorem weighted_sum_eq {S : Type*} [Fintype S]
    (f : S → ℝ) (r w : ℝ) (h : w = ∑ s, f s) :
    (∑ s, r * f s) = r * w :=
  (Finset.mul_sum _ _ _).symm.trans (congrArg (fun t : ℝ => r * t) h.symm)

variable {N : ℕ}
attribute [local irreducible] referenceSubspace inclusion PauliCurrent.wave
  PauliCurrent.pauliVelocity PauliReference.wave covariant PauliGroundState.data
  ElectronicH1Complex.complexWeakGraph ElectronicH1Complex.value ElectronicH1Complex.derivative

def components (u : PauliGroundState.Ref N) : PauliCurrent.Components (N := N) :=
  fun s => electronic (Fin N × Fin 3) (fun _ => 0) (u s)

theorem components_wave (u : PauliGroundState.Ref N) :
    PauliCurrent.wave (N := N) (components u) = PauliReference.wave u := by
  unfold PauliCurrent.wave PauliReference.wave components inclusion
  rfl

theorem components_value (u : PauliGroundState.Ref N) (s : PauliSpin.SpinIndex N) :
    ElectronicH1Complex.value (components u s) = inclusion (Fin N × Fin 3) (fun _ => 0) (u s) := by
  unfold components inclusion
  rfl

theorem components_norm_sq_ae (u : PauliGroundState.Ref N) :
    (fun X => ‖PauliCurrent.wave (N := N) (components u) X‖ ^ 2) =ᵐ[volume]
      fun X => ∑ s, ‖inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X‖ ^ 2 := by
  unfold PauliCurrent.wave
  simp only [components_value]
  exact FiniteFiberL2.norm_sq_ae _

theorem gradient_density_integrable (G : WeakSpatialGauge) (u : PauliGroundState.Ref N)
    (n : Fin N) (a : Fin 3) :
    Integrable (fun X => G.gradient a (particle X n) *
      ‖PauliCurrent.wave (N := N) (components u) X‖ ^ 2) volume := by
  have hi := integrable_finsetSum Finset.univ (fun s _ =>
    G.gradient_density_configuration_integrable (fun _ => 0) (n,a) (u s))
  apply hi.congr
  filter_upwards [components_norm_sq_ae u] with X hX
  exact weighted_sum_eq
    (fun s : PauliSpin.SpinIndex N => ‖inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X‖ ^ 2)
    (G.gradient a (particle X n)) _ hX

variable (C : CanonicalSectorCCR photonMeasure) (e : ℝ) (F : Frame) (χ : ArticleCutoff)

theorem bundled_current_gauge (G : WeakSpatialGauge) (u : PauliGroundState.Ref N)
    (n : Fin N) (a : Fin 3) :
    (fun X => (inner ℂ (E := PauliSpin.Fiber N PhotonFock) (PauliCurrent.wave (N := N) (components (gauge G u)) X)
      (PauliCurrent.pauliVelocity (N := N) (covariants C e F χ (gauge G u)) n a X)).re) =ᵐ[volume]
      fun X => (inner ℂ (E := PauliSpin.Fiber N PhotonFock) (PauliCurrent.wave (N := N) (components u) X)
        (PauliCurrent.pauliVelocity (N := N) (covariants C e F χ u) n a X)).re +
        G.gradient a (particle X n) * ‖PauliCurrent.wave (N := N) (components u) X‖ ^ 2 := by
  filter_upwards [PauliExternalEnergy.current_ae (N := N) n (components (gauge G u))
      (covariants C e F χ (gauge G u)) a,
    PauliExternalEnergy.current_ae (N := N) n (components u) (covariants C e F χ u) a,
    current_gauge_ae C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e G n u a,
    components_norm_sq_ae u] with X h₁ h₂ h₃ hρ
  simp only [components_value] at h₁ h₂
  exact h₁.trans (h₃.trans (congrArg₂ (· + ·) h₂.symm
    (congrArg (fun r : ℝ => G.gradient a (particle X n) * r) hρ.symm)))

theorem data_density_gauge (G : WeakSpatialGauge) (u : PauliGroundState.Ref N) :
    densityL1 (data C e F χ (gauge G u)) = densityL1 (data C e F χ u) := by
  have hρ : (fun X => ‖PauliCurrent.wave (N := N) (components (gauge G u)) X‖ ^ 2) =ᵐ[volume]
      fun X => ‖PauliCurrent.wave (N := N) (components u) X‖ ^ 2 := by
    rw [components_wave, components_wave]
    exact (wave_norm_gauge_ae G u).mono (fun _ hx => congrArg (fun r : ℝ => r ^ 2) hx)
  unfold PauliGroundState.data
  exact PauliPairCovariance.pair_density_eq (N := N) (components u) (components (gauge G u))
    (covariants C e F χ u) (covariants C e F χ (gauge G u)) hρ

theorem data_current_gauge (G : WeakSpatialGauge) (u : PauliGroundState.Ref N) (a : Fin 3) :
    (fun x => currentL1 (data C e F χ (gauge G u)) x a) =ᵐ[volume]
      fun x => currentL1 (data C e F χ u) x a + G.gradient a x * densityL1 (data C e F χ u) x := by
  unfold PauliGroundState.data
  exact PauliPairCovariance.pair_current_shift (N := N) (components u) (components (gauge G u))
    (covariants C e F χ u) (covariants C e F χ (gauge G u)) a (G.gradient a)
    (fun n => bundled_current_gauge C e F χ G u n a)
    (fun n => gradient_density_integrable G u n a)

theorem data_gauge (G : WeakSpatialGauge) (u : PauliGroundState.Ref N) :
    data C e F χ (gauge G u) = G.shiftPair (data C e F χ u) := by
  apply pair_ext_ae
  · rw [G.densityL1_shiftPair, data_density_gauge]
  · filter_upwards [ae_all_iff.mpr (fun a => data_current_gauge C e F χ G u a),
      G.currentL1_shiftPair (data C e F χ u)] with x h₁ h₂
    have he : currentL1 (data C e F χ (gauge G u)) x =
        currentL1 (data C e F χ u) x + densityL1 (data C e F χ u) x • G.gradientVector x := by
      apply PiLp.ext
      intro a
      simpa only [PiLp.add_apply, PiLp.smul_apply, G.gradientVector_apply, smul_eq_mul, mul_comm]
        using h₁ a
    exact he.trans h₂.symm

theorem data_gaugeState (G : WeakSpatialGauge) (p : State N) :
    data C e F χ (gaugeState G p).vector = G.shiftPair (data C e F χ p.vector) :=
  data_gauge C e F χ G p.vector

end PfHk.PauliWeakGauge

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
