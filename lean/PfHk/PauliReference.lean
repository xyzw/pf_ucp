import PfHk.FiniteFiberH1
import PfHk.PauliSpin
import PfHk.NonvanishingDensity
import GptLean.PhysicalPFReference
import GptLean.PhysicalFockSeparable

/-! The common spinful reference space is a finite family of actual
orbital form vectors. Its wave function has the electron spin--photon
Hilbert fiber, not an additional scalar or an abstract state model. -/

noncomputable section
namespace PfHk.PauliReference

open MeasureTheory GptLean GptLean.PhysicalFock PauliSpin

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000

local instance spinScalarTower (N : ℕ) : IsScalarTower ℝ ℂ (Fiber N PhotonFock) where
  smul_assoc r c u := by
    apply PiLp.ext
    intro s
    exact smul_assoc r c (u s)

abbrev Ref (N : ℕ) := SpinIndex N → PhysicalPFReference.Reference (Fin N × Fin 3) (fun _ => 0)
abbrev Wave (N : ℕ) := PhysicalElectronicDensity.Wave (N := N) (H := Fiber N PhotonFock)

def wave {N : ℕ} (u : Ref N) : Wave N :=
  FiniteFiberL2.bundle (fun s => PhysicalPFReference.inclusion (Fin N × Fin 3) (fun _ => 0) (u s))

def electronic {N : ℕ} (u : Ref N) :
    ElectronicH1Complex.ComplexH1 (Fiber N PhotonFock) (Fin N × Fin 3) :=
  FiniteFiberH1.bundle (fun s => PhysicalPFReference.electronic (Fin N × Fin 3) (fun _ => 0) (u s))

theorem electronic_value {N : ℕ} (u : Ref N) :
    ElectronicH1Complex.value (electronic u) = wave u :=
  FiniteFiberH1.value_bundle _

theorem electronic_derivative {N : ℕ} (u : Ref N) (i : Fin N × Fin 3) :
    ElectronicH1Complex.derivative i (electronic u) = FiniteFiberL2.bundle
      (fun s => PhysicalPFReference.ordinary (Fin N × Fin 3) (fun _ => 0) i (u s)) :=
  FiniteFiberH1.derivative_bundle _ i

theorem wave_ae {N : ℕ} (u : Ref N) :
    (wave u : GptLean.SymmetricLift.Configuration N → Fiber N PhotonFock) =ᵐ[volume]
      fun X => WithLp.toLp 2
        (fun s => PhysicalPFReference.inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X) :=
  FiniteFiberL2.bundle_ae _

theorem wave_norm_sq {N : ℕ} (u : Ref N) :
    ‖wave u‖ ^ 2 = ∑ s, ‖PhysicalPFReference.inclusion (Fin N × Fin 3) (fun _ => 0) (u s)‖ ^ 2 :=
  FiniteFiberL2.norm_sq _

theorem wave_norm_sq_ae {N : ℕ} (u : Ref N) :
    (fun X => ‖wave u X‖ ^ 2) =ᵐ[volume]
      fun X => ∑ s, ‖PhysicalPFReference.inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X‖ ^ 2 :=
  FiniteFiberL2.norm_sq_ae _

theorem wave_injective {N : ℕ} : Function.Injective (wave (N := N)) := by
  intro u v huv
  have h := FiniteFiberL2.bundle_injective huv
  funext s
  exact PhysicalPFReference.inclusion_injective (Fin N × Fin 3) (fun _ => 0) (congrFun h s)

theorem wave_zero {N : ℕ} : wave (0 : Ref N) = 0 := by
  unfold wave
  simp only [Pi.zero_apply, map_zero]
  exact FiniteFiberL2.bundle_zero

theorem wave_ne_zero {N : ℕ} {u : Ref N} (hu : u ≠ 0) : wave u ≠ 0 := by
  intro h
  exact hu (wave_injective (h.trans wave_zero.symm))

/-- The physical density sums the electronic marginals of the full
spin--photon norm, hence includes all spin components. -/
def density {N : ℕ} (u : Ref N) := PhysicalElectronicDensity.density (wave u)

theorem density_nonneg {N : ℕ} (u : Ref N) : ∀ᵐ x ∂volume, 0 ≤ density u x :=
  PhysicalElectronicDensity.density_nonneg _

theorem density_pos_ae {N : ℕ} (hN : 0 < N) (u : Ref N)
    (hu : ∀ᵐ X ∂volume, wave u X ≠ 0) : ∀ᵐ x ∂volume, 0 < density u x :=
  NonvanishingDensity.density_pos_ae ⟨0, hN⟩ (wave u) hu

end PfHk.PauliReference
