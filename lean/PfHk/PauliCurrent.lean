import PfHk.PauliCurrentAverage
import PfHk.PauliCurrentAlgebra
import PfHk.FiniteFiberH1
import GptLean.PhysicalPFReference
import GptLean.PhysicalSourceTests
import GptLean.PhysicalElectronicDensity
import GptLean.PhysicalFockSeparable

/-! The finite-spin Pauli density and current in their actual Lebesgue
intersection spaces. The three current velocities are obtained from the
Pauli contraction of L2 covariant derivatives. Their integrability follows
from the proved Hilbert-valued H1 marginal construction. -/

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

noncomputable section
namespace PfHk.PauliCurrent

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPairSpace GptLean.PhysicalSourceCoordinates
  GptLean.PhysicalSourcePair PfHk.PauliSpin PfHk.PauliCurrentAlgebra
open scoped ENNReal

set_option Elab.async false
set_option maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency.types true

local instance spinScalarTower (N : ℕ) : IsScalarTower ℝ ℂ (Fiber N PhotonFock) where
  smul_assoc r c u := by
    apply PiLp.ext
    intro s
    exact smul_assoc r c (u s)

variable {N : ℕ}

attribute [local irreducible] ElectronicH1Complex.value

abbrev Electronic := ElectronicH1Complex.ComplexH1 PhotonFock (Fin N × Fin 3)
abbrev Components := SpinIndex N → Electronic (N := N)
abbrev Wave := Lp (Fiber N PhotonFock) 2 (volume : Measure (GptLean.SymmetricLift.Configuration N))
abbrev Derivatives := (Fin N × Fin 3) → SpinIndex N → WaveSpace (Fin N × Fin 3)

def wave (u : Components (N := N)) :
    Lp (Fiber N PhotonFock) 2 (volume : Measure (GptLean.SymmetricLift.Configuration N)) :=
  FiniteFiberL2.bundle (S := SpinIndex N) (H := PhotonFock)
    (X := GptLean.SymmetricLift.Configuration N) (μ := volume) (fun s => ElectronicH1Complex.value (E := PhotonFock) (I := Fin N × Fin 3) (u s))

def pauliVelocity (d : Derivatives (N := N)) (i : Fin N) (a : Fin 3) :
    Lp (Fiber N PhotonFock) 2 (volume : Measure (GptLean.SymmetricLift.Configuration N)) :=
  FiniteFiberL2.bundle (velocity i a (fun b => d (i, b)))

def source (u : Components (N := N)) :
    ElectronicH1Space.H1 (Fiber N PhotonFock) (Fin N × Fin 3) :=
  ElectronicH1Complex.realEquiv (E := Fiber N PhotonFock) (I := Fin N × Fin 3)
    (FiniteFiberH1.bundle (S := SpinIndex N) (H := PhotonFock) (I := Fin N × Fin 3) u)

theorem source_value (u : Components (N := N)) :
    ElectronicH1Space.value (E := Fiber N PhotonFock) (I := Fin N × Fin 3) (source (N := N) u) = wave (N := N) u :=
  (ElectronicH1Complex.value_realEquiv (E := Fiber N PhotonFock) (I := Fin N × Fin 3)
    (FiniteFiberH1.bundle (S := SpinIndex N) (H := PhotonFock) (I := Fin N × Fin 3) u)).trans
      (FiniteFiberH1.value_bundle (S := SpinIndex N) (H := PhotonFock) (I := Fin N × Fin 3) u)

theorem wave_norm_sq (u : Components (N := N)) :
    ‖wave (N := N) u‖ ^ 2 = ∑ s, ‖ElectronicH1Complex.value (E := PhotonFock) (I := Fin N × Fin 3) (u s)‖ ^ 2 :=
  FiniteFiberL2.norm_sq _

/-- The current and density at one selected electron, including all spins. -/
def particlePair (i : Fin N) (u : Components (N := N)) (d : Derivatives (N := N)) : Pair :=
  ofWaveFunction i (source (N := N) u) (fun a => pauliVelocity (N := N) d i a)

theorem particlePair_def (i : Fin N) (u : Components (N := N)) (d : Derivatives (N := N)) :
    particlePair (N := N) i u d = ofWaveFunction i (source (N := N) u) (fun a => pauliVelocity (N := N) d i a) := rfl

/-- Sum all electron marginals. This also applies before antisymmetrization. -/
def pair (u : Components (N := N)) (d : Derivatives (N := N)) : Pair :=
  (N : ℝ)⁻¹ • ∑ i : Fin N, particlePair (N := N) i u d

theorem pair_def (u : Components (N := N)) (d : Derivatives (N := N)) :
    pair (N := N) u d = (N : ℝ)⁻¹ • ∑ i : Fin N, particlePair (N := N) i u d := rfl

attribute [local irreducible] wave pauliVelocity source particlePair pair
  ofWaveFunction densityL1 currentL1 PhysicalElectronicDensity.density

theorem particle_density_ae (i : Fin N) (u : Components (N := N))
    (d : Derivatives (N := N)) :
    (densityL1 (particlePair (N := N) i u d) : PhysicalPairSpace.Position → ℝ) =ᵐ[volume]
      fun x => (N : ℝ) * ∫ y, ‖wave (N := N) u ((split i).symm (x, y))‖ ^ 2 := by
  have hl := congrArg (fun P : Pair => (densityL1 P : PhysicalPairSpace.Position → ℝ))
    (particlePair_def (N := N) i u d)
  have hr := congrArg (fun w : Wave (N := N) => fun x : PhysicalPairSpace.Position =>
    (N : ℝ) * ∫ y, ‖w ((split i).symm (x, y))‖ ^ 2) (source_value (N := N) u)
  exact Filter.EventuallyEq.trans (Filter.Eventually.of_forall (fun x => congrFun hl x))
    ((density_ofWaveFunction_ae (N := N) (H := Fiber N PhotonFock) i (source (N := N) u)
      (fun a => pauliVelocity (N := N) d i a)).trans
        (Filter.Eventually.of_forall (fun x => congrFun hr x)))

theorem particle_current_ae (i : Fin N) (u : Components (N := N))
    (d : Derivatives (N := N)) (a : Fin 3) :
    (fun x => currentL1 (particlePair (N := N) i u d) x a) =ᵐ[volume]
      fun x => (N : ℝ) * (∫ y,
        inner ℂ (wave (N := N) u ((split i).symm (x, y)))
          (pauliVelocity (N := N) d i a ((split i).symm (x, y)))).re := by
  have hl := congrArg (fun P : Pair => fun x : PhysicalPairSpace.Position => currentL1 P x a)
    (particlePair_def (N := N) i u d)
  have hr := congrArg (fun w : Wave (N := N) => fun x : PhysicalPairSpace.Position =>
    (N : ℝ) * (∫ y, inner ℂ (w ((split i).symm (x, y)))
      (pauliVelocity (N := N) d i a ((split i).symm (x, y)))).re) (source_value (N := N) u)
  exact Filter.EventuallyEq.trans (Filter.Eventually.of_forall (fun x => congrFun hl x))
    ((current_ofWaveFunction_ae (N := N) (H := Fiber N PhotonFock) i (source (N := N) u)
      (fun b => pauliVelocity (N := N) d i b) a).trans
        (Filter.Eventually.of_forall (fun x => congrFun hr x)))

theorem particle_density_integral (i : Fin N) (u : Components (N := N))
    (d : Derivatives (N := N)) :
    (∫ x, densityL1 (particlePair (N := N) i u d) x) =
      (N : ℝ) * ∑ s, ‖ElectronicH1Complex.value (E := PhotonFock) (I := Fin N × Fin 3) (u s)‖ ^ 2 := by
  have hl := congrArg (fun P : Pair => ∫ x, densityL1 P x) (particlePair_def (N := N) i u d)
  have hr := (congrArg (fun w : Wave (N := N) => ‖w‖ ^ 2) (source_value (N := N) u)).trans
    (wave_norm_sq (N := N) u)
  exact hl.trans ((integral_density_ofWaveFunction (N := N) (H := Fiber N PhotonFock) i
    (source (N := N) u) (fun a => pauliVelocity (N := N) d i a)).trans
      (congrArg (fun r : ℝ => (N : ℝ) * r) hr))

theorem tested_particle_current (i : Fin N) (u : Components (N := N))
    (d : Derivatives (N := N)) (a : Fin 3)
    (f : PhysicalPairSpace.Position → ℝ) (hf : AEStronglyMeasurable f volume)
    {c : ℝ} (hc : ∀ᵐ x ∂volume, ‖f x‖ ≤ c) :
    (∫ x, f x * currentL1 (particlePair (N := N) i u d) x a) =
      (N : ℝ) * ∫ X, f ((split i) X).1 *
        (inner ℂ (wave (N := N) u X) (pauliVelocity (N := N) d i a X)).re := by
  have hl := congrArg (fun P : Pair => ∫ x, f x * currentL1 P x a)
    (particlePair_def (N := N) i u d)
  have hr := congrArg (fun w : Wave (N := N) => (N : ℝ) * ∫ X,
    f ((split i) X).1 * (inner ℂ (w X) (pauliVelocity (N := N) d i a X)).re)
    (source_value (N := N) u)
  exact hl.trans ((tested_current_ofWaveFunction (N := N) (H := Fiber N PhotonFock) i
    (source (N := N) u) (fun b => pauliVelocity (N := N) d i b) a f hf hc).trans hr)

/-- The density component is the actual sum of all spinor marginals. -/
theorem density_eq (hN : 0 < N) (u : Components (N := N))
    (d : Derivatives (N := N)) :
    densityL1 (pair (N := N) u d) =
      PhysicalElectronicDensity.density (N := N) (H := Fiber N PhotonFock) (wave (N := N) u) := by
  have hp (i : Fin N) :
      (densityL1 (particlePair (N := N) i u d) : PhysicalPairSpace.Position → ℝ) =ᵐ[volume]
        fun x => (N : ℝ) * ‖PhysicalSourceMarginal.particleMap i (wave (N := N) u) x‖ ^ 2 :=
    (particle_density_ae (N := N) i u d).trans
      ((particleMap_norm_sq_ae (N := N) (H := Fiber N PhotonFock) i (wave (N := N) u)).mono
        (fun x hx => congrArg (fun r : ℝ => (N : ℝ) * r) hx.symm))
  exact (congrArg densityL1 (pair_def (N := N) u d)).trans
    (PauliCurrentAverage.density_of_ae hN (fun i => particlePair (N := N) i u d)
      (PhysicalElectronicDensity.density (N := N) (H := Fiber N PhotonFock) (wave (N := N) u))
      (fun i x => ‖PhysicalSourceMarginal.particleMap i (wave (N := N) u) x‖ ^ 2) hp
      (PhysicalElectronicDensity.density_ae (N := N) (H := Fiber N PhotonFock) (wave (N := N) u)))

end PfHk.PauliCurrent

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
