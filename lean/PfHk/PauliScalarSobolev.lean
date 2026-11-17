import PfHk.PauliLocalEnergy
import PfHk.PauliFormBounds
import PfHk.PhysicalScalarSobolev
import PfHk.NormWeakH1Finite

/-! The norm of the actual spin--photon wave function has a genuine weak
H1 gradient. Scalar localization and Sobolev embedding retain the full
spin sum through the finite Hilbert fiber. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliInfiniteOrder

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.ElectronicH1Multiplier GptLean.SymmetricLift
  PfHk.PauliSpin PfHk.PauliReference PfHk.PauliLocalEnergy
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000

local instance spinScalarTower (N : ℕ) : IsScalarTower ℝ ℂ (Fiber N PhotonFock) where
  smul_assoc r c u := by
    apply PiLp.ext
    intro s
    exact smul_assoc r c (u s)

variable {N : ℕ}

attribute [local irreducible] referenceSubspace inclusion
  PauliReference.wave PauliReference.electronic ElectronicH1Complex.derivative
  ElectronicH1Complex.value ordinary PhysicalPFScalarMultiplier.multiply

private theorem memLp_normDerivative {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {μ : Measure X}
    (f d : Lp H 2 μ) :
    MemLp (fun x => (inner ℂ (f x) (d x)).re / ‖f x‖) 2 μ := by
  have hf := Lp.aestronglyMeasurable f
  have hd := Lp.aestronglyMeasurable d
  have hre : AEMeasurable (fun x => (inner ℂ (f x) (d x)).re) μ :=
    Complex.continuous_re.measurable.comp_aemeasurable
      (hf.inner (𝕜 := ℂ) hd).aemeasurable
  exact (Lp.memLp d).norm.mono'
    (hre.div hf.norm.aemeasurable).aestronglyMeasurable
    (ae_of_all _ fun x => PhysicalSourceCurrentBounds.norm_re_inner_div_norm_le (f x) (d x))

private theorem normDerivative_sq_le {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (f d : H) :
    ((inner ℂ f d).re / ‖f‖) ^ 2 ≤ ‖d‖ ^ 2 := by
  have h := PhysicalSourceCurrentBounds.norm_re_inner_div_norm_le f d
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  simpa only [Real.norm_eq_abs, sq_abs] using hs

private theorem normDerivative_weak {I H : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (f : Lp H 2 (volume : Measure (EuclideanSpace ℝ I)))
    (d : I → Lp H 2 (volume : Measure (EuclideanSpace ℝ I))) :
    let _ := InnerProductSpace.rclikeToReal ℂ H
    HasWeakH1Local (fun X => f X) (fun q X => d q X) →
      HasWeakH1Local (fun X => ‖f X‖)
        (fun q X => (inner ℂ (f X) (d q X)).re / ‖f X‖) := by
  dsimp only
  let := InnerProductSpace.rclikeToReal ℂ H
  intro hw
  exact NormWeakH1Finite.norm_weakH1Local (Lp.memLp f) (fun q => Lp.memLp (d q)) hw

private theorem normDerivative_weak_transfer {I H : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (f g : Lp H 2 (volume : Measure (EuclideanSpace ℝ I)))
    (d : I → Lp H 2 (volume : Measure (EuclideanSpace ℝ I))) (hfg : f = g) :
    let _ := InnerProductSpace.rclikeToReal ℂ H
    HasWeakH1Local (fun X => f X) (fun q X => d q X) →
      HasWeakH1Local (fun X => ‖g X‖)
        (fun q X => (inner ℂ (g X) (d q X)).re / ‖g X‖) := by
  dsimp only
  let := InnerProductSpace.rclikeToReal ℂ H
  intro hw
  subst g
  exact normDerivative_weak f d hw

private theorem integral_normDerivative_sq_le {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {μ : Measure X}
    (f d : Lp H 2 μ) :
    (∫ x, ((inner ℂ (f x) (d x)).re / ‖f x‖) ^ 2 ∂μ) ≤ ‖d‖ ^ 2 := by
  let := InnerProductSpace.rclikeToReal ℂ H
  have h := integral_mono_ae (memLp_normDerivative f d).integrable_sq
    (Lp.memLp d).norm.integrable_sq (ae_of_all _ fun x => normDerivative_sq_le (f x) (d x))
  exact h.trans_eq (PhotonKernelLocalization.l2_norm_sq_eq_integral d).symm

def normGradient (u : PauliReference.Ref N) (q : Fin N × Fin 3)
    (X : Configuration N) : ℝ :=
  (inner ℂ (PauliReference.wave u X)
    (ElectronicH1Complex.derivative q (PauliReference.electronic u) X)).re /
      ‖PauliReference.wave u X‖

def normGradientEnergy (u : PauliReference.Ref N) : ℝ :=
  ∑ q : Fin N × Fin 3, ∫ X, normGradient u q X ^ 2

theorem normGradient_memLp (u : PauliReference.Ref N) (q : Fin N × Fin 3) :
    MemLp (normGradient u q) 2 volume :=
  memLp_normDerivative (PauliReference.wave u)
    (ElectronicH1Complex.derivative q (PauliReference.electronic u))

theorem normGradient_weak (u : PauliReference.Ref N) :
    HasWeakH1Local (fun X => ‖PauliReference.wave u X‖) (normGradient u) :=
  normDerivative_weak_transfer (ElectronicH1Complex.value (PauliReference.electronic u))
    (PauliReference.wave u)
    (fun q => ElectronicH1Complex.derivative q (PauliReference.electronic u))
    (PauliReference.electronic_value u)
    (ElectronicH1Complex.weak (PauliReference.electronic u))

theorem normGradientEnergy_nonneg (u : PauliReference.Ref N) :
    0 ≤ normGradientEnergy u :=
  Finset.sum_nonneg fun q _ => integral_nonneg fun X => sq_nonneg (normGradient u q X)

theorem normGradientEnergy_le_ordinaryEnergy (u : PauliReference.Ref N) :
    normGradientEnergy u ≤ PauliFormBounds.ordinaryEnergy u := by
  apply Finset.sum_le_sum
  intro q _
  have hb := integral_normDerivative_sq_le (PauliReference.wave u)
    (ElectronicH1Complex.derivative q (PauliReference.electronic u))
  have hsum : ‖ElectronicH1Complex.derivative q (PauliReference.electronic u)‖ ^ 2 =
      ∑ s, ‖ordinary (Fin N × Fin 3) (fun _ => 0) q (u s)‖ ^ 2 :=
    (congrArg (fun z : PauliReference.Wave N => ‖z‖ ^ 2)
      (PauliReference.electronic_derivative u q)).trans (FiniteFiberL2.norm_sq _)
  exact hb.trans_eq hsum

theorem wave_localize_ae (a : DifferentiableMultiplier (Fin N × Fin 3))
    (u : PauliReference.Ref N) :
    (PauliReference.wave (PauliLocalEnergy.localize a u) :
      Configuration N → Fiber N PhotonFock) =ᵐ[volume]
        fun X => a.weight X • PauliReference.wave u X := by
  have hc (s : SpinIndex N) :
      (inclusion (Fin N × Fin 3) (fun _ => 0) (PauliLocalEnergy.localize a u s) :
        Configuration N → PhotonFock) =ᵐ[volume]
      fun X => a.weight X • inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X :=
    (Filter.EventuallyEq.of_eq (congrArg
      (fun z : WaveSpace (Fin N × Fin 3) => (z : Configuration N → PhotonFock))
      (PhysicalPFScalarMultiplier.value_multiply (fun _ => 0) a (u s)))).trans
        (PhysicalCutoffCommutator.scalar_multiplier_ae a _)
  filter_upwards [PauliReference.wave_ae (PauliLocalEnergy.localize a u),
    PauliReference.wave_ae u, ae_all_iff.mpr hc] with X h₁ h₂ h₃
  have hpoint : WithLp.toLp 2
      (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (PauliLocalEnergy.localize a u s) X) =
      a.weight X • WithLp.toLp 2
        (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X) := by
    apply PiLp.ext
    intro s
    exact h₃ s
  exact h₁.trans (hpoint.trans (congrArg (fun z : Fiber N PhotonFock => a.weight X • z) h₂.symm))

theorem wave_localize (a : DifferentiableMultiplier (Fin N × Fin 3))
    (u : PauliReference.Ref N) :
    PauliReference.wave (PauliLocalEnergy.localize a u) =
      a.multiplier (H := Fiber N PhotonFock) (PauliReference.wave u) := by
  apply Lp.ext
  exact (wave_localize_ae a u).trans
    (PhysicalCutoffCommutator.scalar_multiplier_ae a (PauliReference.wave u)).symm

theorem localized_norm_sq_ae (a : DifferentiableMultiplier (Fin N × Fin 3))
    (ha : ∀ X, 0 ≤ a.weight X) (u : PauliReference.Ref N) :
    (fun X => ‖PauliReference.wave (PauliLocalEnergy.localize a u) X‖ ^ 2) =ᵐ[volume]
      fun X => (a.weight X * ‖PauliReference.wave u X‖) ^ 2 := by
  have hv := wave_localize a u
  have hnorm := PhysicalCutoffCommutator.scalar_multiplier_norm_sq_ae
    (H := Fiber N PhotonFock) a ha (PauliReference.wave u)
  filter_upwards [hnorm] with X hX
  exact (congrArg (fun z : PauliReference.Wave N => ‖z X‖ ^ 2) hv).trans hX

theorem localized_scalar_sobolev {p S : ℝ}
    (hSob : PhysicalInfiniteOrder.ScalarSobolevBound (I := Fin N × Fin 3) p S)
    (a : DifferentiableMultiplier (Fin N × Fin 3)) (ha : ∀ X, 0 ≤ a.weight X)
    (u : PauliReference.Ref N) :
    MemLp (fun X => (a.weight X * ‖PauliReference.wave u X‖) ^ 2)
        (ENNReal.ofReal p) volume ∧
      (∫ X, ((a.weight X * ‖PauliReference.wave u X‖) ^ 2) ^ p) ^ (1 / p) ≤
        S * normGradientEnergy (PauliLocalEnergy.localize a u) := by
  let w := PauliLocalEnergy.localize a u
  have hh := hSob (fun X => ‖PauliReference.wave w X‖) (normGradient w)
    (normGradient_weak w) (Lp.memLp _).norm (normGradient_memLp w)
  have heq := localized_norm_sq_ae a ha u
  refine ⟨(memLp_congr_ae heq).mp hh.1, ?_⟩
  have hint : (∫ X, ((a.weight X * ‖PauliReference.wave u X‖) ^ 2) ^ p) =
      ∫ X, (‖PauliReference.wave w X‖ ^ 2) ^ p := by
    apply integral_congr_ae
    filter_upwards [heq] with X hX using congrArg (fun z : ℝ => z ^ p) hX.symm
  exact (congrArg (fun z : ℝ => z ^ (1 / p)) hint).le.trans hh.2

end PfHk.PauliInfiniteOrder

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
