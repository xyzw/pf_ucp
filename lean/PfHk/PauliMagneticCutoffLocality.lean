import PfHk.PauliMagneticFormRules
import PfHk.PauliSquareForm
import PfHk.PauliClassicalCurlLocal
import PfHk.PhysicalCutoffLocality

/-! Scalar cutoffs can be transferred through the magnetic forms. The
classical argument uses the integral form directly, without an L2
magnetic multiplier hypothesis. -/

noncomputable section
namespace PfHk.PauliMagneticCutoffLocality

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.SymmetricLift GptLean.ElectronicH1Multiplier
  PfHk.PauliSpin PfHk.PauliSquareAlgebra PfHk.PauliGroundState
  PfHk.PhysicalFieldRegularity PfHk.PauliClassicalCurlForm
open scoped InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000

theorem integral_cutoff_pairing {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {μ : Measure X}
    (a b : X → ℝ) (z u az au : Lp H 2 μ)
    (hz : az =ᵐ[μ] fun x => a x • z x)
    (hu : au =ᵐ[μ] fun x => a x • u x) :
    (∫ x, weightedInner b az u x ∂μ) = ∫ x, weightedInner b z au x ∂μ := by
  apply integral_congr_ae
  filter_upwards [hz, hu] with x hx hy
  unfold weightedInner
  rw [hx, hy, inner_smul_left_eq_smul, inner_smul_right_eq_smul]

theorem integral_cutoff_left {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {μ : Measure X}
    (a b : X → ℝ) (z u az : Lp H 2 μ)
    (hz : az =ᵐ[μ] fun x => a x • z x)
    (hu : (fun x => a x • u x) =ᵐ[μ] u) :
    (∫ x, weightedInner b az u x ∂μ) = ∫ x, weightedInner b z u x ∂μ := by
  apply integral_congr_ae
  filter_upwards [hz, hu] with x hx hy
  unfold weightedInner
  rw [hx, inner_smul_left_eq_smul, ← inner_smul_right_eq_smul, hy]

private theorem trace_congr {N : ℕ}
    (B D : Fin N → Fin 3 → SpinIndex N → SpinIndex N → ℂ)
    (h : ∀ n k s t, B n k s t = D n k s t) :
    (1 / 2 : ℂ) * ∑ n, ∑ k, matrixSpinTrace n k (B n k) =
      (1 / 2 : ℂ) * ∑ n, ∑ k, matrixSpinTrace n k (D n k) :=
  congrArg (fun E : Fin N → Fin 3 → SpinIndex N → SpinIndex N → ℂ =>
    (1 / 2 : ℂ) * ∑ n, ∑ k, matrixSpinTrace n k (E n k))
      (funext fun n => funext fun k => funext fun s => funext fun t => h n k s t)

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
attribute [local irreducible] referenceSubspace inclusion
  DifferentiableMultiplier.multiplier PhysicalPFScalarMultiplier.multiply

variable {N : ℕ}

theorem localized_value_ae (a : DifferentiableMultiplier (Fin N × Fin 3))
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    (inclusion (Fin N × Fin 3) (fun _ => 0)
      (PhysicalPFScalarMultiplier.multiply (fun _ => 0) a u) : Configuration N → PhotonFock) =ᵐ[volume]
      fun X => a.weight X • inclusion (Fin N × Fin 3) (fun _ => 0) u X := by
  apply (Filter.EventuallyEq.of_eq (congrArg (fun v : WaveSpace (Fin N × Fin 3) => ⇑v)
    (PhysicalPFScalarMultiplier.value_multiply (fun _ => 0) a u))).trans
  unfold DifferentiableMultiplier.multiplier
  exact PhotonLocalization.realL2Multiplier_apply a.weight
    a.differentiable.continuous.aestronglyMeasurable a.bound
    (Filter.Eventually.of_forall a.bounded) (inclusion (Fin N × Fin 3) (fun _ => 0) u)

theorem classical_cutoff_pairing (a : DifferentiableMultiplier (Fin N × Fin 3))
    (B : Fin N → Fin 3 → PhysicalSourceCoordinates.Position → ℝ) (z u : Ref N) :
    PauliSquareForm.classicalForm B (PauliLocalEnergy.localize a z) u =
      PauliSquareForm.classicalForm B z (PauliLocalEnergy.localize a u) :=
  trace_congr _ _ (fun n k s t => integral_cutoff_pairing a.weight
    (CoordinateSobolev.coordinateCoefficient n (B n k))
    (inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
    (inclusion (Fin N × Fin 3) (fun _ => 0) (u t))
    (inclusion (Fin N × Fin 3) (fun _ => 0) (PauliLocalEnergy.localize a z s))
    (inclusion (Fin N × Fin 3) (fun _ => 0) (PauliLocalEnergy.localize a u t))
    (localized_value_ae a (z s)) (localized_value_ae a (u t)))

theorem classical_localize_left
    (a : DifferentiableMultiplier (Fin N × Fin 3))
    (B : Fin N → Fin 3 → PhysicalSourceCoordinates.Position → ℝ)
    (z u : Ref N)
    (hfix : ∀ s, a.multiplier (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) =
      inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) :
    PauliSquareForm.classicalForm B (PauliLocalEnergy.localize a z) u =
      PauliSquareForm.classicalForm B z u := by
  have hfixed : PauliLocalEnergy.localize a u = u := funext fun s =>
    PhysicalCutoffLocality.reference_multiply_eq_of_value (fun _ => 0) a (u s) (u s) (hfix s)
  exact (classical_cutoff_pairing a B z u).trans
    (congrArg (PauliSquareForm.classicalForm B z) hfixed)

theorem classical_coefficient_congr
    (B B' : Fin N → Fin 3 → PhysicalSourceCoordinates.Position → ℝ)
    (U : Fin N → Set PhysicalSourceCoordinates.Position)
    (hB : ∀ n k x, x ∈ U n → B n k x = B' n k x)
    (z u : Ref N)
    (hus : ∀ n s, PauliClassicalCurl.SupportedInCoordinate n (U n)
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))) :
    PauliSquareForm.classicalForm B z u = PauliSquareForm.classicalForm B' z u :=
  trace_congr _ _ (fun n k s t => PauliClassicalCurl.pairing_congr n (U n)
    (B n k) (B' n k) (hB n k)
    (inclusion (Fin N × Fin 3) (fun _ => 0) (u t))
    (inclusion (Fin N × Fin 3) (fun _ => 0) (z s)) (hus n t))

theorem quantum_cutoff_pairing (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ)
    (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
    (a : DifferentiableMultiplier (Fin N × Fin 3)) (z u : Ref N) :
    (∑ s, inner ℂ (inclusion (Fin N × Fin 3) (fun _ => 0) (PauliLocalEnergy.localize a z s))
      (PauliMagneticOperator.quantum F χ hUV C e u s)) =
    ∑ s, inner ℂ (inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
      (PauliMagneticOperator.quantum F χ hUV C e (PauliLocalEnergy.localize a u) s) := by
  apply Finset.sum_congr rfl
  intro s _
  exact (congrArg (fun v : WaveSpace (Fin N × Fin 3) =>
    inner ℂ v (PauliMagneticOperator.quantum F χ hUV C e u s))
      (PhysicalPFScalarMultiplier.value_multiply (fun _ => 0) a (z s))).trans
    ((a.multiplier_symmetric (H := PhotonFock) _ _).symm.trans
      (congrArg (fun v : WaveSpace (Fin N × Fin 3) =>
        inner ℂ (inclusion (Fin N × Fin 3) (fun _ => 0) (z s)) v)
        (PauliMagneticFormRules.quantum_localize F χ hUV C a e u s).symm))

theorem quantum_localize_left (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ)
    (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
    (a : DifferentiableMultiplier (Fin N × Fin 3)) (z u : Ref N)
    (hfix : ∀ s, a.multiplier (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) =
      inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) :
    (∑ s, inner ℂ (inclusion (Fin N × Fin 3) (fun _ => 0) (PauliLocalEnergy.localize a z s))
      (PauliMagneticOperator.quantum F χ hUV C e u s)) =
    ∑ s, inner ℂ (inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
      (PauliMagneticOperator.quantum F χ hUV C e u s) := by
  have hfixed : PauliLocalEnergy.localize a u = u := funext fun s =>
    PhysicalCutoffLocality.reference_multiply_eq_of_value (fun _ => 0) a (u s) (u s) (hfix s)
  have hsource (s : SpinIndex N) :
      a.multiplier (PauliMagneticOperator.quantum F χ hUV C e u s) =
        PauliMagneticOperator.quantum F χ hUV C e u s :=
    (PauliMagneticFormRules.quantum_localize F χ hUV C a e u s).symm.trans
      (congrArg (fun v : Ref N => PauliMagneticOperator.quantum F χ hUV C e v s) hfixed)
  apply Finset.sum_congr rfl
  intro s _
  exact (congrArg (fun v : WaveSpace (Fin N × Fin 3) =>
    inner ℂ v (PauliMagneticOperator.quantum F χ hUV C e u s))
      (PhysicalPFScalarMultiplier.value_multiply (fun _ => 0) a (z s))).trans
    ((a.multiplier_symmetric (H := PhotonFock) _ _).symm.trans
      (congrArg (fun v : WaveSpace (Fin N × Fin 3) =>
        inner ℂ (inclusion (Fin N × Fin 3) (fun _ => 0) (z s)) v) (hsource s)))

end PfHk.PauliMagneticCutoffLocality

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
