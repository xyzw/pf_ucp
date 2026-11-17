import GptLean.PhysicalPFLocalizationControl
import GptLean.PhysicalNormalCompression

/-!
The physical Coulomb potential, radiation family, and energy truncations
in the common channel interface. The negative potential branch is zero
for the internal repulsive Coulomb model.
-/

noncomputable section

namespace GptLean.PhysicalPFLocalization

open MeasureTheory PhysicalFock PhysicalPFReference PhysicalNormalTrace
  PhysicalClosedForms PhysicalPFSource PhotonLocalization PhotonLocalizationChannel
  PhotonLocalizationFormBounds RemovalState
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000
set_option Elab.async false

section Zero

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (Tr : PositiveTraceData X)

def zeroForm : PositiveForm Tr where
  truncation _ := 0
  nonneg _ _ _ := le_rfl
  monotone _ _ _ _ _ := le_rfl

@[simp] theorem zeroForm_expectation (x : X) : (zeroForm Tr).expectation x = 0 := by
  simp [PositiveForm.expectation, zeroForm]

end Zero

variable (N : ℕ) (B : StandardNormalTraceBackground)

def potentialPart : Bool → PositiveForm (B.traceData (H := WaveSpace (Fin N × Fin 3)))
  | true => PhysicalPFDecomposition.coulomb N B
  | false => zeroForm (B.traceData (H := WaveSpace (Fin N × Fin 3)))

def potentialOperator : Bool → ℕ →
    WaveSpace (Fin N × Fin 3) →L[ℂ] WaveSpace (Fin N × Fin 3)
  | true => PhysicalSpatialPotential.operator volume
      (PhysicalPFDecomposition.coulombWeight N) (PhysicalPFDecomposition.coulombWeight_measurable N)
  | false => fun _ => 0

theorem potential_trace (b : Bool) (k : ℕ) (v : WaveSpace (Fin N × Fin 3)) :
    ((potentialPart N B b).truncation k
      ((B.realization (WaveSpace (Fin N × Fin 3))).rank.rankOne v) : ℂ) =
        ⟪v, potentialOperator N b k v⟫_ℂ := by
  cases b with
  | false => simp [potentialPart, zeroForm, potentialOperator]
  | true =>
    exact PhysicalSpatialPotential.truncation_complex (H := PhotonFock)
        (volume : Measure (SymmetricLift.Configuration N))
        (PhysicalPFDecomposition.coulombWeight N) (PhysicalPFDecomposition.coulombWeight_measurable N)
        B k v

theorem potential_commute
    (BF : StandardSymmetricFockExponential)
    (j : PhysicalOnePhotonFourier.PositionSpace →ₗᵢ[ℂ]
      WithLp 2 (PhysicalOnePhotonFourier.PositionSpace × PhysicalOnePhotonFourier.PositionSpace))
    (b : Bool) (k : ℕ) (v : WaveSpace (Fin N × Fin 3)) (a : ℕ) :
    (fullFactorization BF PhysicalOnePhotonFourier.fourier N).factor j
      (potentialOperator N b k v) a = potentialOperator N b k
        ((fullFactorization BF PhysicalOnePhotonFourier.fourier N).factor j v a) := by
  cases b with
  | false => simp only [potentialOperator, zero_apply, map_zero, lp.coeFn_zero, Pi.zero_apply]
  | true =>
    exact PhysicalNormalCompression.multiplier_kraus (H := PhotonFock)
        (μ := (volume : Measure (SymmetricLift.Configuration N)))
        (PhysicalSpatialPotential.cap (PhysicalPFDecomposition.coulombWeight N) k)
        (PhysicalSpatialPotential.cap_measurable volume (PhysicalPFDecomposition.coulombWeight N)
          (PhysicalPFDecomposition.coulombWeight_measurable N) k)
        (k : ℝ) (ae_of_all _ (PhysicalSpatialPotential.cap_bound
          (PhysicalPFDecomposition.coulombWeight N) k))
        ((photonFactorization BF).factor (transportSplit PhysicalOnePhotonFourier.fourier j)) v a

variable (S : StandardClosedFormBackground) (BF : StandardSymmetricFockExponential)
  (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)

theorem potential_le_control (b : Bool) {x : B.Trace (WaveSpace (Fin N × Fin 3))}
    (hx : x ∈ (B.realization (WaveSpace (Fin N × Fin 3))).rank.positive) :
    (potentialPart N B b).expectation x ≤
      (currentControl (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N)
        C κ hκ M hbound B S e).expectation x := by
  cases b with
  | false => simp only [potentialPart, zeroForm_expectation, zero_le]
  | true => exact coulomb_le_control C M B S e N κ hκ hbound hx

theorem calculus_radiation_le_control {x : B.Trace (WaveSpace (Fin N × Fin 3))}
    (hx : x ∈ (B.realization (WaveSpace (Fin N × Fin 3))).rank.positive) :
    ((PhysicalPFEnergyTruncation.calculus N B BF C).observable radiationFamily).expectation x ≤
      (currentControl (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N)
        C κ hκ M hbound B S e).expectation x :=
  (fullFormCalculus_radiation_eq BF C B PhysicalOnePhotonFourier.fourier N hx).trans_le
    (radiation_le_control C M B S e N κ hκ hbound hx)

theorem full_form {x : B.Trace (WaveSpace (Fin N × Fin 3))}
    (hx : x ∈ (B.realization (WaveSpace (Fin N × Fin 3))).rank.positive)
    (he : (PhysicalPFDecomposition.energy N B S C κ hκ M hbound e).expectation x < ⊤) :
    ((PhysicalPFDecomposition.energy N B S C κ hκ M hbound e).expectation x).toReal =
      ((PhysicalPFDecomposition.kinetic N B S C κ hκ M hbound e).expectation x).toReal +
      ((potentialPart N B true).expectation x).toReal -
      ((potentialPart N B false).expectation x).toReal +
      (((PhysicalPFEnergyTruncation.calculus N B BF C).observable radiationFamily).expectation x).toReal := by
  have hr := fullFormCalculus_radiation_eq BF C B PhysicalOnePhotonFourier.fourier N hx
  have h := (PhysicalPFEnergyTruncation.full_form N B S C κ hκ M hbound e hx he).trans
    (congrArg (fun r : ℝ≥0∞ =>
      ((PhysicalPFDecomposition.kinetic N B S C κ hκ M hbound e).expectation x).toReal +
        ((PhysicalPFDecomposition.coulomb N B).expectation x).toReal + r.toReal) hr.symm)
  simpa only [PhysicalPFEnergyTruncation.calculus, potentialPart, zeroForm_expectation,
    ENNReal.toReal_zero, sub_zero] using
    h

theorem truncated_form (k : ℕ) (x : B.Trace (WaveSpace (Fin N × Fin 3)))
    (hk : (PhysicalPFDecomposition.kinetic N B S C κ hκ M hbound e).expectation x < ⊤)
    (hp : ∀ b, (potentialPart N B b).expectation x < ⊤)
    (hr : (PhysicalPFEnergyTruncation.radiationPrefix N B BF C k).expectation x < ⊤) :
    PhysicalPFEnergyTruncation.truncatedEnergy N B S BF C κ hκ M hbound e k x =
      ENNReal.ofReal
        (((PhysicalPFDecomposition.kinetic N B S C κ hκ M hbound e).expectation x).toReal +
        ((potentialPart N B true).expectation x).toReal -
        ((potentialPart N B false).expectation x).toReal +
        ((PhysicalPFEnergyTruncation.radiationPrefix N B BF C k).expectation x).toReal) := by
  simpa only [potentialPart, zeroForm_expectation, ENNReal.toReal_zero, sub_zero] using
    PhysicalPFEnergyTruncation.truncatedEnergy_of_finite N B S BF C κ hκ M hbound e k x hk (hp true) hr

end GptLean.PhysicalPFLocalization
