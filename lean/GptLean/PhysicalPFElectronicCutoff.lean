import GptLean.PhysicalPFElectronicIMS
import GptLean.PhysicalElectronicScalars
import GptLean.PhysicalNormalCompression

/-! The physical electronic cutoff and its full PF IMS estimate.
The source identities are obtained from the actual finite-energy domain.
-/

noncomputable section

namespace GptLean.PhysicalPFElectronicCutoff

open MeasureTheory Filter Topology PhysicalFock PhysicalPFReference PhysicalNormalTrace
  PhysicalClosedForms PhotonLocalization
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000
set_option Elab.async false

variable (N : ℕ) (V : Position (Fin N × Fin 3) → ℝ)
  (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground) (e : ℝ)

def data : ElectronicCutoffData
    (A := (B.realization (WaveSpace (Fin N × Fin 3))).rank)
    (Ω := SymmetricLift.Configuration N) (K := PhotonFock)
    (α := Fin N → Bool) (ι := Fin N × Fin 3)
    (normalEnergy (Fin N × Fin 3) V C κ hκ M hbound B S e) where
  measure := volume
  partition := PhysicalElectronicScalars.weight N
  direction i := EuclideanSpace.single i 1
  differentiable := PhysicalElectronicScalars.differentiable N
  nonneg := PhysicalElectronicScalars.nonneg N
  square_partition := PhysicalElectronicScalars.square_partition N
  cost := PhysicalElectronicScalars.cost N
  cost_nonneg := PhysicalElectronicScalars.cost_nonneg N
  cost_zero := PhysicalElectronicScalars.cost_zero N
  metric := PhysicalElectronicScalars.metric N
  multiplier l a := (PhysicalElectronicScalars.branch N l a).multiplier
  selected := PhysicalElectronicScalars.selected N
  compression l := B.push
    ((PhysicalElectronicScalars.branch N l (PhysicalElectronicScalars.selected N)).multiplier)
  compression_rankOne l v := B.push_rankOne _ v
  source l v hv := by
    obtain ⟨u, rfl⟩ := (PhysicalPFRadiation.normalEnergy_rankOne_finite_iff
      (Fin N × Fin 3) V C κ hκ M hbound B S e v).mp hv
    exact ⟨PhysicalPFElectronicIMS.source V C κ hκ M hbound B S e
      (PhysicalElectronicScalars.branch N l) u⟩

theorem bound (l : ℕ) {x : B.Trace (WaveSpace (Fin N × Fin 3))}
    (hx : x ∈ (B.realization (WaveSpace (Fin N × Fin 3))).rank.positive)
    (hfinite : (normalEnergy (Fin N × Fin 3) V C κ hκ M hbound B S e).expectation x < ⊤)
    (htrace : (B.realization (WaveSpace (Fin N × Fin 3))).rank.trace x = 1) :
    (data N V C κ hκ M hbound B S e).compression l x ∈
        (B.realization (WaveSpace (Fin N × Fin 3))).rank.positive ∧
      (normalEnergy (Fin N × Fin 3) V C κ hκ M hbound B S e).expectation
          ((data N V C κ hκ M hbound B S e).compression l x) ≤
        (normalEnergy (Fin N × Fin 3) V C κ hκ M hbound B S e).expectation x +
          ENNReal.ofReal (PhysicalElectronicScalars.cost N l) :=
  (data N V C κ hκ M hbound B S e).bound B.normal (fun _ h => h) l hx hfinite htrace

theorem compression_tendsto {x : B.Trace (WaveSpace (Fin N × Fin 3))}
    (hx : x ∈ (B.realization (WaveSpace (Fin N × Fin 3))).rank.positive) :
    Tendsto (fun l => (data N V C κ hκ M hbound B S e).compression l x) atTop (𝓝 x) := by
  change Tendsto (fun l => B.push
    ((PhysicalElectronicScalars.branch N l (PhysicalElectronicScalars.selected N)).multiplier
      (H := PhotonFock)) x)
      atTop (𝓝 x)
  exact PhysicalNormalCompression.push_tendsto B (H := WaveSpace (Fin N × Fin 3))
    (fun l => (PhysicalElectronicScalars.branch N l (PhysicalElectronicScalars.selected N)).multiplier
      (H := PhotonFock))
    (fun l v => PhysicalElectronicScalars.multiplier_contraction N (H := PhotonFock) l
      (PhysicalElectronicScalars.selected N) v)
    (PhysicalElectronicScalars.selected_strong N (H := PhotonFock)) hx

end GptLean.PhysicalPFElectronicCutoff
