import GptLean.PhysicalPFSource
import GptLean.PhysicalElectronicFermions

/-! Finite-energy normal fermionic states have actual fermionic reference sources. -/

noncomputable section

namespace GptLean.PhysicalPFSource

open MeasureTheory PhysicalFock PhysicalPFReference PhysicalNormalTrace
  PhysicalClosedForms PhysicalPFRadiation PhysicalElectronicFermions
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000

variable (N : ℕ) (V : Position (Fin N × Fin 3) → ℝ)
  (B : StandardNormalTraceBackground)

structure SupportedSource (x : B.Trace (WaveSpace (Fin N × Fin 3))) extends
    Source (Fin N × Fin 3) V B x where
  fermionic : ∀ n, PhysicalPFReference.inclusion (Fin N × Fin 3) V (vector n) ∈
    fermionicSubspace N PhotonFock

variable (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hκ : ∀ q, AEStronglyMeasurable (κ q) volume)
  (M : ℝ) (hbound : ∀ q, ∀ᵐ x ∂volume, ‖κ q x‖ ≤ M)
  (S : StandardClosedFormBackground) (e : ℝ)

theorem supported_source_exists {x : B.Trace (WaveSpace (Fin N × Fin 3))}
    (hx : x ∈ (B.realization (WaveSpace (Fin N × Fin 3))).rank.positive)
    (he : (normalEnergy (Fin N × Fin 3) V C κ hκ M hbound B S e).expectation x < ⊤)
    (hP : B.conjugation.conjugate (projection N PhotonFock) x = x) :
    Nonempty (SupportedSource N V B x) := by
  obtain ⟨v, hv, hs⟩ := B.conjugation.supported_decomposition B.normal (projection N PhotonFock)
    (projection_isStarProjection N PhotonFock).isIdempotentElem hx hP
  have hd (n : ℕ) : ∃ u : Reference (Fin N × Fin 3) V,
      PhysicalPFReference.inclusion (Fin N × Fin 3) V u = v n :=
    (normalEnergy_rankOne_finite_iff (Fin N × Fin 3) V C κ hκ M hbound B S e (v n)).mp
      (PhysicalNormalSpectral.source_form_finite
        (normalEnergy (Fin N × Fin 3) V C κ hκ M hbound B S e) hv he n)
  choose u hu using hd
  refine ⟨{ vector := u
            hasSum := hv.congr_fun (fun n =>
              congrArg (B.realization (WaveSpace (Fin N × Fin 3))).rank.rankOne (hu n))
            fermionic := ?_ }⟩
  intro n
  have hmem : v n ∈ fermionicSubspace N PhotonFock :=
    (mem_fermionicSubspace_iff N PhotonFock (v n)).mpr
      ((projection_eq_self_iff N PhotonFock (v n)).mp (hs n))
  exact (congrArg (fun w : WaveSpace (Fin N × Fin 3) => w ∈ fermionicSubspace N PhotonFock)
    (hu n)).mpr hmem

end GptLean.PhysicalPFSource
