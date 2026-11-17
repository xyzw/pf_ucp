import GptLean.PhysicalGraphCompactness
import GptLean.PhysicalPhotonLocalizedNumber
import GptLean.PhysicalPFCompactnessDensity

/-!
The local graph compactness argument on the actual photon channel.
The source vectors are its flattened Kraus expansion. Electronic tails
are measured by the original normal-state density, transported through
the proved scalar-multiplier identity for this same channel.
-/

noncomputable section
namespace GptLean.PhysicalGraphCompactness

open MeasureTheory Filter Topology PhysicalFock PhotonLocalization
  PhotonLocalizationChannel PhotonLocalizationKernelCutoffs
  PhysicalLocalFreeGraph PhysicalLocalSupport PhysicalPhotonLocalizedNumber
  PhysicalNormalTrace PhysicalClosedForms
open PhysicalNormalTrace.StandardNormalTraceBackground
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false

theorem channelSources_totallyBounded
    (BF : StandardSymmetricFockExponential) (B : StandardNormalTraceBackground)
    (S : StandardClosedFormBackground) (N m : ℕ)
    (hcompact : ∀ L M, TotallyBounded
      (supportValue N (radius m) L M '' Metric.closedBall 0 1))
    (x : ℕ → B.FullTrace N) (hx : ∀ n, x n ∈ B.normal.states)
    {E b : ℝ} (hE : 0 ≤ E) (hb : 0 ≤ b)
    (hfree : ∀ n, (PhysicalFreeForm.normalEnergy (Fin N × Fin 3) B S).expectation
      (B.normal.extend (physicalKraus BF N m) (x n)) ≤ ENNReal.ofReal E)
    (hnumber : ∀ n, (fullNumberForm B N).expectation
      (B.normal.extend (physicalKraus BF N m) (x n)) ≤ ENNReal.ofReal b)
    {ρ : Lp ℝ 1 (volume : Measure ElectronicPosition)}
    (hρ : Tendsto (fun n => PhysicalPFCompactnessDensity.density B N (x n)) atTop (𝓝 ρ)) :
    TotallyBounded (Set.range fun n => B.normal.extend (physicalKraus BF N m) (x n)) := by
  choose v hv using fun n => B.normal.positive_decomposition (x n) (hx n).1
  apply normalSources_totallyBounded N (radius m) B S hcompact
    (fun n => B.normal.extend (physicalKraus BF N m) (x n))
    (fun n => B.normal.preserves_states (physicalKraus BF N m) (hx n))
    (fun n => Repair.flattenVectors (fun i a => physicalKraus BF N m (v n i) a))
    (fun n => B.normal.mixed_hasSum (physicalKraus BF N m) (hv n))
    (fun n k => kraus_mem_photonSupport BF N m
      (v n (Nat.unpair k).1) (Nat.unpair k).2) hE hfree b
    (fun M n => number_tail_bound B N M
      (B.normal.positive (physicalKraus BF N m) (hx n).1) hb (hnumber n))
    (fun n => PhysicalPFCompactnessDensity.density B N (x n))
    (fun L n => ?_) hρ
  exact PhysicalPFCompactnessDensity.electronic_tail_lift B N
    ((photonFactorization BF).factor (physicalSplit m)) (hx n).1 L

end GptLean.PhysicalGraphCompactness
