import GptLean.RemovalClusterChannel
import GptLean.RemovalClusterPhase
import GptLean.Repair.ScalarFormOperations
import GptLean.RemovalChannel
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! The common measurable lift representative retains permutation
invariance. Thus the actual phase and coordinate channel vectors retain
the original electronic character, including at the level of L2 classes. -/

noncomputable section

set_option maxHeartbeats 800000

namespace GptLean.SymmetricLift

open MeasureTheory Filter

variable {Q : Type*} [MeasurableSpace Q]
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [TopologicalSpace.SeparableSpace V]

/-- One null set works for every parameter. Pulling it back by a particle
permutation preserves nullity because the permutation is a real linear
isometry of the configuration space. -/
theorem liftSectionRepresentative_permutation_ae
    (B : TensorBackground V) (N : ℕ) (t : Q → EuclideanSpace ℝ (Fin 3) → V)
    (π : Equiv.Perm (Fin N)) :
    ∀ᵐ x ∂volume, ∀ q,
      liftSectionRepresentative B N t q (permuteConfiguration π x) =
        liftSectionRepresentative B N t q x := by
  have hrep := liftSectionRepresentative_ae_eq B N t
  have hpre := (permuteConfiguration π).measurePreserving.quasiMeasurePreserving.ae hrep
  filter_upwards [hrep, hpre, ae_distinctConfigurations N] with x hx hπx hd
  intro q
  rw [hx q, hπx q]
  unfold recursiveLiftField
  rw [configurationTensor_permute]
  exact (recursiveLiftCandidate_properties B N).equivariant π x hd _

end GptLean.SymmetricLift

namespace GptLean.Repair

open MeasureTheory Filter GptLean.SymmetricLift GptLean.RemovalEnergy

variable {Q ι H : Type*} [MeasurableSpace Q]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

theorem measuredRepairLift_permutation_ae
    (B : TensorBackground SixTag) (N : ℕ)
    (basis : HilbertBasis ι ℂ (recursiveLiftCandidate B N).target) (index : ι ↪ ℕ)
    (t : Q → RepairSpace → SixTag) (π : Equiv.Perm (Fin N)) :
    ∀ᵐ x ∂volume, ∀ q,
      measuredRepairLift B N basis index t q (permuteConfiguration π x) =
        measuredRepairLift B N basis index t q x := by
  filter_upwards [liftSectionRepresentative_permutation_ae B N t π] with x hx
  intro q
  exact congrArg (countableEmbedding basis index) (hx q)

theorem electronicCharacter_toLp {N : ℕ}
    (χ : Equiv.Perm (Fin N) → ℂ) {f : Configuration N → H}
    (hf : MemLp f 2 volume)
    (hχ : HasElectronicCharacter (fun π => permuteConfiguration π) χ f) :
    HasElectronicCharacter (fun π => permuteConfiguration π) χ (hf.toLp f) := by
  intro π
  have hpre := (permuteConfiguration π).measurePreserving.quasiMeasurePreserving.ae hf.coeFn_toLp
  filter_upwards [hf.coeFn_toLp, hpre, hχ π] with x hx hπx hχx
  rw [hx, hπx, hχx]

/-- The actual L2 output has the source character. Only source symmetry
and the derived invariance of the two scalar factors are used. -/
theorem phase_channelSection_character {N : ℕ}
    (χ : Equiv.Perm (Fin N) → ℂ)
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (b : HilbertBasis ℕ ℂ V)
    (z : Q × Configuration N → V) (φ : Q → Configuration N → ℝ)
    (ψ : Q × Configuration N → H) (q : Q)
    (hz : AEStronglyMeasurable (fun x => z (q,x)) volume)
    (hunit : ∀ᵐ x ∂volume, ‖z (q,x)‖ = 1)
    (hzinv : ∀ π, ∀ᵐ x ∂volume, z (q,permuteConfiguration π x) = z (q,x))
    (hφ : AEStronglyMeasurable (φ q) volume)
    (hφinv : ∀ π, ∀ᵐ x ∂volume, φ q (permuteConfiguration π x) = φ q x)
    (hψ : MemLp (fun x => ψ (q,x)) 2 volume)
    (hχ : HasElectronicCharacter (fun π => permuteConfiguration π) χ (fun x => ψ (q,x)))
    (a : ℕ) :
    HasElectronicCharacter (fun π => permuteConfiguration π) χ
      (channelSection (ν := volume) b z
        (fun p => gaugePhase (φ p.1) p.2 • ψ p) a q) := by
  have hp : AEStronglyMeasurable (gaugePhase (φ q)) volume := by
    exact Complex.continuous_exp.comp_aestronglyMeasurable
      ((Complex.continuous_ofReal.comp_aestronglyMeasurable hφ).mul_const Complex.I)
  have hphase : MemLp (fun x => gaugePhase (φ q) x • ψ (q,x)) 2 volume :=
    hψ.smul (memLp_top_of_bound hp 1 (Eventually.of_forall fun x => (gaugePhase_norm _ x).le))
  have hout := channelValue_memLp b hz hphase.1 hunit
    ((memLp_two_iff_integrable_sq_norm hphase.1).mp hphase) a
  have hpinv : ∀ π, ∀ᵐ x ∂volume,
      gaugePhase (φ q) (permuteConfiguration π x) = gaugePhase (φ q) x := by
    intro π
    filter_upwards [hφinv π] with x hx
    simp only [gaugePhase, hx]
  have hphaseχ := electronicCharacter_smul (fun π => permuteConfiguration π) χ hpinv hχ
  have hcinv : ∀ π, ∀ᵐ x ∂volume,
      coordinate b (z (q,permuteConfiguration π x)) a = coordinate b (z (q,x)) a := by
    intro π
    filter_upwards [hzinv π] with x hx
    rw [hx]
  have houtχ := electronicCharacter_smul (fun π => permuteConfiguration π) χ
    (k := fun x => coordinate b (z (q,x)) a) hcinv hphaseχ
  rw [channelSection, toL2Section_eq
    (f := fun q x => coordinate b (z (q,x)) a • (gaugePhase (φ q) x • ψ (q,x)))
    (q := q) hout]
  exact electronicCharacter_toLp χ hout houtχ

end GptLean.Repair

namespace GptLean.RemovalGeometry

open MeasureTheory Filter GptLean.Repair GptLean.SymmetricLift GptLean.RemovalEnergy

variable {Q ι H : Type*} [MeasurableSpace Q] {N : ℕ}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

theorem clusterChannelLift_permutation_ae
    (B : TensorBackground SixTag)
    (basis : HilbertBasis ι ℂ (recursiveLiftCandidate B N).target) (index : ι ↪ ℕ)
    (c : Fin N → ClusterSpace) (R e : ℝ) (Z : Q → ℝ)
    (a : Q → ClusterSpace → ClusterSpace) (π : Equiv.Perm (Fin N)) :
    ∀ᵐ x ∂volume, ∀ q,
      clusterChannelLift B basis index c R e Z a q (permuteConfiguration π x) =
        clusterChannelLift B basis index c R e Z a q x :=
  measuredRepairLift_permutation_ae B N basis index (clusterTag c R e Z a) π

/-- Concrete phase and lift, with no target antisymmetry premise. This is
the source-only character theorem for the physical removal channels. -/
theorem cluster_phase_channelSection_character
    (B : TensorBackground SixTag)
    (basis : HilbertBasis ι ℂ (recursiveLiftCandidate B N).target) (index : ι ↪ ℕ)
    (c : Fin N → ClusterSpace) (R e : ℝ) (Z : Q → ℝ)
    (a : Q → ClusterSpace → ClusterSpace)
    (χ : Equiv.Perm (Fin N) → ℂ) (ψ : Q × Configuration N → H) (q : Q)
    (hz : AEStronglyMeasurable (clusterChannelLift B basis index c R e Z a q) volume)
    (hunit : ∀ᵐ x ∂volume, ‖clusterChannelLift B basis index c R e Z a q x‖ = 1)
    (hψ : MemLp (fun x => ψ (q,x)) 2 volume)
    (hχ : HasElectronicCharacter (fun π => permuteConfiguration π) χ (fun x => ψ (q,x)))
    (j : ℕ) :
    HasElectronicCharacter (fun π => permuteConfiguration π) χ
      (channelSection (ν := volume) countableTargetBasis
        (Function.uncurry (clusterChannelLift B basis index c R e Z a))
        (fun p => gaugePhase (configurationClusterPhase c R e (a p.1)) p.2 • ψ p) j q) := by
  have hzi (π : Equiv.Perm (Fin N)) : ∀ᵐ x ∂volume,
      clusterChannelLift B basis index c R e Z a q (permuteConfiguration π x) =
        clusterChannelLift B basis index c R e Z a q x :=
    (clusterChannelLift_permutation_ae B basis index c R e Z a π).mono fun x hx => hx q
  have hφm : AEStronglyMeasurable (configurationClusterPhase c R e (a q)) volume :=
    (configurationClusterPhase_contDiff c R e (a q)).continuous.aestronglyMeasurable
  have hφi (π : Equiv.Perm (Fin N)) : ∀ᵐ x ∂volume,
      configurationClusterPhase c R e (a q) (permuteConfiguration π x) =
        configurationClusterPhase c R e (a q) x :=
    Eventually.of_forall (configurationClusterPhase_permute c R e (a q) π)
  exact phase_channelSection_character χ countableTargetBasis
    (Function.uncurry (clusterChannelLift B basis index c R e Z a))
    (fun q => configurationClusterPhase c R e (a q)) ψ q hz hunit hzi hφm hφi hψ hχ j

end GptLean.RemovalGeometry
