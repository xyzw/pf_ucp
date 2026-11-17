import PfHk.PauliFieldCommutation
import PfHk.PauliMagneticWeakPairing
import PfHk.CenteredPhysicalReference

/-! Weak identities for the actual physical coupling labels `-e G_j`.
Their mutual field commutation follows from the proved reality of the
polarization kernels. The ordinary-field identity uses only the first
ultraviolet moment and the retained ordinary form-core theorem. -/

noncomputable section
namespace PfHk.PauliPhysicalFieldCommutation

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.PhysicalNonattainmentFluxKernel
  GptLean.SymmetricLift GptLean.Representability Gaussian
  PfHk.PhysicalFieldRegularity PfHk.PhysicalOperatorDomain
  PfHk.WeylGraphC1Calculus PfHk.WeylCoreReference
open scoped InnerProductSpace Topology

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
attribute [local instance]
  PfHk.PhysicalFormProductRules.instInnerProductSpaceRealSubtypePreLpNatSectorPhotonModePhotonMeasureMemAddSubgroupPhotonFock_pfHk
  PfHk.PauliMagneticWeakCore.weakCoreRadiationComplex
  PfHk.PauliMagneticWeakCore.weakCoreRadiationReal
  PfHk.PauliMagneticWeakPairing.referenceComplex

/-- The exact equality `⟪A u,B v⟫ = ⟪B u,A v⟫`. -/
def CommutingPairing {Q H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A B : Q → H) (u v : Q) : Prop :=
  inner ℂ (A u) (B v) = inner ℂ (B u) (A v)

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (e : ℝ)

def couplingBound : ℝ := |e| * CenteredPhysicalReference.profileBound F χ

theorem coupling_norm_bound (j : Fin N × Fin 3) (X : Configuration N) :
    ‖RadialGauge.couplingKernel F χ e j X‖ ≤ couplingBound F χ e := by
  have hp : ‖physicalKernel F χ j.2 (particle X j.1)‖ ≤
      CenteredPhysicalReference.profileBound F χ :=
    PhysicalProfiles.momentumKernel_bound (formFactors F χ) rfl
      (LinearIsometryEquiv.refl ℝ _) (j.2, particle X j.1)
  unfold RadialGauge.couplingKernel couplingBound
  rw [norm_smul, Real.norm_eq_abs, abs_neg]
  exact mul_le_mul_of_nonneg_left hp (abs_nonneg e)

variable (C : CanonicalSectorCCR photonMeasure)

def couplingField (j : Fin N × Fin 3) :=
  PauliMagneticWeakPairing.field C (RadialGauge.couplingKernel F χ e j)
    (RadialGauge.couplingKernel_continuous F χ e j)
    (couplingBound F χ e) (coupling_norm_bound F χ e j)

attribute [local irreducible] radiationRoot weightedKernelSubspace
  referenceSubspace inclusion ordinary radiationSource kernelField

theorem field_field (W : ConcreteWeylLaw photonMeasure)
    (i j : Fin N × Fin 3)
    (u v : Reference (Fin N × Fin 3) (fun _ => 0)) :
    CommutingPairing (Q := Reference (Fin N × Fin 3) (fun _ => 0))
      (H := WaveSpace (Fin N × Fin 3))
      (couplingField F χ e C i) (couplingField F χ e C j) u v := by
  have h := PauliFieldCommutation.spatialField_pairing C W
    (X := Configuration N) volume
    (RadialGauge.couplingKernel F χ e i) (RadialGauge.couplingKernel F χ e j)
    (RadialGauge.couplingKernel_continuous F χ e i).aestronglyMeasurable
    (RadialGauge.couplingKernel_continuous F χ e j).aestronglyMeasurable
    (couplingBound F χ e) (couplingBound F χ e)
    (ae_of_all _ (coupling_norm_bound F χ e i))
    (ae_of_all _ (coupling_norm_bound F χ e j))
    (ae_of_all _ (fun X => RadialGauge.coupling_inner_im F χ e i j X X))
    (radiationSource (Fin N × Fin 3) (fun _ => 0) u)
    (radiationSource (Fin N × Fin 3) (fun _ => 0) v)
  exact h

variable (hUV : CarlemanUV χ)

def derivativeBound : ℝ := |e| * RadialGauge.momentBound F χ hUV

theorem derivative_norm_bound (i j : Fin N × Fin 3) (X : Configuration N) :
    ‖RadialGauge.couplingDerivative F χ hUV e j (EuclideanSpace.single i 1) X‖ ≤
      derivativeBound F χ e hUV := by
  simpa only [derivativeBound, PiLp.norm_single, norm_one, mul_one] using
    RadialGauge.couplingDerivative_norm_le F χ hUV e j (EuclideanSpace.single i 1) X

def derivativeField (i j : Fin N × Fin 3) :=
  PauliMagneticWeakPairing.field C
    (RadialGauge.couplingDerivative F χ hUV e j (EuclideanSpace.single i 1))
    (RadialGauge.couplingDerivative_continuous F χ hUV e j (EuclideanSpace.single i 1))
    (derivativeBound F χ e hUV) (derivative_norm_bound F χ e hUV i j)

/-- Weak differentiation of the actual quantum coupling on the common
compactly supported reference domain. -/
theorem ordinary_field (W : ConcreteWeylLaw photonMeasure) (B : StandardWeylGraphC1 W)
    (D : StandardWeylFormCoreDensity W B) (i j : Fin N × Fin 3)
    (s : Set (Configuration N)) (hs : IsOpen s)
    (u v : Reference (Fin N × Fin 3) (fun _ => 0))
    (hu : CompactlySupportedIn s u) (hv : CompactlySupportedIn s v) :
    PauliMagneticWeakPairing.Pairing
      (Q := Reference (Fin N × Fin 3) (fun _ => 0)) (H := WaveSpace (Fin N × Fin 3))
      (ordinary (Fin N × Fin 3) (fun _ => 0) i) (couplingField F χ e C j)
      (inclusion (Fin N × Fin 3) (fun _ => 0)) (derivativeField F χ e C hUV i j) u v := by
  exact PauliMagneticWeakPairing.compact_pairing
    (I := Fin N × Fin 3) (C := C)
    (k := RadialGauge.couplingKernel F χ e j)
    (dk := RadialGauge.couplingDerivative F χ hUV e j (EuclideanSpace.single i 1))
    (hk := RadialGauge.couplingKernel_continuous F χ e j)
    (hdk := RadialGauge.couplingDerivative_continuous F χ hUV e j (EuclideanSpace.single i 1))
    (M := couplingBound F χ e) (Md := derivativeBound F χ e hUV)
    (hM := coupling_norm_bound F χ e j) (hMd := derivative_norm_bound F χ e hUV i j)
    (i := i) (hderiv := RadialGauge.couplingKernel_hasLineDerivAt F χ hUV e j
      (EuclideanSpace.single i 1)) W B D s hs u v hu hv

end PfHk.PauliPhysicalFieldCommutation

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
