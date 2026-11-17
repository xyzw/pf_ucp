import PfHk.PauliPhysicalFieldLinearity
import PfHk.ElectronicH1MixedPairing
import PfHk.PauliMagneticOperator
import GptLean.SymmetricLift.TensorApproximation

/-! The weak commutator of the actual free physical covariant derivatives.
The curl is the existing quantized magnetic multiplier, with the sign
fixed by the physical convention `qP = -i∂ - e A_quantum`. -/

noncomputable section
namespace PfHk.PauliQuantumCommutator

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.SymmetricLift GptLean.Representability
  PfHk.PhysicalFieldRegularity PfHk.PhysicalOperatorDomain
  PfHk.WeylGraphC1Calculus PfHk.WeylCoreReference
  PfHk.PauliPhysicalFieldCommutation PfHk.PauliPhysicalFieldLinearity
open scoped InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000

section Algebra
variable {Q H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The exact antisymmetric pairing `⟪A u,B v⟫ - ⟪B u,A v⟫`. -/
def Cross (A B : Q → H) (u v : Q) : ℂ :=
  inner ℂ (A u) (B v) - inner ℂ (B u) (A v)

theorem affine_cross (P R A B J K L : Q → H) (u v : Q)
    (hPR : CommutingPairing P R u v) (hAB : CommutingPairing A B u v)
    (hPB : PauliMagneticWeakPairing.Pairing P B J K u v)
    (hRA : PauliMagneticWeakPairing.Pairing R A J L u v) :
    Cross (fun z => (-Complex.I) • P z + A z)
      (fun z => (-Complex.I) • R z + B z) u v =
      -Complex.I * inner ℂ (J u) (K v - L v) := by
  unfold Cross CommutingPairing PauliMagneticWeakPairing.Pairing at *
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    inner_sub_right, map_neg, Complex.conj_I, neg_neg]
  linear_combination (-Complex.I * Complex.I) * hPR + hAB +
    Complex.I * hPB - Complex.I * hRA

theorem cross_congr (A B A' B' : Q → H) (u v : Q)
    (hAu : A u = A' u) (hAv : A v = A' v)
    (hBu : B u = B' u) (hBv : B v = B' v) :
    Cross A B u v = Cross A' B' u v :=
  congrArg₂ (fun z w : ℂ => z - w)
    (congrArg₂ (inner ℂ) hAu hBv) (congrArg₂ (inner ℂ) hBu hAv)

theorem charged_curl (u x y b : H) (e : ℝ)
    (h : x - y = ((-e : ℝ) : ℂ) • b) :
    -Complex.I * inner ℂ u (x - y) =
      Complex.I * (e : ℂ) * inner ℂ u b := by
  rw [h, inner_smul_right]
  simp only [Complex.ofReal_neg]
  ring

end Algebra

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
attribute [local instance]
  PfHk.PhysicalFormProductRules.instInnerProductSpaceRealSubtypePreLpNatSectorPhotonModePhotonMeasureMemAddSubgroupPhotonFock_pfHk
  PfHk.PauliMagneticWeakCore.weakCoreRadiationComplex
  PfHk.PauliMagneticWeakCore.weakCoreRadiationReal
  PfHk.PauliMagneticWeakPairing.referenceComplex
attribute [local irreducible] radiationRoot weightedKernelSubspace
  referenceSubspace inclusion ordinary radiationSource kernelField

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (e : ℝ)
  (C : CanonicalSectorCCR photonMeasure) (hUV : CarlemanUV χ)

theorem ordinary_ordinary (i j : Fin N × Fin 3)
    (u v : Reference (Fin N × Fin 3) (fun _ => 0)) :
    CommutingPairing (Q := Reference (Fin N × Fin 3) (fun _ => 0))
      (H := WaveSpace (Fin N × Fin 3))
      (ordinary (Fin N × Fin 3) (fun _ => 0) i)
      (ordinary (Fin N × Fin 3) (fun _ => 0) j) u v := by
  unfold CommutingPairing ordinary
  exact ElectronicH1MixedPairing.complex_pairing (H := PhotonFock) (I := Fin N × Fin 3)
    (electronic (Fin N × Fin 3) (fun _ => 0) u)
    (electronic (Fin N × Fin 3) (fun _ => 0) v) i j

/-- The actual quantum covariant commutator, before choosing a cyclic
pair of spatial directions. No commutator identity is an assumption. -/
theorem qP_cross (W : ConcreteWeylLaw photonMeasure) (B : StandardWeylGraphC1 W)
    (D : StandardWeylFormCoreDensity W B) (i j : Fin N × Fin 3)
    (s : Set (Configuration N)) (hs : IsOpen s)
    (u v : Reference (Fin N × Fin 3) (fun _ => 0))
    (hu : CompactlySupportedIn s u) (hv : CompactlySupportedIn s v) :
    Cross (Q := Reference (Fin N × Fin 3) (fun _ => 0)) (H := WaveSpace (Fin N × Fin 3))
      (qP C F χ e i) (qP C F χ e j) u v =
      -Complex.I * inner ℂ (E := WaveSpace (Fin N × Fin 3))
        (inclusion (Fin N × Fin 3) (fun _ => 0) u)
        (derivativeField F χ e C hUV i j v - derivativeField F χ e C hUV j i v) := by
  have h := affine_cross (Q := Reference (Fin N × Fin 3) (fun _ => 0))
    (H := WaveSpace (Fin N × Fin 3))
    (ordinary (Fin N × Fin 3) (fun _ => 0) i)
    (ordinary (Fin N × Fin 3) (fun _ => 0) j)
    (couplingField F χ e C i) (couplingField F χ e C j)
    (inclusion (Fin N × Fin 3) (fun _ => 0))
    (derivativeField F χ e C hUV i j) (derivativeField F χ e C hUV j i) u v
    (ordinary_ordinary i j u v) (field_field F χ e C W i j u v)
    (ordinary_field F χ e C hUV W B D i j s hs u v hu hv)
    (ordinary_field F χ e C hUV W B D j i s hs u v hu hv)
  exact (cross_congr (Q := Reference (Fin N × Fin 3) (fun _ => 0))
    (H := WaveSpace (Fin N × Fin 3)) _ _ _ _ u v
    (qP_eq C F χ e i u) (qP_eq C F χ e i v)
    (qP_eq C F χ e j u) (qP_eq C F χ e j v)).trans h

theorem derivative_kernel_curl (n : Fin N) (a : Fin 3) (X : Configuration N) :
    RadialGauge.couplingDerivative F χ hUV e (n, PauliMagneticField.last a)
        (EuclideanSpace.single (n, PauliMagneticField.next a) 1) X -
      RadialGauge.couplingDerivative F χ hUV e (n, PauliMagneticField.next a)
        (EuclideanSpace.single (n, PauliMagneticField.last a) 1) X =
      (-e) • PauliMagneticOperator.profile F χ hUV n a X := by
  simp only [RadialGauge.couplingDerivative, PauliMagneticOperator.profile,
    PauliMagneticField.kernel, particle_single_same, smul_sub]

/-- The derivative difference is the existing L2 magnetic component,
multiplied by the actual charge `-e`. -/
theorem derivativeField_curl (n : Fin N) (a : Fin 3)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    derivativeField F χ e C hUV (n, PauliMagneticField.next a) (n, PauliMagneticField.last a) u -
      derivativeField F χ e C hUV (n, PauliMagneticField.last a) (n, PauliMagneticField.next a) u =
      ((-e : ℝ) : ℂ) • PauliMagneticOperator.component F χ hUV C n a u := by
  exact spatial_sub_eq_smul C volume
    (RadialGauge.couplingDerivative F χ hUV e (n, PauliMagneticField.last a)
      (EuclideanSpace.single (n, PauliMagneticField.next a) 1))
    (RadialGauge.couplingDerivative F χ hUV e (n, PauliMagneticField.next a)
      (EuclideanSpace.single (n, PauliMagneticField.last a) 1))
    (PauliMagneticOperator.profile F χ hUV n a)
    (RadialGauge.couplingDerivative_continuous F χ hUV e (n, PauliMagneticField.last a)
      (EuclideanSpace.single (n, PauliMagneticField.next a) 1)).aestronglyMeasurable
    (RadialGauge.couplingDerivative_continuous F χ hUV e (n, PauliMagneticField.next a)
      (EuclideanSpace.single (n, PauliMagneticField.last a) 1)).aestronglyMeasurable
    (PauliMagneticOperator.profile_measurable F χ hUV n a)
    (derivativeBound F χ e hUV) (derivativeBound F χ e hUV)
    (2 * RadialGauge.momentBound F χ hUV) (-e)
    (ae_of_all _ (derivative_norm_bound F χ e hUV
      (n, PauliMagneticField.next a) (n, PauliMagneticField.last a)))
    (ae_of_all _ (derivative_norm_bound F χ e hUV
      (n, PauliMagneticField.last a) (n, PauliMagneticField.next a)))
    (PauliMagneticOperator.profile_bound F χ hUV n a)
    (ae_of_all _ (derivative_kernel_curl F χ e hUV n a))
    (radiationSource (Fin N × Fin 3) (fun _ => 0) u)

/-- The quantum curl has sign `+ i e` in the antisymmetric weak
covariant pairing and therefore sign `-e/2` in the Pauli form. -/
theorem qP_cross_curl (W : ConcreteWeylLaw photonMeasure) (B : StandardWeylGraphC1 W)
    (D : StandardWeylFormCoreDensity W B) (n : Fin N) (a : Fin 3)
    (s : Set (Configuration N)) (hs : IsOpen s)
    (u v : Reference (Fin N × Fin 3) (fun _ => 0))
    (hu : CompactlySupportedIn s u) (hv : CompactlySupportedIn s v) :
    Cross (Q := Reference (Fin N × Fin 3) (fun _ => 0)) (H := WaveSpace (Fin N × Fin 3))
      (qP C F χ e (n, PauliMagneticField.next a))
      (qP C F χ e (n, PauliMagneticField.last a)) u v =
      Complex.I * (e : ℂ) * inner ℂ (E := WaveSpace (Fin N × Fin 3))
        (inclusion (Fin N × Fin 3) (fun _ => 0) u)
        (PauliMagneticOperator.component F χ hUV C n a v) := by
  exact (qP_cross F χ e C hUV W B D
    (n, PauliMagneticField.next a) (n, PauliMagneticField.last a) s hs u v hu hv).trans
      (charged_curl (H := WaveSpace (Fin N × Fin 3)) _ _ _ _ e
        (derivativeField_curl F χ e C hUV n a v))

end PfHk.PauliQuantumCommutator

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
