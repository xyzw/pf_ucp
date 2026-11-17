import GptLean.PhysicalCovariantKinetic
import GptLean.PhysicalCoulombH1Density
import GptLean.ElectronicH1Maximal
import GptLean.PhysicalSpatialRadiationDomain
import GptLean.PhysicalPFDomain

/-!
The closed covariant kinetic domain intersected with the radiation domain
is the actual common Coulomb reference domain. Field symmetry moves the
field action onto the radiation-finite vector before H1 density is used.
-/

noncomputable section

namespace GptLean.PhysicalCovariantKinetic

open MeasureTheory PhysicalFock PhysicalPFReference PhysicalNormalTrace PhysicalClosedForms
open scoped InnerProductSpace ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000
set_option Elab.async false

private theorem recover_pair {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (a b e : ℝ) (hab : b * a = 1) (u v w dv au av : H)
    (hw : ⟪w, v⟫_ℂ = ⟪u, (a : ℂ) • ((-Complex.I) • dv - (e : ℂ) • av)⟫_ℂ)
    (hf : ⟪v, au⟫_ℂ = ⟪av, u⟫_ℂ) :
    ⟪v, Complex.I • ((b : ℂ) • w + (e : ℂ) • au)⟫_ℂ = -⟪dv, u⟫_ℂ := by
  have hw' : ⟪v, w⟫_ℂ = ⟪(a : ℂ) • ((-Complex.I) • dv - (e : ℂ) • av), u⟫_ℂ := by
    simpa only [inner_conj_symm] using congrArg (starRingEnd ℂ) hw
  simp only [inner_smul_left, inner_sub_left, Complex.conj_ofReal,
    map_neg, Complex.conj_I, neg_neg] at hw'
  have hab' : (b : ℂ) * (a : ℂ) = 1 := by exact_mod_cast hab
  simp only [inner_smul_right, inner_add_right, hw', hf]
  calc
    _ = ((b : ℂ) * (a : ℂ)) * Complex.I ^ 2 * ⟪dv, u⟫_ℂ +
        (1 - (b : ℂ) * (a : ℂ)) * Complex.I * (e : ℂ) * ⟪av, u⟫_ℂ := by ring
    _ = _ := by rw [hab', Complex.I_sq]; ring

private theorem sqrt_two_half : Real.sqrt 2 * Real.sqrt (1 / 2 : ℝ) = 1 := by
  rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

variable (N : ℕ) (C : CanonicalSectorCCR photonMeasure)
  (κ : Index N → Position (Index N) → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)

def recoveredDerivative (d : Output N)
    (r : SpatialRadiationGraph (volume : Measure (Position (Index N)))) (i : Index N) :
    Wave N :=
  Complex.I • ((Real.sqrt 2 : ℂ) • d i +
    (e : ℂ) • spatialField volume C (κ i) (hκ i) M (hbound i) r)

theorem recoveredDerivative_reference (u : Wave N) (d : Output N)
    (hd : (u, d) ∈ (operator N C κ hκ M hbound e).graph)
    (r : SpatialRadiationGraph (volume : Measure (Position (Index N))))
    (hr : spatialRadiationInclusion volume r = u)
    (i : Index N) (v : Reference N) :
    ⟪inclusion (Index N) (potential N) v, recoveredDerivative N C κ hκ M hbound e d r i⟫_ℂ =
      -⟪ordinary (Index N) (potential N) i v, u⟫_ℂ := by
  have hf := spatial_field_symmetric volume C (κ i) (hκ i) M (hbound i)
    (radiationSource (Index N) (potential N) v) r
  have hm : ⟪inclusion (Index N) (potential N) v,
      spatialField volume C (κ i) (hκ i) M (hbound i) r⟫_ℂ =
      ⟪field (Index N) (potential N) C κ hκ M hbound i v, u⟫_ℂ :=
    (congrArg (fun w : Wave N =>
      ⟪w, spatialField volume C (κ i) (hκ i) M (hbound i) r⟫_ℂ)
        (radiation_matches (Index N) (potential N) v).symm).trans
      (hf.trans (congrArg (fun w : Wave N =>
        ⟪field (Index N) (potential N) C κ hκ M hbound i v, w⟫_ℂ) hr))
  exact recover_pair (Real.sqrt (1 / 2 : ℝ)) (Real.sqrt 2) e sqrt_two_half
    u (inclusion (Index N) (potential N) v)
    (d i) (ordinary (Index N) (potential N) i v)
    (spatialField volume C (κ i) (hκ i) M (hbound i) r)
    (field (Index N) (potential N) C κ hκ M hbound i v)
    (graph_test N C κ hκ M hbound e u d hd i v) hm

theorem recoveredDerivative_adjoint (u : Wave N) (d : Output N)
    (hd : (u, d) ∈ (operator N C κ hκ M hbound e).graph)
    (r : SpatialRadiationGraph (volume : Measure (Position (Index N))))
    (hr : spatialRadiationInclusion volume r = u)
    (i : Index N) (v : ElectronicH1Complex.ComplexH1 PhotonFock (Index N)) :
    ⟪ElectronicH1Complex.value v, recoveredDerivative N C κ hκ M hbound e d r i⟫_ℂ =
      -⟪ElectronicH1Complex.derivative i v, u⟫_ℂ := by
  have hc : IsClosed {v : ElectronicH1Complex.ComplexH1 PhotonFock (Index N) |
      ⟪ElectronicH1Complex.value v, recoveredDerivative N C κ hκ M hbound e d r i⟫_ℂ =
        -⟪ElectronicH1Complex.derivative i v, u⟫_ℂ} :=
    isClosed_eq (ElectronicH1Complex.value.continuous.inner continuous_const)
      (((ElectronicH1Complex.derivative i).continuous.inner continuous_const).neg)
  apply closure_minimal (t := {v : ElectronicH1Complex.ComplexH1 PhotonFock (Index N) |
      ⟪ElectronicH1Complex.value v, recoveredDerivative N C κ hκ M hbound e d r i⟫_ℂ =
        -⟪ElectronicH1Complex.derivative i v, u⟫_ℂ}) _ hc
    (PhysicalCoulombReferenceCore.electronic_denseRange N 1 (by norm_num) v)
  rintro _ ⟨w, rfl⟩
  exact recoveredDerivative_reference N C κ hκ M hbound e u d hd r hr i w

def electronicOfJoint (u : Wave N) (d : Output N)
    (hd : (u, d) ∈ (operator N C κ hκ M hbound e).graph)
    (r : SpatialRadiationGraph (volume : Measure (Position (Index N))))
    (hr : spatialRadiationInclusion volume r = u) :
    ElectronicH1Complex.ComplexH1 PhotonFock (Index N) :=
  ElectronicH1Maximal.ofAdjoint u
    (recoveredDerivative N C κ hκ M hbound e d r)
    (recoveredDerivative_adjoint N C κ hκ M hbound e u d hd r hr)

theorem joint_domain_reference (u : Wave N) (d : Output N)
    (hd : (u, d) ∈ (operator N C κ hκ M hbound e).graph)
    (r : SpatialRadiationGraph (volume : Measure (Position (Index N))))
    (hr : spatialRadiationInclusion volume r = u) :
    ∃ v : Reference N, inclusion (Index N) (potential N) v = u := by
  let h1 := electronicOfJoint N C κ hκ M hbound e u d hd r hr
  let free : PhysicalFreeReferenceCore.FreeReference (Index N) := ⟨(h1, r), by
    change u - spatialRadiationInclusion volume r = 0
    exact sub_eq_zero.mpr hr.symm⟩
  exact ⟨PhysicalCoulombReferenceCore.attach N 1 (by norm_num) free, rfl⟩

theorem finite_joint_domain (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground)
    (u : Wave N)
    (hk : (normalEnergy N C κ hκ M hbound e B S).expectation
      ((B.realization (Wave N)).rank.rankOne u) < ⊤)
    (hr : (PhysicalPhotonMarginal.fullForm B volume
      (NormalPhoton.radiationForm B.normal (B.realization PhotonFock).functional)).expectation
      ((B.realization (Wave N)).rank.rankOne u) < ⊤) :
    (PhysicalPFReference.normalEnergy (Index N) (potential N) C κ hκ M hbound B S e).expectation
      ((B.realization (Wave N)).rank.rankOne u) < ⊤ := by
  obtain ⟨r, hr⟩ := (PhysicalSpatialRadiationDomain.fullRadiationForm_finite_iff volume B u).mp hr
  obtain ⟨d, hd⟩ := (normalEnergy_finite_graph N C κ hκ M hbound e B S u).mp hk
  exact (PhysicalPFRadiation.normalEnergy_rankOne_finite_iff (Index N) (potential N)
    C κ hκ M hbound B S e u).mpr
      (joint_domain_reference N C κ hκ M hbound e u d hd r hr)

end GptLean.PhysicalCovariantKinetic
