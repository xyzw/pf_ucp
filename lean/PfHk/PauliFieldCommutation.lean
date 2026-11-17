import PfHk.CommutingUnitaryGenerators
import GptLean.WeylGraphDomains
import GptLean.WeylPhaseFinite
import GptLean.PhysicalFockFieldSymmetry

/-! Weak commutation of the actual Segal fields with real mutual kernel
pairing. Commuting Weyl groups supply the finite-number identity, which
extends by continuity in the actual radiation graph norm. -/

noncomputable section
namespace PfHk.PauliFieldCommutation

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.Representability
  GptLean.PhysicalWeyl GptLean.WeylPhase
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000

section General
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]
  (W : ConcreteWeylLaw μ)

def orbit (f : Lp ℂ 2 μ) (t : ℝ) : Fock μ ≃ₗᵢ[ℂ] Fock μ :=
  W.weyl (t • (Complex.I • f))

theorem orbit_inner (f : Lp ℂ 2 μ) (t : ℝ) (u v : Fock μ) :
    inner ℂ (orbit μ W f t u) v = inner ℂ u (orbit μ W f (-t) v) := by
  simpa only [orbit, neg_smul] using inner_weyl W (t • (Complex.I • f)) u v

omit [SigmaFinite μ] in
private theorem label (f : Lp ℂ 2 μ) (t : ℝ) :
    t • (Complex.I • f) = (Complex.I * (t : ℂ)) • f := by
  rw [mul_comm Complex.I, ← Complex.real_smul]
  exact (smul_assoc t Complex.I f).symm

theorem orbit_commute (f g : Lp ℂ 2 μ) (hreal : (inner ℂ f g).im = 0)
    (s t : ℝ) (u : Fock μ) :
    orbit μ W f t (orbit μ W g s u) = orbit μ W g s (orbit μ W f t u) := by
  simpa only [orbit, label] using W.field_groups_commute μ f g hreal s t u

theorem orbit_cross_pairing (f g : Lp ℂ 2 μ) (hreal : (inner ℂ f g).im = 0)
    (s t : ℝ) (u v : Fock μ) :
    inner ℂ (orbit μ W f t u) (orbit μ W g s v) =
      inner ℂ (orbit μ W g (-s) u) (orbit μ W f (-t) v) := by
  have hneg := orbit_inner μ W g (-s) (orbit μ W f t u) v
  rw [neg_neg] at hneg
  calc
    _ = inner ℂ (orbit μ W g (-s) (orbit μ W f t u)) v := hneg.symm
    _ = inner ℂ (orbit μ W f t (orbit μ W g (-s) u)) v :=
      congrArg (fun z => inner ℂ z v) (orbit_commute μ W f g hreal (-s) t u).symm
    _ = _ := orbit_inner μ W f t (orbit μ W g (-s) u) v

def finiteField (M : ℕ) (f : Lp ℂ 2 μ) (u : Fock μ) : Fock μ :=
  creationFinite μ M f u + annihilationFinite μ M f u

theorem orbit_derivative (M : ℕ) (f : Lp ℂ 2 μ) (u : Fock μ)
    (hu : FiniteNumberSupport μ M u) :
    HasDerivAt (fun t : ℝ => orbit μ W f t u) (Complex.I • finiteField μ M f u) 0 := by
  simpa only [orbit, finiteField, zero_smul, W.zero, LinearIsometryEquiv.coe_refl, id_eq] using
    imaginary_orbit_derivative μ W M f u hu 0

include W in
theorem finite_pairing (f g : Lp ℂ 2 μ) (hreal : (inner ℂ f g).im = 0)
    (M L : ℕ) (u v : Fock μ)
    (hu : FiniteNumberSupport μ M u) (hv : FiniteNumberSupport μ L v) :
    inner ℂ (finiteField μ M f u) (finiteField μ L g v) =
      inner ℂ (finiteField μ M g u) (finiteField μ L f v) := by
  have h := CommutingUnitaryGenerators.paired_derivatives
    (H := Fock μ) (fun t u => orbit μ W f t u) (fun t u => orbit μ W g t u)
    u v (Complex.I • finiteField μ M f u) (Complex.I • finiteField μ L f v)
    (Complex.I • finiteField μ M g u) (Complex.I • finiteField μ L g v)
    (fun s t => orbit_cross_pairing μ W f g hreal s t u v)
    (orbit_derivative μ W M f u hu) (orbit_derivative μ W L f v hv)
    (orbit_derivative μ W M g u hu) (orbit_derivative μ W L g v hv)
  simpa only [inner_smul_left, inner_smul_right, Complex.conj_I,
    mul_neg, ← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul] using h

end General

private theorem l2_inner_eq_of_ae {X H : Type*} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (a b c d : Lp H 2 μ)
    (h : ∀ᵐ x ∂μ, inner ℂ (a x) (b x) = inner ℂ (c x) (d x)) :
    inner ℂ a b = inner ℂ c d := by
  rw [L2.inner_def, L2.inner_def]
  exact integral_congr_ae h

variable (C : CanonicalSectorCCR photonMeasure) (W : ConcreteWeylLaw photonMeasure)

theorem kernelField_eq_finite (k : WeightedPhotonKernel) (q : RadiationGraphSpace)
    (M : ℕ) (hq : FiniteNumberSupport photonMeasure M (radiationGraphInclusion q)) :
    kernelField C k q = finiteField photonMeasure M k.val.1 (radiationGraphInclusion q) :=
  segalGraph_unique photonMeasure k.val.1 (kernelField_segalGraph C k q)
    (finite_segalGraph photonMeasure M k.val.1 (radiationGraphInclusion q) hq)

attribute [local irreducible] kernelField finiteField

include W in
theorem core_pairing (k l : WeightedPhotonKernel)
    (hreal : (inner ℂ (E := Lp ℂ 2 photonMeasure) k.val.1 l.val.1).im = 0) (q r : RadiationGraphSpace)
    (hq : q ∈ radiationGraphCore) (hr : r ∈ radiationGraphCore) :
    inner ℂ (E := PhotonFock) (kernelField C k q) (kernelField C l r) =
      inner ℂ (E := PhotonFock) (kernelField C l q) (kernelField C k r) := by
  have hq' : ∃ M, FiniteNumberSupport photonMeasure M (radiationGraphInclusion q) := hq
  have hr' : ∃ L, FiniteNumberSupport photonMeasure L (radiationGraphInclusion r) := hr
  obtain ⟨M, hM⟩ := hq'
  obtain ⟨L, hL⟩ := hr'
  have hleft := congrArg₂ (inner ℂ (E := PhotonFock))
    (kernelField_eq_finite C k q M hM) (kernelField_eq_finite C l r L hL)
  have hright := congrArg₂ (inner ℂ (E := PhotonFock))
    (kernelField_eq_finite C l q M hM) (kernelField_eq_finite C k r L hL)
  exact hleft.trans ((finite_pairing photonMeasure W k.val.1 l.val.1 hreal M L
    (radiationGraphInclusion q) (radiationGraphInclusion r) hM hL).trans hright.symm)

include W in
/-- Weak commutation on the full square-root radiation domain. -/
theorem kernelField_pairing (k l : WeightedPhotonKernel)
    (hreal : (inner ℂ (E := Lp ℂ 2 photonMeasure) k.val.1 l.val.1).im = 0) (q r : RadiationGraphSpace) :
    inner ℂ (E := PhotonFock) (kernelField C k q) (kernelField C l r) =
      inner ℂ (E := PhotonFock) (kernelField C l q) (kernelField C k r) := by
  have hc : IsClosed {p : RadiationGraphSpace × RadiationGraphSpace |
      inner ℂ (E := PhotonFock) (kernelField C k p.1) (kernelField C l p.2) =
        inner ℂ (E := PhotonFock) (kernelField C l p.1) (kernelField C k p.2)} :=
    isClosed_eq (((kernelField C k).continuous.comp continuous_fst).inner
      ((kernelField C l).continuous.comp continuous_snd))
      (((kernelField C l).continuous.comp continuous_fst).inner
        ((kernelField C k).continuous.comp continuous_snd))
  have hsubset : (radiationGraphCore : Set RadiationGraphSpace).prod
      (radiationGraphCore : Set RadiationGraphSpace) ⊆
      {p : RadiationGraphSpace × RadiationGraphSpace |
        inner ℂ (E := PhotonFock) (kernelField C k p.1) (kernelField C l p.2) =
          inner ℂ (E := PhotonFock) (kernelField C l p.1) (kernelField C k p.2)} := by
    intro p hp
    exact core_pairing C W k l hreal p.1 p.2 hp.1 hp.2
  exact (closure_minimal hsubset hc)
    ((radiationGraphCore_dense.prod radiationGraphCore_dense) (q, r))

include W in
/-- The pointwise identity integrates to the actual spatial field maps. -/
theorem spatialField_pairing {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (κ η : X → WeightedPhotonKernel)
    (hκ : AEStronglyMeasurable κ μ) (hη : AEStronglyMeasurable η μ)
    (M L : ℝ) (hM : ∀ᵐ x ∂μ, ‖κ x‖ ≤ M) (hL : ∀ᵐ x ∂μ, ‖η x‖ ≤ L)
    (hreal : ∀ᵐ x ∂μ, (inner ℂ (E := Lp ℂ 2 photonMeasure) (κ x).val.1 (η x).val.1).im = 0)
    (q r : SpatialRadiationGraph μ) :
    inner ℂ (E := Lp PhotonFock 2 μ) (spatialField μ C κ hκ M hM q) (spatialField μ C η hη L hL r) =
      inner ℂ (E := Lp PhotonFock 2 μ) (spatialField μ C η hη L hL q) (spatialField μ C κ hκ M hM r) := by
  apply l2_inner_eq_of_ae (H := PhotonFock) (μ := μ)
    (spatialField μ C κ hκ M hM q) (spatialField μ C η hη L hL r)
    (spatialField μ C η hη L hL q) (spatialField μ C κ hκ M hM r)
  filter_upwards [spatialField_ae μ C κ hκ M hM q,
    spatialField_ae μ C η hη L hL r, spatialField_ae μ C η hη L hL q,
    spatialField_ae μ C κ hκ M hM r, hreal] with x hkq hlr hlq hkr hx
  exact (congrArg₂ (inner ℂ (E := PhotonFock)) hkq hlr).trans
    ((kernelField_pairing C W (κ x) (η x) hx (q x) (r x)).trans
      (congrArg₂ (inner ℂ (E := PhotonFock)) hlq.symm hkr.symm))

end PfHk.PauliFieldCommutation
