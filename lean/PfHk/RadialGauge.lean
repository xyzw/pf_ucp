import GptLean.PhysicalNonattainmentFluxKernel
import GptLean.WeylCoherentReal
import GptLean.WeylGraphDomains
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
The actual radial Pauli–Fierz Weyl label. The Bochner integral is taken
in the complete weighted one-photon space, so both field-bound moments
are retained. Its derivative along each ray is proved by the fundamental
theorem of calculus. Reality gives strong commutation with every physical
field, with no parity assumption on the polarization frame.
-/

noncomputable section
namespace PfHk.RadialGauge

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.PhysicalNonattainmentFluxKernel GptLean.SymmetricLift
  GptLean.Representability Gaussian
open scoped ENNReal InnerProductSpace Interval

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 500000

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (e : ℝ)

/-- The coupling label in `D_j = -i ∂_j + Φ(g_j)`. -/
def couplingKernel (j : Fin N × Fin 3) (X : Configuration N) : WeightedPhotonKernel :=
  (-e) • physicalKernel F χ j.2 (particle X j.1)

theorem couplingKernel_continuous (j : Fin N × Fin 3) :
    Continuous (couplingKernel F χ e j) := by
  unfold couplingKernel
  exact (continuous_const : Continuous (fun _ : Configuration N => (-e : ℝ))).smul ((physicalKernel_continuous F χ j.2).comp
    (particleLinear j.1).continuous_of_finiteDimensional)

theorem couplingKernel_fixed (j : Fin N × Fin 3) (X : Configuration N) :
    F.conjugation (couplingKernel F χ e j X).val.1 =
      (couplingKernel F χ e j X).val.1 :=
  real_smul_fixed F (-e) _ (physicalKernel_fixed F χ j.2 (particle X j.1))

/-- Contraction with the fixed ray direction. -/
def rayIntegrand (θ : Configuration N) (r : ℝ) : WeightedPhotonKernel :=
  ∑ j : Fin N × Fin 3, θ j • couplingKernel F χ e j (r • θ)

theorem rayIntegrand_continuous (θ : Configuration N) :
    Continuous (rayIntegrand F χ e θ) := by
  unfold rayIntegrand
  apply continuous_finsetSum
  intro j _
  exact (continuous_const : Continuous (fun _ : ℝ => θ j)).smul ((couplingKernel_continuous F χ e j).comp
    ((continuous_id : Continuous (fun r : ℝ => r)).smul continuous_const))

theorem rayIntegrand_fixed (θ : Configuration N) (r : ℝ) :
    F.conjugation (rayIntegrand F χ e θ r).val.1 =
      (rayIntegrand F χ e θ r).val.1 := by
  unfold rayIntegrand
  have h (s : Finset (Fin N × Fin 3)) :
      F.conjugation (∑ j ∈ s, θ j • couplingKernel F χ e j (r • θ)).val.1 =
        (∑ j ∈ s, θ j • couplingKernel F χ e j (r • θ)).val.1 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
      simp only [Finset.sum_insert hj]
      exact add_fixed F _ _
        (real_smul_fixed F _ _ (couplingKernel_fixed F χ e j _)) ih
  simpa using h Finset.univ

/-- `h_X = ∫₀¹ Σ_j X_j g_j(sX) ds`, in the weighted photon space. -/
def label (X : Configuration N) : WeightedPhotonKernel :=
  ∫ s in (0 : ℝ)..1, rayIntegrand F χ e X s

@[simp] theorem label_zero : label F χ e (0 : Configuration N) = 0 := by
  simp [label, rayIntegrand]

theorem label_fixed (X : Configuration N) :
    F.conjugation (label F χ e X).val.1 = (label F χ e X).val.1 :=
  integral_fixed F _ ((rayIntegrand_continuous F χ e X).intervalIntegrable _ _)
    (rayIntegrand_fixed F χ e X)

theorem rayIntegrand_smul (θ : Configuration N) (r s : ℝ) :
    rayIntegrand F χ e (r • θ) s = r • rayIntegrand F χ e θ (s * r) := by
  simp only [rayIntegrand, PiLp.smul_apply, smul_eq_mul, smul_smul, Finset.smul_sum]

/-- Reparametrization makes the radial derivative independent of spatial
coordinate differentiability of the field label. -/
theorem label_smul (θ : Configuration N) (r : ℝ) :
    label F χ e (r • θ) = ∫ s in (0 : ℝ)..r, rayIntegrand F χ e θ s := by
  unfold label
  simp_rw [rayIntegrand_smul]
  rw [intervalIntegral.integral_smul]
  simp

/-- The exact radial identity `∂ᵣ h_{rθ} = Σ θ_j g_j(rθ)`. -/
theorem label_radial_hasDerivAt (θ : Configuration N) (r : ℝ) :
    HasDerivAt (fun s : ℝ => label F χ e (s • θ)) (rayIntegrand F χ e θ r) r := by
  simp_rw [label_smul]
  exact intervalIntegral.integral_hasDerivAt_right
    ((rayIntegrand_continuous F χ e θ).intervalIntegrable 0 r)
    (rayIntegrand_continuous F χ e θ).stronglyMeasurable.stronglyMeasurableAtFilter
    (rayIntegrand_continuous F χ e θ).continuousAt

/-- In cylinder coordinates the derivative has the factor `-r`. -/
theorem label_logarithmic_hasDerivAt (θ : Configuration N) (t : ℝ) :
    HasDerivAt (fun s : ℝ => label F χ e (Real.exp (-s) • θ))
      ((-Real.exp (-t)) • rayIntegrand F χ e θ (Real.exp (-t))) t := by
  have ht : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    simpa only [Function.comp_def, mul_neg, mul_one] using
      (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_id t).neg
  simpa only [Function.comp_def] using (label_radial_hasDerivAt F χ e θ (Real.exp (-t))).scomp t ht

/-- All physical field labels have zero symplectic pairing. -/
theorem coupling_inner_im (j k : Fin N × Fin 3) (X Y : Configuration N) :
    (⟪(couplingKernel F χ e j X).val.1, (couplingKernel F χ e k Y).val.1⟫_ℂ).im = 0 :=
  realStructure_fixed_inner_im photonMeasure F.realStructure
    ⟨_, (F.realStructure.mem_fixedSpace _).mpr (couplingKernel_fixed F χ e j X)⟩ ⟨_, (F.realStructure.mem_fixedSpace _).mpr (couplingKernel_fixed F χ e k Y)⟩

/-- The integrated radial label commutes with every translated field. -/
theorem label_inner_im (j : Fin N × Fin 3) (X Y : Configuration N) :
    (⟪(label F χ e X).val.1, (couplingKernel F χ e j Y).val.1⟫_ℂ).im = 0 :=
  realStructure_fixed_inner_im photonMeasure F.realStructure
    ⟨_, (F.realStructure.mem_fixedSpace _).mpr (label_fixed F χ e X)⟩ ⟨_, (F.realStructure.mem_fixedSpace _).mpr (couplingKernel_fixed F χ e j Y)⟩

def unitary (W : ConcreteWeylLaw photonMeasure) (X : Configuration N) :
    PhotonFock ≃ₗᵢ[ℂ] PhotonFock :=
  W.weyl (Complex.I • (label F χ e X).val.1)

theorem unitary_field_groups_commute (W : ConcreteWeylLaw photonMeasure)
    (j : Fin N × Fin 3) (X Y : Configuration N) (s : ℝ) (u : PhotonFock) :
    unitary F χ e W X
        (W.weyl ((Complex.I * (s : ℂ)) • (couplingKernel F χ e j Y).val.1) u) =
      W.weyl ((Complex.I * (s : ℂ)) • (couplingKernel F χ e j Y).val.1)
        (unitary F χ e W X u) := by
  simpa only [unitary, Complex.ofReal_one, mul_one] using
    W.field_groups_commute photonMeasure _ _ (label_inner_im F χ e j X Y) s 1 u

/-- Conjugation preserves the maximal physical Segal graph with zero shift. -/
theorem unitary_field_graph_iff (W : ConcreteWeylLaw photonMeasure)
    (j : Fin N × Fin 3) (X Y : Configuration N) (u v : PhotonFock) :
    SegalGraph photonMeasure (couplingKernel F χ e j Y).val.1
      (unitary F χ e W X u) (unitary F χ e W X v) ↔
    SegalGraph photonMeasure (couplingKernel F χ e j Y).val.1 u v := by
  have hi : (⟪(couplingKernel F χ e j Y).val.1, (label F χ e X).val.1⟫_ℂ).im = 0 :=
    realStructure_fixed_inner_im photonMeasure F.realStructure
      ⟨_, (F.realStructure.mem_fixedSpace _).mpr (couplingKernel_fixed F χ e j Y)⟩ ⟨_, (F.realStructure.mem_fixedSpace _).mpr (label_fixed F χ e X)⟩
  simpa [unitary, inner_smul_right, Complex.mul_re, hi] using
    W.field_shift_iff photonMeasure (Complex.I • (label F χ e X).val.1)
      (couplingKernel F χ e j Y).val.1 u v

end PfHk.RadialGauge
