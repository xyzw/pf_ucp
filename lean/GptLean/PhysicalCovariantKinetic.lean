import GptLean.PhysicalPFCovariantSymmetry
import GptLean.PhysicalCoulombReferenceCore
import GptLean.PhysicalSymmetricFamilyClosure

/-!
The physical kinetic form is obtained from the closure of the actual
covariant derivative tuple on the dense Coulomb reference domain.
-/

noncomputable section

namespace GptLean.PhysicalCovariantKinetic

open MeasureTheory PhysicalFock PhysicalPFReference PhysicalNormalTrace PhysicalClosedForms
open scoped InnerProductSpace ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000
set_option Elab.async false

private theorem real_scale_symmetric {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (a : ℝ) (u v fu fv : H) (h : ⟪u, fv⟫_ℂ = ⟪fu, v⟫_ℂ) :
    ⟪(a : ℂ) • fu, v⟫_ℂ = ⟪u, (a : ℂ) • fv⟫_ℂ := by
  simp only [inner_smul_left, inner_smul_right, Complex.conj_ofReal, h]

private theorem half_norm_sq {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (u : H) : ‖(Real.sqrt (1 / 2 : ℝ) : ℂ) • u‖ ^ 2 = (1 / 2 : ℝ) * ‖u‖ ^ 2 := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (by norm_num)]

abbrev Index (N : ℕ) := Fin N × Fin 3
def potential (N : ℕ) : Position (Index N) → ℝ :=
  fun x => 1 * PhysicalCoulombH1.potential N x
abbrev Reference (N : ℕ) := PhysicalPFReference.Reference (Index N) (potential N)
abbrev Wave (N : ℕ) := WaveSpace (Index N)
abbrev Output (N : ℕ) := PiLp 2 (fun _ : Index N => Wave N)

variable (N : ℕ) (C : CanonicalSectorCCR photonMeasure)
  (κ : Index N → Position (Index N) → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)

local instance referenceModule : Module ℂ (Reference N) :=
  (referenceNormedSpace (Index N) (potential N)).toModule

local instance referenceSMul : SMul ℂ (Reference N) := (referenceModule N).toSMul

def family (i : Index N) : Reference N →L[ℂ] Wave N :=
  (Real.sqrt (1 / 2 : ℝ) : ℂ) •
    covariant (Index N) (potential N) C κ hκ M hbound e i

theorem family_symmetric (i : Index N) (u v : Reference N) :
    ⟪family N C κ hκ M hbound e i u, inclusion (Index N) (potential N) v⟫_ℂ =
      ⟪inclusion (Index N) (potential N) u, family N C κ hκ M hbound e i v⟫_ℂ :=
  real_scale_symmetric (Real.sqrt (1 / 2 : ℝ)) _ _ _ _
    (covariant_symmetric (Index N) (potential N) C κ hκ M hbound e i u v)

theorem value_dense : DenseRange (inclusion (Index N) (potential N)) :=
  PhysicalCoulombReferenceCore.inclusion_denseRange N 1 (by norm_num)

def output : Reference N →L[ℂ] Output N :=
  PhysicalSymmetricFamilyClosure.tupleOutput (E := Reference N) (H := Wave N)
    (I := Index N) (family N C κ hκ M hbound e)

def operator : Wave N →ₗ.[ℂ] Output N :=
  PhysicalSymmetricFamilyClosure.operator (E := Reference N) (H := Wave N) (I := Index N)
    (inclusion (Index N) (potential N))
    (family N C κ hκ M hbound e)

theorem operator_closed : (operator N C κ hκ M hbound e).IsClosed :=
  PhysicalSymmetricFamilyClosure.operator_closed (E := Reference N) (H := Wave N)
    (I := Index N) _ _ (value_dense N)
    (family_symmetric N C κ hκ M hbound e)

theorem operator_graph : (operator N C κ hκ M hbound e).graph =
    PhysicalSymmetricFamilyClosure.closedGraph (E := Reference N) (H := Wave N)
      (I := Index N) (inclusion (Index N) (potential N)) (family N C κ hκ M hbound e) :=
  PhysicalSymmetricFamilyClosure.operator_graph (E := Reference N) (H := Wave N)
    (I := Index N) _ _ (value_dense N) (family_symmetric N C κ hκ M hbound e)

theorem reference_graph (u : Reference N) :
    (inclusion (Index N) (potential N) u, output N C κ hκ M hbound e u) ∈
      ((operator N C κ hκ M hbound e).graph : Set (Wave N × Output N)) := by
  have h := (PhysicalSymmetricFamilyClosure.graphMap (E := Reference N) (H := Wave N)
    (I := Index N) (inclusion (Index N) (potential N))
    (family N C κ hκ M hbound e)).range.le_topologicalClosure
      ⟨u, rfl⟩
  exact (congrArg (fun L : Submodule ℂ (Wave N × Output N) =>
    (inclusion (Index N) (potential N) u, output N C κ hκ M hbound e u) ∈ L)
      (operator_graph N C κ hκ M hbound e)).mpr h

theorem output_norm_sq (u : Reference N) :
    ‖output N C κ hκ M hbound e u‖ ^ 2 =
      kineticEnergy (Index N) (potential N) C κ hκ M hbound e u := by
  have h := PhysicalSymmetricFamilyClosure.original_energy (E := Reference N) (H := Wave N)
    (I := Index N)
    (family N C κ hκ M hbound e) u
  exact h.trans (by
    simp only [family, smul_apply, half_norm_sq,
      ← Finset.mul_sum, kineticEnergy])

theorem graph_test (u : Wave N) (w : Output N)
    (hw : (u, w) ∈ (operator N C κ hκ M hbound e).graph)
    (i : Index N) (v : Reference N) :
    ⟪w i, inclusion (Index N) (potential N) v⟫_ℂ =
      ⟪u, family N C κ hκ M hbound e i v⟫_ℂ := by
  have hz : (u, w) ∈
      PhysicalSymmetricFamilyClosure.closedGraph (E := Reference N) (H := Wave N)
        (I := Index N) (inclusion (Index N) (potential N)) (family N C κ hκ M hbound e) := by
    exact (congrArg (fun L : Submodule ℂ (Wave N × Output N) =>
      (u, w) ∈ L) (operator_graph N C κ hκ M hbound e)).mp hw
  have hc : IsClosed {z : Wave N × Output N |
      ⟪z.2 i, inclusion (Index N) (potential N) v⟫_ℂ =
        ⟪z.1, family N C κ hκ M hbound e i v⟫_ℂ} :=
    isClosed_eq (((PiLp.continuous_apply 2 _ i).comp continuous_snd).inner continuous_const)
      (continuous_fst.inner continuous_const)
  apply closure_minimal (t := {z : Wave N × Output N |
      ⟪z.2 i, inclusion (Index N) (potential N) v⟫_ℂ =
        ⟪z.1, family N C κ hκ M hbound e i v⟫_ℂ}) _ hc hz
  rintro _ ⟨q, rfl⟩
  exact family_symmetric N C κ hκ M hbound e i q v

variable (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground)

def normalEnergy : RemovalState.PositiveForm (B.traceData (H := Wave N)) :=
  PhysicalClosedForms.positiveForm
    (S.resolve (Wave N) (Output N) (operator N C κ hκ M hbound e)
      (operator_closed N C κ hκ M hbound e))
    B.normal (B.realization (Wave N)).functional

theorem normalEnergy_reference (u : Reference N) :
    (normalEnergy N C κ hκ M hbound e B S).expectation
      ((B.realization (Wave N)).rank.rankOne (inclusion (Index N) (potential N) u)) =
      ENNReal.ofReal (kineticEnergy (Index N) (potential N) C κ hκ M hbound e u) :=
  (PhysicalClosedForms.positiveForm_graph _ _ _ _ _
    (reference_graph N C κ hκ M hbound e u)).trans
      (congrArg ENNReal.ofReal (output_norm_sq N C κ hκ M hbound e u))

theorem normalEnergy_finite_iff (v : Wave N) :
    (normalEnergy N C κ hκ M hbound e B S).expectation
      ((B.realization (Wave N)).rank.rankOne v) < ⊤ ↔
      v ∈ (operator N C κ hκ M hbound e).domain :=
  PhysicalClosedForms.positiveForm_finite_iff _ _ _ v

theorem normalEnergy_finite_graph (v : Wave N) :
    (normalEnergy N C κ hκ M hbound e B S).expectation
      ((B.realization (Wave N)).rank.rankOne v) < ⊤ ↔
      ∃ w : Output N, (v, w) ∈ (operator N C κ hκ M hbound e).graph :=
  (normalEnergy_finite_iff N C κ hκ M hbound e B S v).trans LinearPMap.mem_domain_iff

end GptLean.PhysicalCovariantKinetic
