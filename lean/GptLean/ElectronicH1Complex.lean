import GptLean.ElectronicH1Space
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
The complex structure on the same electronic weak-derivative graph.
The graph norm is the maximum product norm, so this is a complex Banach
space. Its real linear isometry to the real graph preserves the value
and every derivative and transports the smooth-core and Sobolev results.
-/

noncomputable section

namespace GptLean.ElectronicH1Complex

open MeasureTheory GptLean.SymmetricLift GptLean.Repair
open scoped ENNReal

/-- The same weak coordinate identities, closed under complex scalars. -/
def complexWeakGraph (E I : Type*) [Fintype I] [DecidableEq I]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] [CompleteSpace E] :
    Submodule ℂ (ElectronicH1Space.L2 E I × (I → ElectronicH1Space.L2 E I)) where
  carrier := ElectronicH1Space.weakGraph E I
  zero_mem' := (ElectronicH1Space.weakGraph E I).zero_mem
  add_mem' := (ElectronicH1Space.weakGraph E I).add_mem
  smul_mem' := by
    intro c u hu
    have h := weakH1Local_map ((c • ContinuousLinearMap.id ℂ E).restrictScalars ℝ) hu
    exact h.congr (Lp.coeFn_smul c u.1).symm
      (fun i => (Lp.coeFn_smul c (u.2 i)).symm)

/-- The actual complex electronic H1 reference space with its Banach graph norm. -/
abbrev ComplexH1 (E I : Type*) [Fintype I] [DecidableEq I]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] [CompleteSpace E] :=
  ↥(complexWeakGraph E I)

variable {I E : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] [CompleteSpace E]

theorem isClosed_complexWeakGraph :
    IsClosed (complexWeakGraph E I :
      Set (ElectronicH1Space.L2 E I × (I → ElectronicH1Space.L2 E I))) :=
  ElectronicH1Space.isClosed_weakGraph

instance instCompleteSpace : CompleteSpace (ComplexH1 E I) :=
  isClosed_complexWeakGraph.completeSpace_coe

def value : ComplexH1 E I →L[ℂ] ElectronicH1Space.L2 E I :=
  (ContinuousLinearMap.fst ℂ (ElectronicH1Space.L2 E I)
    (I → ElectronicH1Space.L2 E I)).comp (complexWeakGraph E I).subtypeL

def gradient : ComplexH1 E I →L[ℂ] (I → ElectronicH1Space.L2 E I) :=
  (ContinuousLinearMap.snd ℂ (ElectronicH1Space.L2 E I)
    (I → ElectronicH1Space.L2 E I)).comp (complexWeakGraph E I).subtypeL

def derivative (i : I) : ComplexH1 E I →L[ℂ] ElectronicH1Space.L2 E I :=
  (ContinuousLinearMap.proj i).comp gradient

@[simp] theorem value_apply (u : ComplexH1 E I) : value u = u.val.1 := rfl
@[simp] theorem gradient_apply (u : ComplexH1 E I) : gradient u = u.val.2 := rfl
@[simp] theorem derivative_apply (i : I) (u : ComplexH1 E I) :
    derivative i u = u.val.2 i := rfl

/-- Restricting scalars does not change the functions, derivatives, or norm. -/
def realEquiv : ComplexH1 E I ≃ₗᵢ[ℝ] ElectronicH1Space.H1 E I where
  toFun u := ⟨u.val, u.property⟩
  invFun u := ⟨u.val, u.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

@[simp] theorem value_realEquiv (u : ComplexH1 E I) :
    ElectronicH1Space.value (realEquiv u) = value u := rfl

@[simp] theorem gradient_realEquiv (u : ComplexH1 E I) :
    ElectronicH1Space.gradient (realEquiv u) = gradient u := rfl

@[simp] theorem derivative_realEquiv (i : I) (u : ComplexH1 E I) :
    ElectronicH1Space.derivative i (realEquiv u) = derivative i u := rfl

@[simp] theorem value_realEquiv_symm (u : ElectronicH1Space.H1 E I) :
    value ((realEquiv (E := E) (I := I)).symm u) = ElectronicH1Space.value u := rfl

@[simp] theorem derivative_realEquiv_symm (i : I) (u : ElectronicH1Space.H1 E I) :
    derivative i ((realEquiv (E := E) (I := I)).symm u) =
      ElectronicH1Space.derivative i u := rfl

theorem value_restrictScalars :
    (value (E := E) (I := I)).restrictScalars ℝ =
      ElectronicH1Space.value.comp
        (realEquiv (E := E) (I := I)).toLinearIsometry.toContinuousLinearMap := by
  ext u
  rfl

theorem derivative_restrictScalars (i : I) :
    (derivative (E := E) i).restrictScalars ℝ =
      (ElectronicH1Space.derivative i).comp
        (realEquiv (E := E) (I := I)).toLinearIsometry.toContinuousLinearMap := by
  ext u
  rfl

theorem weak (u : ComplexH1 E I) :
    HasWeakH1Local (fun x => value u x) (fun i x => derivative i u x) := u.property

theorem norm_eq_max (u : ComplexH1 E I) : ‖u‖ = max ‖value u‖ ‖gradient u‖ := rfl

theorem norm_value_le (u : ComplexH1 E I) : ‖value u‖ ≤ ‖u‖ :=
  _root_.norm_fst_le u.val

theorem norm_gradient_le (u : ComplexH1 E I) : ‖gradient u‖ ≤ ‖u‖ :=
  _root_.norm_snd_le u.val

theorem norm_derivative_le (u : ComplexH1 E I) (i : I) : ‖derivative i u‖ ≤ ‖u‖ :=
  (norm_le_pi_norm (gradient u) i).trans (norm_gradient_le u)

theorem value_injective : Function.Injective (value (E := E) (I := I)) := by
  intro u v h
  apply (realEquiv (E := E) (I := I)).injective
  exact ElectronicH1Space.value_injective h

theorem ext_ae {u v : ComplexH1 E I}
    (h : (value u : EuclideanSpace ℝ I → E) =ᵐ[volume] value v) : u = v :=
  value_injective (Lp.ext h)

/-- Transport any dense real core to this complex reference graph. -/
theorem dense_preimage_realEquiv {s : Set (ElectronicH1Space.H1 E I)} (hs : Dense s) :
    Dense ((realEquiv (E := E) (I := I)) ⁻¹' s : Set (ComplexH1 E I)) :=
  hs.preimage (realEquiv (E := E) (I := I)).toHomeomorph.isOpenMap

end GptLean.ElectronicH1Complex
