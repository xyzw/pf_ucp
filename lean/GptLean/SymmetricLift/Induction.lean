import GptLean.SymmetricLift.TensorSmooth
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.Basic

/-!
The finite block tensorization used by the particle-number induction.

This file recursively constructs tensor products of arbitrarily many local
operator families with different domain and target Hilbert spaces. It proves
their smoothness and isometry. It does not assume an already tensorized family.
Identifying these iterated products with completed unordered tensor powers and
proving the full particle-number construction are separate obligations.
-/

noncomputable section

namespace GptLean.SymmetricLift

open scoped TensorProduct ContDiff
open TopologicalSpace

instance tensorProduct_separable {A B : Type*}
    [NormedAddCommGroup A] [InnerProductSpace ℂ A] [SeparableSpace A]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] [SeparableSpace B] :
    SeparableSpace (A ⊗[ℂ] B) := by
  rw [← TopologicalSpace.isSeparable_univ_iff]
  have hs := (TopologicalSpace.isSeparable_range
    (TensorProduct.continuous_tmul (𝕜 := ℂ) (E := A) (F := B))).span (R := ℂ)
  have he : Set.range (fun p : A × B => p.1 ⊗ₜ[ℂ] p.2) =
      {z : A ⊗[ℂ] B | ∃ a b, a ⊗ₜ[ℂ] b = z} := by
    ext z
    simp only [Set.mem_range, Set.mem_setOf_eq]
    exact ⟨fun ⟨⟨a, b⟩, h⟩ => ⟨a, b, h⟩, fun ⟨a, b, h⟩ => ⟨(a, b), h⟩⟩
  rw [he, TensorProduct.span_tmul_eq_top] at hs
  exact hs

/-- A small bundle allows the iterated tensor product to carry its norm and
inner product during the recursion on blocks. Completeness is not asserted. -/
structure TensorHilbert where
  Carrier : Type
  normed : NormedAddCommGroup Carrier
  inner : @InnerProductSpace ℂ Carrier _ normed.toSeminormedAddCommGroup

attribute [instance] TensorHilbert.normed TensorHilbert.inner

instance : CoeSort TensorHilbert Type := ⟨TensorHilbert.Carrier⟩

abbrev TensorHilbert.of (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    TensorHilbert := ⟨H, inferInstance, inferInstance⟩

abbrev TensorHilbert.tensor (H K : TensorHilbert) : TensorHilbert :=
  ⟨H ⊗[ℂ] K, inferInstance, inferInstance⟩

theorem tensorMap_norm_of_isometry {A B C D : Type}
    [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B]
    [NormedAddCommGroup C] [InnerProductSpace ℂ C]
    [NormedAddCommGroup D] [InnerProductSpace ℂ D]
    (V : A →L[ℂ] B) (W : C →L[ℂ] D)
    (hV : ∀ u, ‖V u‖ = ‖u‖) (hW : ∀ u, ‖W u‖ = ‖u‖) (z : A ⊗[ℂ] C) :
    ‖TensorProduct.mapL V W z‖ = ‖z‖ := by
  let iV : A →ₗᵢ[ℂ] B := ⟨V.toLinearMap, hV⟩
  let iW : C →ₗᵢ[ℂ] D := ⟨W.toLinearMap, hW⟩
  change ‖TensorProduct.mapL iV.toContinuousLinearMap iW.toContinuousLinearMap z‖ = ‖z‖
  rw [← TensorProduct.toContinuousLinearMap_mapIsometry]
  exact (TensorProduct.mapIsometry iV iW).norm_map z

theorem tensorMapDerivative_tmul_metric {X A B C D : Type}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B]
    [NormedAddCommGroup C] [InnerProductSpace ℂ C]
    [NormedAddCommGroup D] [InnerProductSpace ℂ D]
    (V : A →L[ℂ] B) (W : C →L[ℂ] D)
    (dV : X →L[ℝ] (A →L[ℂ] B)) (dW : X →L[ℝ] (C →L[ℂ] D))
    (d : X) (u : A) (v : C) (hVu : ‖V u‖ = 1) (hWv : ‖W v‖ = 1)
    (hflat : inner ℂ (V u) (dV d u) = 0) :
    ‖tensorMapDerivative V W dV dW d (u ⊗ₜ[ℂ] v)‖ ^ 2 =
      ‖dV d u‖ ^ 2 + ‖dW d v‖ ^ 2 := by
  rw [tensorMapDerivative_apply, ContinuousLinearMap.add_apply,
    TensorProduct.mapL_tmul, TensorProduct.mapL_tmul, norm_add_sq (𝕜 := ℂ)]
  simp [TensorProduct.inner_tmul, hflat, hVu, hWv, add_comm]

variable {ι X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable (H K : ι → Type)
  [∀ a, NormedAddCommGroup (H a)] [∀ a, InnerProductSpace ℂ (H a)]
  [∀ a, NormedAddCommGroup (K a)] [∀ a, InnerProductSpace ℂ (K a)]

/-- Ordered iterated tensor products, with the scalar field as empty product. -/
def BlockTensor : List ι → TensorHilbert
  | [] => TensorHilbert.of ℂ
  | a :: s => (TensorHilbert.of (H a)).tensor (BlockTensor s)

theorem blockTensor_finiteDimensional [∀ a, FiniteDimensional ℂ (H a)] (s : List ι) :
    FiniteDimensional ℂ (BlockTensor H s) := by
  induction s with
  | nil => exact inferInstanceAs (FiniteDimensional ℂ ℂ)
  | cons a s ih =>
    letI := ih
    exact inferInstanceAs (FiniteDimensional ℂ (H a ⊗[ℂ] BlockTensor H s))

theorem blockTensor_separable [∀ a, SeparableSpace (H a)] (s : List ι) :
    SeparableSpace (BlockTensor H s) := by
  induction s with
  | nil => exact inferInstanceAs (SeparableSpace ℂ)
  | cons a s ih =>
    letI := ih
    exact inferInstanceAs (SeparableSpace (H a ⊗[ℂ] BlockTensor H s))

/-- A constructive finite recursion, applied to the lower-particle local maps. -/
def blockTensorFamily (V : ∀ a, X → H a →L[ℂ] K a) :
    (s : List ι) → X → BlockTensor H s →L[ℂ] BlockTensor K s
  | [], _ => ContinuousLinearMap.id ℂ ℂ
  | a :: s, x => TensorProduct.mapL (V a x) (blockTensorFamily V s x)

def blockTensorVector (t : ∀ a, H a) : (s : List ι) → BlockTensor H s
  | [] => (1 : ℂ)
  | a :: s => t a ⊗ₜ[ℂ] blockTensorVector t s

theorem blockTensorVector_unit (t : ∀ a, H a) (ht : ∀ a, ‖t a‖ = 1) (s : List ι) :
    ‖blockTensorVector H t s‖ = 1 := by
  induction s with
  | nil => change ‖(1 : ℂ)‖ = 1; exact norm_one
  | cons a s ih =>
    change ‖t a ⊗ₜ[ℂ] blockTensorVector H t s‖ = 1
    rw [TensorProduct.norm_tmul, ht a, ih, one_mul]

theorem blockTensorFamily_contDiffOn (V : ∀ a, X → H a →L[ℂ] K a)
    {O : Set X} (hV : ∀ a, ContDiffOn ℝ ∞ (V a) O) (s : List ι) :
    ContDiffOn ℝ ∞ (blockTensorFamily H K V s) O := by
  induction s with
  | nil => exact contDiffOn_const
  | cons a s ih =>
    exact tensorMap_contDiffOn (H := H a) (K := K a)
      (E := BlockTensor H s) (F := BlockTensor K s) (hV a) ih

theorem blockTensorFamily_const_eq {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (C : ∀ a, H a →L[ℂ] K a) (s : List ι) (x : X) (y : Y) :
    blockTensorFamily H K (fun a (_ : X) => C a) s x =
      blockTensorFamily H K (fun a (_ : Y) => C a) s y := by
  induction s with
  | nil => rfl
  | cons a s ih => change TensorProduct.mapL (C a) _ = TensorProduct.mapL (C a) _; rw [ih]

theorem blockTensorFamily_norm (V : ∀ a, X → H a →L[ℂ] K a)
    {x : X} (hV : ∀ a u, ‖V a x u‖ = ‖u‖) (s : List ι)
    (z : BlockTensor H s) : ‖blockTensorFamily H K V s x z‖ = ‖z‖ := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    exact tensorMap_norm_of_isometry (V a x) (blockTensorFamily H K V s x) (hV a) ih z

/-- Explicit recursive product-rule derivative of every finite block family. -/
def blockTensorDerivative (V : ∀ a, X → H a →L[ℂ] K a)
    (dV : ∀ a, X → X →L[ℝ] (H a →L[ℂ] K a)) :
    (s : List ι) → X → X →L[ℝ] (BlockTensor H s →L[ℂ] BlockTensor K s)
  | [], _ => 0
  | a :: s, x => tensorMapDerivative (V a x) (blockTensorFamily H K V s x)
      (dV a x) (blockTensorDerivative V dV s x)

theorem blockTensorFamily_hasFDerivAt (V : ∀ a, X → H a →L[ℂ] K a)
    (dV : ∀ a, X → X →L[ℝ] (H a →L[ℂ] K a)) {x : X}
    (hV : ∀ a, HasFDerivAt (V a) (dV a x) x) (s : List ι) :
    HasFDerivAt (blockTensorFamily H K V s) (blockTensorDerivative H K V dV s x) x := by
  induction s with
  | nil => exact hasFDerivAt_const _ _
  | cons a s ih => exact tensorMap_hasFDerivAt (hV a) ih

theorem blockTensorDerivative_flat (V : ∀ a, X → H a →L[ℂ] K a)
    (dV : ∀ a, X → X →L[ℝ] (H a →L[ℂ] K a)) {x : X}
    (hV : ∀ a d u v, inner ℂ (V a x u) (dV a x d v) = 0)
    (s : List ι) (d : X) (u v : BlockTensor H s) :
    inner ℂ (blockTensorFamily H K V s x u) (blockTensorDerivative H K V dV s x d v) = 0 := by
  induction s generalizing d with
  | nil => simp [blockTensorDerivative]
  | cons a s ih =>
    exact tensorMapDerivative_flat (V a x) (blockTensorFamily H K V s x)
      (dV a x) (blockTensorDerivative H K V dV s x) (hV a) ih d u v

/-- Orthogonality of the differentiated tensor factors gives the exact
finite-block metric, without a factor depending on the number of blocks. -/
theorem blockTensorDerivative_metric (V : ∀ a, X → H a →L[ℂ] K a)
    (dV : ∀ a, X → X →L[ℝ] (H a →L[ℂ] K a)) {x : X}
    (hiso : ∀ a u, ‖V a x u‖ = ‖u‖)
    (hflat : ∀ a d u v, inner ℂ (V a x u) (dV a x d v) = 0)
    (t : ∀ a, H a) (ht : ∀ a, ‖t a‖ = 1) (s : List ι) (d : X) :
    ‖blockTensorDerivative H K V dV s x d (blockTensorVector H t s)‖ ^ 2 =
      (s.map (fun a => ‖dV a x d (t a)‖ ^ 2)).sum := by
  induction s with
  | nil => simp [blockTensorDerivative]
  | cons a s ih =>
    change ‖tensorMapDerivative (V a x) (blockTensorFamily H K V s x)
      (dV a x) (blockTensorDerivative H K V dV s x) d
      (t a ⊗ₜ[ℂ] blockTensorVector H t s)‖ ^ 2 = _
    rw [tensorMapDerivative_tmul_metric]
    · simpa only [List.map_cons, List.sum_cons] using congrArg (fun z => ‖dV a x d (t a)‖ ^ 2 + z) ih
    · rw [hiso, ht]
    · rw [blockTensorFamily_norm H K V hiso, blockTensorVector_unit H t ht]
    · exact hflat a d (t a) (t a)

/-- Constancy on each block's projected subspace tensorizes through the
actual recursively constructed operators. -/
theorem blockTensorFamily_fixed (V : ∀ a, X → H a →L[ℂ] K a)
    (P : ∀ a, H a →L[ℂ] H a) (C : ∀ a, H a →L[ℂ] K a) {x : X}
    (hfixed : ∀ a u, V a x (P a u) = C a u) (s : List ι) :
    (blockTensorFamily H K V s x).comp
      (blockTensorFamily H H (fun a _ => P a) s x) =
        blockTensorFamily H K (fun a _ => C a) s x := by
  induction s with
  | nil => ext u; rfl
  | cons a s ih =>
    change (TensorProduct.mapL (V a x) (blockTensorFamily H K V s x)).comp
      (TensorProduct.mapL (P a) (blockTensorFamily H H (fun a _ => P a) s x)) = _
    rw [← TensorProduct.mapL_comp, ih]
    have ha : (V a x).comp (P a) = C a := by ext u; exact hfixed a u
    rw [ha]
    rfl

/-- The local stabilizer covariance tensorizes block by block. -/
theorem blockTensorFamily_equivariant (V : ∀ a, X → H a →L[ℂ] K a)
    (R : ∀ a, H a →L[ℂ] H a) (x y : X)
    (hV : ∀ a u, V a y (R a u) = V a x u) (s : List ι) :
    (blockTensorFamily H K V s y).comp
      (blockTensorFamily H H (fun a _ => R a) s x) = blockTensorFamily H K V s x := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    change (TensorProduct.mapL (V a y) (blockTensorFamily H K V s y)).comp
      (TensorProduct.mapL (R a) (blockTensorFamily H H (fun a _ => R a) s x)) = _
    rw [← TensorProduct.mapL_comp, ih]
    have ha : (V a y).comp (R a) = V a x := by ext u; exact hV a u
    rw [ha]
    rfl

end GptLean.SymmetricLift
