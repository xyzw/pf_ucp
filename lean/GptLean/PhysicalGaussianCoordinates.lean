import GptLean.PhysicalFockHardSoftVacuum
import GptLean.PhysicalL2HilbertSum
import GptLean.PhysicalSectorCoordinates
import GptLean.Gaussian.CovariantSlicing

/-!
Constructed tensor and spatial coordinates for a scalar Gaussian realization.
A scalar soft-Fock unitary determines the full photon unitary and the
spatial product-space map. Their representative and Fubini identities are
proved on the same L² classes. This module does not supply the scalar WIS
theorem or the unbounded field intertwining.
-/

noncomputable section

namespace GptLean.PhysicalGaussianCoordinates

open MeasureTheory Filter Topology PhysicalFock
open PhysicalFock.TensorCoordinates
open scoped ENNReal InnerProductSpace TensorProduct

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

section Completion

variable {H K : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup K] [NormedSpace ℂ K]

private theorem completion_inverse (U : H ≃ₗᵢ[ℂ] K)
    (x : UniformSpace.Completion H) :
    U.symm.toLinearIsometry.completion (U.toLinearIsometry.completion x) = x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (U.symm.toLinearIsometry.completion.continuous.comp
      U.toLinearIsometry.completion.continuous) continuous_id
  | ih x =>
    rw [LinearIsometry.completion_apply_coe, LinearIsometry.completion_apply_coe]
    exact congrArg (fun y : H => (y : UniformSpace.Completion H)) (U.symm_apply_apply x)

/-- Completion preserves a concrete unitary and its inverse. -/
def completionEquiv (U : H ≃ₗᵢ[ℂ] K) :
    UniformSpace.Completion H ≃ₗᵢ[ℂ] UniformSpace.Completion K :=
  LinearIsometryEquiv.ofSurjective U.toLinearIsometry.completion
    (fun y => ⟨U.symm.toLinearIsometry.completion y, completion_inverse U.symm y⟩)

@[simp] theorem completionEquiv_coe (U : H ≃ₗᵢ[ℂ] K) (x : H) :
    completionEquiv U x = (U x : UniformSpace.Completion K) :=
  LinearIsometry.completion_apply_coe U.toLinearIsometry x

end Completion

section Tensor

variable {Q H K ι : Type*} [MeasurableSpace Q] {μ : Measure Q}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- Interchange the two factors of the actual completed Hilbert tensor product. -/
def tensorFlip : TensorSpace H K ≃ₗᵢ[ℂ] TensorSpace K H :=
  completionEquiv (TensorProduct.commIsometry ℂ H K)

omit [CompleteSpace H] in
theorem tensorFlip_tensor (v : H) (w : K) :
    tensorFlip (tensor v w) = tensor w v := by
  rw [tensor_apply, tensorFlip, completionEquiv_coe]
  rfl

variable (b : HilbertBasis ι ℂ K) (U : K ≃ₗᵢ[ℂ] Lp ℂ 2 μ)

/-- Transport the chosen Hilbert basis through the scalar realization. -/
def imageBasis : HilbertBasis ι ℂ (Lp ℂ 2 μ) :=
  HilbertBasis.ofRepr (U.symm.trans b.repr)

omit [CompleteSpace H] in
theorem imageBasis_apply (i : ι) : imageBasis b U i = U (b i) := by
  classical
  change U (b.repr.symm (lp.single 2 i (1 : ℂ))) = U (b i)
  rw [HilbertBasis.repr_symm_single]

/-- The coefficient maps construct tensor-to-Bochner L² without a tensor
representation assumption. -/
def tensorToL2 : TensorSpace H K ≃ₗᵢ[ℂ] Lp H 2 μ :=
  (TensorCoordinates.coefficients b).trans
    (PhysicalL2HilbertSum.coefficients (imageBasis b U)).symm

private theorem l2_coefficients_tensor (f : Lp ℂ 2 μ) (v : H) (i : ι) :
    PhysicalL2HilbertSum.coefficients (imageBasis b U)
      (PhysicalL2HilbertSum.tensor f v) i = ⟪imageBasis b U i, f⟫_ℂ • v := by
  apply ext_inner_left ℂ
  intro z
  rw [PhysicalL2HilbertSum.coefficients_inner, PhysicalL2HilbertSum.tensor_inner,
    inner_smul_right]

theorem tensorToL2_tensor (v : H) (w : K) :
    tensorToL2 b U (tensor v w) = PhysicalL2HilbertSum.tensor (U w) v := by
  apply (PhysicalL2HilbertSum.coefficients (imageBasis b U)).injective
  change PhysicalL2HilbertSum.coefficients (imageBasis b U)
      ((PhysicalL2HilbertSum.coefficients (imageBasis b U)).symm
        (TensorCoordinates.coefficients b (tensor v w))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  ext i
  rw [TensorCoordinates.coefficients_tensor, l2_coefficients_tensor,
    imageBasis_apply, U.inner_map_map]

theorem tensorToL2_tensor_ae (v : H) (w : K) :
    tensorToL2 b U (tensor v w) =ᵐ[μ] fun q => U w q • v := by
  rw [tensorToL2_tensor]
  exact PhysicalL2HilbertSum.tensor_ae (U w) v

end Tensor

section Spatial

variable {X Q H K : Type*} [MeasurableSpace X] [MeasurableSpace Q]
  (ν : Measure X) (μ : Measure Q)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- A fixed fiber unitary lifts to the actual electronic L² space. -/
def liftEquiv (U : H ≃ₗᵢ[ℂ] K) : Lp H 2 ν ≃ₗᵢ[ℂ] Lp K 2 ν :=
  LinearIsometryEquiv.ofSurjective
    (PhysicalSectorCoordinates.liftIsometry ν U.toLinearIsometry) (by
      intro v
      refine ⟨PhysicalSectorCoordinates.liftIsometry ν U.symm.toLinearIsometry v, ?_⟩
      apply Lp.ext
      filter_upwards [PhysicalSectorCoordinates.liftIsometry_ae ν U.toLinearIsometry
        (PhysicalSectorCoordinates.liftIsometry ν U.symm.toLinearIsometry v),
        PhysicalSectorCoordinates.liftIsometry_ae ν U.symm.toLinearIsometry v]
        with x hx hy
      rw [hx, hy]
      exact U.apply_symm_apply (v x))

theorem liftEquiv_ae (U : H ≃ₗᵢ[ℂ] K) (v : Lp H 2 ν) :
    liftEquiv ν U v =ᵐ[ν] fun x => U (v x) :=
  PhysicalSectorCoordinates.liftIsometry_ae ν U.toLinearIsometry v

variable [SFinite μ] [SFinite ν]

/-- Swap the actual Gaussian and electronic product variables. -/
def productSwap : Lp H 2 (ν.prod μ) ≃ₗᵢ[ℂ] Lp H 2 (μ.prod ν) :=
  LinearIsometryEquiv.ofSurjective
    (Lp.compMeasurePreservingₗᵢ ℂ Prod.swap Measure.measurePreserving_swap) (by
      intro v
      refine ⟨Lp.compMeasurePreserving Prod.swap Measure.measurePreserving_swap v, ?_⟩
      change Lp.compMeasurePreserving Prod.swap Measure.measurePreserving_swap
        (Lp.compMeasurePreserving Prod.swap Measure.measurePreserving_swap v) = v
      apply Lp.ext
      filter_upwards [Lp.coeFn_compMeasurePreserving
        (Lp.compMeasurePreserving Prod.swap Measure.measurePreserving_swap v)
        Measure.measurePreserving_swap,
        (Measure.measurePreserving_swap (μ := μ) (ν := ν)).quasiMeasurePreserving.ae
          (Lp.coeFn_compMeasurePreserving v Measure.measurePreserving_swap)] with p hp hq
      exact hp.trans hq)

theorem productSwap_ae (v : Lp H 2 (ν.prod μ)) :
    productSwap ν μ v =ᵐ[μ.prod ν] fun qx => v (qx.2, qx.1) :=
  Lp.coeFn_compMeasurePreserving v Measure.measurePreserving_swap

variable [CompleteSpace K]
  [TopologicalSpace.SeparableSpace K] [IsSeparable μ] [IsSeparable ν]

/-- Product-space source coordinates come from the fiber unitary and Fubini. -/
def productSource (U : H ≃ₗᵢ[ℂ] Lp K 2 μ) :
    Lp H 2 ν ≃ₗᵢ[ℂ] Lp K 2 (μ.prod ν) :=
  (liftEquiv ν U).trans
    ((PhysicalSourceFubini.curryEquiv (μ := ν) (ν := μ)).symm.trans (productSwap ν μ))

omit [IsSeparable ν] in
/-- The product source is pointwise the same fiber unitary before Fubini. -/
theorem productSource_represents (U : H ≃ₗᵢ[ℂ] Lp K 2 μ) (v : Lp H 2 ν) :
    ∀ᵐ x ∂ν, (fun q => productSource ν μ U v (q, x)) =ᵐ[μ]
      fun q => U (v x) q := by
  let p : Lp K 2 (ν.prod μ) :=
    (PhysicalSourceFubini.curryEquiv (μ := ν) (ν := μ)).symm (liftEquiv ν U v)
  have hp : PhysicalSourceFubini.curryEquiv p = liftEquiv ν U v :=
    LinearIsometryEquiv.apply_symm_apply _ _
  have hc := PhysicalSourceFubini.curryEquiv_represents_ae p
  rw [hp] at hc
  have hs := (Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae
    (productSwap_ae ν μ p)
  filter_upwards [hc, liftEquiv_ae ν U v, Measure.ae_ae_of_ae_prod hs] with x hx hU hswap
  filter_upwards [hx, hswap] with q hq hs
  change productSwap ν μ p (q, x) = U (v x) q
  exact hs.trans (hq.symm.trans (congrArg (fun w : Lp K 2 μ => w q) hU))

/-- The Gaussian slicing unitary uses exactly the same product-space source. -/
def spatialUnitary (U : H ≃ₗᵢ[ℂ] Lp K 2 μ) :
    Lp H 2 ν ≃ₗᵢ[ℂ] Lp (Lp K 2 ν) 2 μ :=
  (productSource ν μ U).trans PhysicalSourceFubini.curryEquiv

theorem spatialUnitary_source (U : H ≃ₗᵢ[ℂ] Lp K 2 μ) (v : Lp H 2 ν) :
    spatialUnitary ν μ U v = PhysicalSourceFubini.curryEquiv (productSource ν μ U v) := rfl

/-- The representative matching required by infrared removal is definitional. -/
theorem spatialUnitary_fiber_source (U : H ≃ₗᵢ[ℂ] Lp K 2 μ) (v : Lp H 2 ν) :
    Gaussian.unitaryFiber (spatialUnitary ν μ U) v =ᵐ[μ]
      fun q => PhysicalSourceFubini.curryEquiv (productSource ν μ U v) q :=
  Filter.Eventually.of_forall (fun _ => rfl)

end Spatial

end GptLean.PhysicalGaussianCoordinates
