import GptLean.PhysicalL2FourierTransport
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
Fourier transform preserves every closed linear relation in the Hilbert
fiber. Orthogonal projection proves subspace preservation, and the Hilbert
product norm then treats graphs of unbounded fiber operators without a
boundedness or spectral-cutoff assumption on those operators.
-/

noncomputable section
namespace GptLean.PhysicalFourierGraph

open MeasureTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 200000

variable {X H K : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem fourier_mem_submodule (W : Submodule ℂ H) (hW : IsClosed (W : Set H))
    (u : Lp H 2 (volume : Measure X)) (hu : ∀ᵐ x ∂volume, u x ∈ W) :
    ∀ᵐ ξ ∂volume, Lp.fourierTransformₗᵢ X H u ξ ∈ W := by
  let : CompleteSpace W := hW.completeSpace_coe
  have hfix : W.starProjection.compLpL 2 volume u = u := by
    apply Lp.ext
    filter_upwards [W.starProjection.coeFn_compLpL u, hu] with x hx hw
    exact hx.trans (W.starProjection_eq_self_iff.mpr hw)
  have hfixF : W.starProjection.compLpL 2 volume (Lp.fourierTransformₗᵢ X H u) =
      Lp.fourierTransformₗᵢ X H u :=
    (PhysicalL2FourierTransport.fourier_compLpL W.starProjection u).symm.trans
      (congrArg (Lp.fourierTransformₗᵢ X H) hfix)
  have h := W.starProjection.coeFn_compLpL (Lp.fourierTransformₗᵢ X H u)
  rw [hfixF] at h
  filter_upwards [h] with ξ hξ
  exact W.starProjection_eq_self_iff.mp hξ.symm

private def left : H →L[ℂ] WithLp 2 (H × K) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H K).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℂ H K)

private def right : K →L[ℂ] WithLp 2 (H × K) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H K).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℂ H K)

private def pairL2 (u : Lp H 2 (volume : Measure X))
    (v : Lp K 2 (volume : Measure X)) : Lp (WithLp 2 (H × K)) 2 (volume : Measure X) :=
  (left (H := H) (K := K)).compLpL 2 volume u +
    (right (H := H) (K := K)).compLpL 2 volume v

omit [CompleteSpace H] [CompleteSpace K] in
private theorem pairL2_ae (u : Lp H 2 (volume : Measure X))
    (v : Lp K 2 (volume : Measure X)) :
    ∀ᵐ x ∂volume, WithLp.ofLp (pairL2 u v x) = (u x, v x) := by
  filter_upwards [(left (H := H) (K := K)).coeFn_compLpL u,
    (right (H := H) (K := K)).coeFn_compLpL v,
    Lp.coeFn_add ((left (H := H) (K := K)).compLpL 2 volume u)
      ((right (H := H) (K := K)).compLpL 2 volume v)] with x hu hv hadd
  change WithLp.ofLp ((_ + _ : Lp (WithLp 2 (H × K)) 2 volume) x) = _
  rw [hadd, Pi.add_apply, hu, hv]
  change (u x + 0, 0 + v x) = (u x, v x)
  simp only [add_zero, zero_add]

private theorem fourier_pairL2 (u : Lp H 2 (volume : Measure X))
    (v : Lp K 2 (volume : Measure X)) :
    Lp.fourierTransformₗᵢ X (WithLp 2 (H × K)) (pairL2 u v) =
      pairL2 (Lp.fourierTransformₗᵢ X H u) (Lp.fourierTransformₗᵢ X K v) := by
  simp only [pairL2, map_add, PhysicalL2FourierTransport.fourier_compLpL]

/-- Closed fiber graphs commute with the actual electronic Fourier transform. -/
theorem fourier_mem_graph (M : Submodule ℂ (H × K))
    (hM : IsClosed (M : Set (H × K)))
    (u : Lp H 2 (volume : Measure X)) (v : Lp K 2 (volume : Measure X))
    (hgraph : ∀ᵐ x ∂volume, (u x, v x) ∈ M) :
    ∀ᵐ ξ ∂volume,
      (Lp.fourierTransformₗᵢ X H u ξ, Lp.fourierTransformₗᵢ X K v ξ) ∈ M := by
  let W : Submodule ℂ (WithLp 2 (H × K)) :=
    M.comap (WithLp.prodContinuousLinearEquiv 2 ℂ H K).toLinearMap
  have hW : IsClosed (W : Set (WithLp 2 (H × K))) :=
    hM.preimage (WithLp.prodContinuousLinearEquiv 2 ℂ H K).continuous
  have hu : ∀ᵐ x ∂volume, pairL2 u v x ∈ W := by
    filter_upwards [pairL2_ae u v, hgraph] with x hx hm
    change WithLp.ofLp (pairL2 u v x) ∈ M
    exact hx.symm ▸ hm
  have hF := fourier_mem_submodule W hW (pairL2 u v) hu
  rw [fourier_pairL2] at hF
  filter_upwards [hF, pairL2_ae (Lp.fourierTransformₗᵢ X H u)
    (Lp.fourierTransformₗᵢ X K v)] with ξ hξ hp
  change WithLp.ofLp (pairL2 _ _ ξ) ∈ M at hξ
  exact hp ▸ hξ

end GptLean.PhysicalFourierGraph
