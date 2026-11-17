import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
Ordinary conjugations and their closed real fixed spaces. These constructions
do not involve a physical kernel or a choice of Gaussian realization.
-/

noncomputable section

namespace GptLean.PhysicalFock

open MeasureTheory
open scoped ENNReal

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A Hilbert real structure is an isometric conjugate-linear involution. -/
structure RealStructure where
  conjugation : E ≃ₗᵢ⋆[ℂ] E
  involutive : Function.Involutive conjugation

namespace RealStructure

variable {E} (J : RealStructure E)

/-- The same conjugation, regarded as a real continuous linear map. -/
def realCLM : E →L[ℝ] E where
  toFun := J.conjugation
  map_add' := map_add J.conjugation
  map_smul' r x := by
    change J.conjugation (r • x) = r • J.conjugation x
    rw [← Complex.coe_smul, map_smulₛₗ, Complex.conj_ofReal, Complex.coe_smul]
  cont := J.conjugation.continuous

@[simp] theorem realCLM_apply (x : E) : J.realCLM x = J.conjugation x := rfl

/-- The real-linear isometry underlying a conjugation. -/
def realIsometry : E →ₗᵢ[ℝ] E where
  toLinearMap := J.realCLM.toLinearMap
  norm_map' := J.conjugation.norm_map

@[simp] theorem realIsometry_apply (x : E) : J.realIsometry x = J.conjugation x := rfl

/-- The vectors fixed by conjugation form a real subspace. -/
def fixedSpace : Submodule ℝ E :=
  (J.realCLM - ContinuousLinearMap.id ℝ E).ker

@[simp] theorem mem_fixedSpace (x : E) :
    x ∈ J.fixedSpace ↔ J.conjugation x = x := by
  change J.conjugation x - x = 0 ↔ J.conjugation x = x
  exact sub_eq_zero

theorem fixedSpace_closed : IsClosed (J.fixedSpace : Set E) :=
  (J.realCLM - ContinuousLinearMap.id ℝ E).isClosed_ker

instance [CompleteSpace E] : CompleteSpace J.fixedSpace :=
  J.fixedSpace_closed.completeSpace_coe

theorem conjugation_fixed (x : J.fixedSpace) : J.conjugation (x : E) = x :=
  (J.mem_fixedSpace x).mp x.property

section Lp

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

private def lpMap : Lp E 2 μ →SL[starRingEnd ℂ] Lp E 2 μ :=
  J.conjugation.toLinearIsometry.toContinuousLinearMap.compLpL 2 μ

private theorem lpMap_ae (u : Lp E 2 μ) :
    lpMap J μ u =ᵐ[μ] fun x => J.conjugation (u x) :=
  J.conjugation.toLinearIsometry.toContinuousLinearMap.coeFn_compLpL u

private theorem lpMap_norm (u : Lp E 2 μ) : ‖lpMap J μ u‖ = ‖u‖ := by
  apply congrArg ENNReal.toReal
  apply eLpNorm_congr_norm_ae
  filter_upwards [lpMap_ae J μ u] with x hx
  exact (congrArg norm hx).trans (J.conjugation.norm_map (u x))

private theorem lpMap_involutive (u : Lp E 2 μ) : lpMap J μ (lpMap J μ u) = u := by
  apply Lp.ext
  filter_upwards [lpMap_ae J μ (lpMap J μ u), lpMap_ae J μ u] with x hx hy
  rw [hx, hy, J.involutive]

/-- Pointwise application of a conjugation gives a conjugation of Bochner L². -/
def onLp : RealStructure (Lp E 2 μ) where
  conjugation :=
    { toLinearMap := (lpMap J μ).toLinearMap
      invFun := lpMap J μ
      left_inv := lpMap_involutive J μ
      right_inv := lpMap_involutive J μ
      norm_map' := lpMap_norm J μ }
  involutive := lpMap_involutive J μ

theorem onLp_ae (u : Lp E 2 μ) :
    (J.onLp μ).conjugation u =ᵐ[μ] fun x => J.conjugation (u x) := lpMap_ae J μ u

end Lp

/-- The ordinary scalar complex conjugation. -/
def complex : RealStructure ℂ where
  conjugation :=
    { toFun := starRingEnd ℂ
      invFun := starRingEnd ℂ
      map_add' := map_add (starRingEnd ℂ)
      map_smul' c z := map_mul (starRingEnd ℂ) c z
      left_inv := Complex.conj_conj
      right_inv := Complex.conj_conj
      norm_map' := Complex.norm_conj }
  involutive := Complex.conj_conj

@[simp] theorem complex_apply (z : ℂ) : complex.conjugation z = starRingEnd ℂ z := rfl

end RealStructure
end GptLean.PhysicalFock
