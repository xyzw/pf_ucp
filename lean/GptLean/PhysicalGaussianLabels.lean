import GptLean.PhysicalFockWienerSegal
import GptLean.PhysicalPolarizationRealStructure

/-!
The article's soft Fourier derivatives are actual vectors of the real soft
one-photon space. Extending first chaos by the real projection and the sharp
soft projection supplies the continuous map on the full one-photon L² space.
Its agreement on every derivative label is proved, rather than supplied as
a physical matching assumption.
-/

noncomputable section

namespace GptLean.PhysicalFock.RealStructure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (J : RealStructure E)

/-- Real part relative to an arbitrary Hilbert conjugation. -/
def realPart : E →L[ℝ] E :=
  (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ E + J.realCLM)

theorem realPart_fixed (x : E) : J.realPart x ∈ J.fixedSpace := by
  rw [J.mem_fixedSpace]
  change J.realCLM ((1 / 2 : ℝ) • (x + J.realCLM x)) =
    (1 / 2 : ℝ) • (x + J.realCLM x)
  rw [map_smul, map_add]
  change (1 / 2 : ℝ) • (J.conjugation x + J.conjugation (J.conjugation x)) = _
  rw [J.involutive, add_comm]
  rfl

/-- The continuous real projection into the fixed real subspace. -/
def realProjection : E →L[ℝ] J.fixedSpace :=
  J.realPart.codRestrict J.fixedSpace J.realPart_fixed

@[simp] theorem realProjection_fixed (x : J.fixedSpace) :
    J.realProjection (x : E) = x := by
  apply Subtype.ext
  change (1 / 2 : ℝ) • ((x : E) + J.conjugation x) = x
  rw [J.conjugation_fixed, ← two_smul ℝ, smul_smul]
  norm_num

end GptLean.PhysicalFock.RealStructure

namespace GptLean.PhysicalPolarization.Frame

open MeasureTheory Filter Gaussian PhysicalFock
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

variable (F : Frame) (χ : ArticleCutoff) (κ : ℝ) (hκ : 0 ≤ κ)

/-- The actual L² Fourier derivative, with the article normalization. -/
def softDerivativeL2 (i : Fin 3) (ds : List (Fin 3)) (x : FieldSpace) :
    Lp ℂ 2 photonMeasure :=
  softKernelL2 Prod.fst measurable_fst ds hκ (base F χ i)
    (base_measurable F χ i) (base_ultraviolet F χ i) x

theorem softDerivativeL2_ae (i : Fin 3) (ds : List (Fin 3)) (x : FieldSpace) :
    F.softDerivativeL2 χ κ hκ i ds x =ᵐ[photonMeasure]
      softDerivativeKernel Prod.fst ds κ x (base F χ i) :=
  (softDerivativeKernel_memLp Prod.fst measurable_fst ds hκ x (base F χ i)
    (base_measurable F χ i) (base_ultraviolet F χ i)).coeFn_toLp

theorem softDerivativeL2_mem (i : Fin 3) (ds : List (Fin 3)) (x : FieldSpace) :
    F.softDerivativeL2 χ κ hκ i ds x ∈ softOnePhoton κ := by
  apply (MomentumSplit.mem_supported_iff photonMeasure (softMomentumSet κ)
    (softMomentumSet_measurable κ) _).mpr
  filter_upwards [F.softDerivativeL2_ae χ κ hκ i ds x] with p hp
  intro hn
  have hn' : ¬ ‖p.1‖ < κ := hn
  rw [hp]
  simp only [softDerivativeKernel, softBase, hn', ↓reduceIte, mul_zero]

theorem softDerivativeL2_fixed (i : Fin 3) (ds : List (Fin 3)) (x : FieldSpace) :
    F.conjugation (F.softDerivativeL2 χ κ hκ i ds x) =
      F.softDerivativeL2 χ κ hκ i ds x :=
  F.softDerivativeKernel_fixed χ i ds κ x
    (softDerivativeKernel_memLp Prod.fst measurable_fst ds hκ x (base F χ i)
      (base_measurable F χ i) (base_ultraviolet F χ i))

/-- Each physical derivative label lies in the fixed real soft subspace. -/
def softLabel (i : Fin 3) (ds : List (Fin 3)) (x : FieldSpace) :
    (F.softRealStructure κ).fixedSpace :=
  ⟨⟨F.softDerivativeL2 χ κ hκ i ds x,
      F.softDerivativeL2_mem χ κ hκ i ds x⟩, by
    rw [RealStructure.mem_fixedSpace]
    apply Subtype.ext
    exact F.softDerivativeL2_fixed χ κ hκ i ds x⟩

/-- Restrict momentum and then take real part in the physical conjugation. -/
def realSoftProjection : Lp ℂ 2 photonMeasure →L[ℝ]
    (F.softRealStructure κ).fixedSpace :=
  (F.softRealStructure κ).realProjection.comp
    ((MomentumSplit.projectionInto photonMeasure (softMomentumSet κ)
      (softMomentumSet_measurable κ)).restrictScalars ℝ)

theorem realSoftProjection_label (i : Fin 3) (ds : List (Fin 3)) (x : FieldSpace) :
    F.realSoftProjection κ (F.softDerivativeL2 χ κ hκ i ds x) =
      F.softLabel χ κ hκ i ds x := by
  have hp : MomentumSplit.projectionInto photonMeasure (softMomentumSet κ)
      (softMomentumSet_measurable κ) (F.softDerivativeL2 χ κ hκ i ds x) =
        (F.softLabel χ κ hκ i ds x : softOnePhoton κ) := by
    apply Subtype.ext
    exact MomentumSplit.projection_of_supported _ _ _
      ⟨F.softDerivativeL2 χ κ hκ i ds x, F.softDerivativeL2_mem χ κ hκ i ds x⟩
  change (F.softRealStructure κ).realProjection
    (MomentumSplit.projectionInto photonMeasure (softMomentumSet κ)
      (softMomentumSet_measurable κ) (F.softDerivativeL2 χ κ hκ i ds x)) = _
  rw [hp, RealStructure.realProjection_fixed]

variable (W : ScalarWienerSegal photonMeasure (softOnePhoton κ) (F.softRealStructure κ))

/-- The required first-chaos map on full one-photon L² is constructed. -/
def fullFirstChaos : Lp ℂ 2 photonMeasure →L[ℝ] Lp ℝ 2 W.space.measure :=
  W.firstChaos.toContinuousLinearMap.comp (F.realSoftProjection κ)

theorem fullFirstChaos_label (i : Fin 3) (ds : List (Fin 3)) (x : FieldSpace) :
    F.fullFirstChaos κ W (F.softDerivativeL2 χ κ hκ i ds x) =
      W.firstChaos (F.softLabel χ κ hκ i ds x) := by
  change W.firstChaos (F.realSoftProjection κ (F.softDerivativeL2 χ κ hκ i ds x)) = _
  rw [F.realSoftProjection_label]

theorem fullFirstChaos_label_ae (i : Fin 3) (ds : List (Fin 3)) (x : FieldSpace) :
    F.fullFirstChaos κ W (F.softDerivativeL2 χ κ hκ i ds x) =ᵐ[W.space.measure]
      W.firstChaos (F.softLabel χ κ hκ i ds x) := by
  rw [F.fullFirstChaos_label]

/-- Apply only the universal scalar theorem to the proved physical real space. -/
def scalarRealization (BW : StandardWienerSegal) :
    ScalarWienerSegal photonMeasure (softOnePhoton κ) (F.softRealStructure κ) :=
  Classical.choice (BW.realization PhotonMode photonMeasure (softOnePhoton κ)
    (MomentumSplit.supported_closed _ _ _) (F.softRealStructure κ))

end GptLean.PhysicalPolarization.Frame
