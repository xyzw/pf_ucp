import GptLean.PhotonLocalizationCompression
import GptLean.PhotonLocalizationSpectral
import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
The compact-resolvent vector estimate supplies the spectral expectation
in the actual operator compression. The trace identity for the weighted
spectral vectors of a normal positive functional is standard background.
Neither the spectral expectation bound nor finite dimensionality of the
operator corner is an input.
-/

namespace GptLean.PhotonTrace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- An operator with finite-dimensional range has a finite-dimensional
two-sided compression range. The finite corner is constructed from the
endomorphisms of the operator range. -/
theorem finiteDimensional_compression_range (S : H →L[ℂ] H)
    (hS : FiniteDimensional ℂ S.range) :
    FiniteDimensional ℂ (LinearMap.range (comprMap S).toLinearMap) := by
  let R : Submodule ℂ H := S.range
  let r : H →L[ℂ] R := S.codRestrict R (fun x => ⟨x, rfl⟩)
  let F : (R →L[ℂ] R) →ₗ[ℂ] (H →L[ℂ] H) := {
    toFun := fun b => R.subtypeL.comp (b.comp r)
    map_add' := by
      intro b c
      ext x
      rfl
    map_smul' := by
      intro c b
      ext x
      rfl }
  have : FiniteDimensional ℂ R := hS
  have : FiniteDimensional ℂ (LinearMap.range F) := inferInstance
  apply Submodule.finiteDimensional_of_le (S₂ := LinearMap.range F)
  rintro _ ⟨a, rfl⟩
  refine ⟨r.comp (a.comp R.subtypeL), ?_⟩
  ext v
  rfl

theorem isFiniteRankProj_of_finite_range {S : H →L[ℂ] H}
    (hS : IsStarProjection S) (hfinite : FiniteDimensional ℂ S.range) :
    IsFiniteRankProj S :=
  ⟨hS, finiteDimensional_compression_range S hfinite⟩

end GptLean.PhotonTrace

namespace GptLean.PhotonLocalization.CompactSpectrum

open PhotonTrace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The spectral projection supplies the finite-corner hypothesis of the
trace compression constructor. -/
theorem projection_isFiniteRankProj (K : CompactSpectrum H) (s : ℕ) :
    IsFiniteRankProj (K.projection s) :=
  isFiniteRankProj_of_finite_range (K.projection_isStarProjection s)
    (K.projection_finite_range s)

/-- The normal trace identity turns the vector spectral estimate into the
spectral tail expectation used by `compressionWitness`. The vectors
already include the square roots of the density-operator eigenvalues. -/
theorem trace_spectral_tail_le (K : CompactSpectrum H) (s : ℕ)
    (φ : (H →L[ℂ] H) →L[ℂ] ℂ) (v : ℕ → H)
    (htrace : ∀ a : H →L[ℂ] H, (φ (star a * a)).re = ∑' n, ‖a (v n)‖ ^ 2)
    (X : H →L[ℂ] H) (hfinite : ∀ n, K.FiniteEnergy (X (v n)))
    (henergy : Summable (fun n => K.form (X (v n)))) {E : ℝ}
    (hbound : ∑' n, K.form (X (v n)) ≤ E) :
    (φ (star X * (1 - K.projection s) * X)).re ≤ E / (s + 1) := by
  rw [star_mul_proj_mul (K.projection_isStarProjection s).one_sub, htrace]
  simpa only [mul_apply_eq_comp, sub_apply,
    one_apply_eq_self] using
    K.ensemble_spectral_tail_le s (fun n => X (v n)) hfinite henergy hbound

variable {Hfull : Type*} [NormedAddCommGroup Hfull] [InnerProductSpace ℂ Hfull]
  [CompleteSpace Hfull]

/-- Extend a local spectral projection by zero through an isometric
embedding. The compact spectrum belongs to the bounded local space,
while the normal state may live on the full configuration space. -/
noncomputable def embeddedProjection (K : CompactSpectrum H)
    (j : H →ₗᵢ[ℂ] Hfull) (s : ℕ) : Hfull →L[ℂ] Hfull :=
  (j.toContinuousLinearMap.comp (K.projection s)).comp j.toContinuousLinearMap.adjoint

@[simp] theorem embeddedProjection_apply (K : CompactSpectrum H)
    (j : H →ₗᵢ[ℂ] Hfull) (s : ℕ) (v : Hfull) :
    K.embeddedProjection j s v = j (K.projection s (j.toContinuousLinearMap.adjoint v)) := rfl

theorem adjoint_apply_embedding (j : H →ₗᵢ[ℂ] Hfull) (v : H) :
    j.toContinuousLinearMap.adjoint (j v) = v := by
  exact congrArg (fun a : H →L[ℂ] H => a v) j.adjoint_comp_self

theorem embeddedProjection_isStarProjection (K : CompactSpectrum H)
    (j : H →ₗᵢ[ℂ] Hfull) (s : ℕ) :
    IsStarProjection (K.embeddedProjection j s) := by
  have hP := K.projection_isStarProjection s
  have hidem (v : H) : K.projection s (K.projection s v) = K.projection s v := by
    simpa only [mul_apply_eq_comp] using
      congrArg (fun a : H →L[ℂ] H => a v) hP.isIdempotentElem.eq
  constructor
  · apply ContinuousLinearMap.ext
    intro v
    simp only [mul_apply_eq_comp, embeddedProjection_apply,
      adjoint_apply_embedding, hidem]
  · exact hP.isSelfAdjoint.conj_adjoint j.toContinuousLinearMap

theorem embeddedProjection_finite_range (K : CompactSpectrum H)
    (j : H →ₗᵢ[ℂ] Hfull) (s : ℕ) :
    FiniteDimensional ℂ (K.embeddedProjection j s).range := by
  have := K.projection_finite_range s
  apply Submodule.finiteDimensional_of_le
    (S₂ := (K.projection s).range.map j.toLinearMap)
  rintro _ ⟨v, rfl⟩
  exact ⟨K.projection s (j.toContinuousLinearMap.adjoint v),
    ⟨j.toContinuousLinearMap.adjoint v, rfl⟩, rfl⟩

theorem embeddedProjection_isFiniteRankProj (K : CompactSpectrum H)
    (j : H →ₗᵢ[ℂ] Hfull) (s : ℕ) :
    IsFiniteRankProj (K.embeddedProjection j s) :=
  isFiniteRankProj_of_finite_range (K.embeddedProjection_isStarProjection j s)
    (K.embeddedProjection_finite_range j s)

/-- The full-space spectral expectation is controlled by the local form
energy once the cutoff vectors are identified with embedded local
vectors. This makes no compact-resolvent assumption on the full space. -/
theorem trace_embedded_spectral_tail_le (K : CompactSpectrum H)
    (j : H →ₗᵢ[ℂ] Hfull) (s : ℕ)
    (φ : (Hfull →L[ℂ] Hfull) →L[ℂ] ℂ) (v : ℕ → Hfull)
    (htrace : ∀ a : Hfull →L[ℂ] Hfull,
      (φ (star a * a)).re = ∑' n, ‖a (v n)‖ ^ 2)
    (X : Hfull →L[ℂ] Hfull) (w : ℕ → H)
    (hlocal : ∀ n, X (v n) = j (w n))
    (hfinite : ∀ n, K.FiniteEnergy (w n))
    (henergy : Summable (fun n => K.form (w n))) {E : ℝ}
    (hbound : ∑' n, K.form (w n) ≤ E) :
    (φ (star X * (1 - K.embeddedProjection j s) * X)).re ≤ E / (s + 1) := by
  rw [star_mul_proj_mul (K.embeddedProjection_isStarProjection j s).one_sub, htrace]
  have hresidual (n : ℕ) :
      ‖((1 - K.embeddedProjection j s) * X) (v n)‖ ^ 2 =
        ‖w n - K.projection s (w n)‖ ^ 2 := by
    simp only [mul_apply_eq_comp, sub_apply,
      one_apply_eq_self, hlocal, embeddedProjection_apply,
      adjoint_apply_embedding, ← map_sub, j.norm_map]
  simp_rw [hresidual]
  exact K.ensemble_spectral_tail_le s w hfinite henergy hbound

end GptLean.PhotonLocalization.CompactSpectrum
