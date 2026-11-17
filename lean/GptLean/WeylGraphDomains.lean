import GptLean.PhysicalWeylIntegral

/-! Domain equalities and commuting field groups from the ordinary Weyl law.
All graphs are the maximal graphs of the actual adjacent-sector operators.
-/

noncomputable section
namespace GptLean.Representability.ConcreteWeylLaw

open MeasureTheory PhysicalFock PhysicalWeyl
open scoped InnerProductSpace

set_option Elab.async false

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]
  (W : ConcreteWeylLaw μ)

theorem annihilation_domain_iff (f g : Lp ℂ 2 μ) (u : Fock μ) :
    (∃ v, AnnihilationGraph μ g (W.weyl f u) v) ↔
      ∃ v, AnnihilationGraph μ g u v := by
  constructor
  · rintro ⟨v, hv⟩
    have h := W.annihilation_shift (-f) g _ _ hv
    rw [weyl_neg_apply] at h
    exact ⟨_, h⟩
  · rintro ⟨v, hv⟩
    exact ⟨_, W.annihilation_shift f g _ _ hv⟩

theorem field_domain_iff (f g : Lp ℂ 2 μ) (u : Fock μ) :
    (∃ v, SegalGraph μ g (W.weyl f u) v) ↔
      ∃ v, SegalGraph μ g u v := by
  constructor
  · rintro ⟨v, hv⟩
    have h := W.field_shift (-f) g _ _ hv
    rw [weyl_neg_apply] at h
    exact ⟨_, h⟩
  · rintro ⟨v, hv⟩
    exact ⟨_, W.field_shift f g _ _ hv⟩

/-- The full graph identity, including its reverse implication. -/
theorem annihilation_shift_iff (f g : Lp ℂ 2 μ) (u v : Fock μ) :
    AnnihilationGraph μ g (W.weyl f u) (W.weyl f (v + ⟪g, f⟫_ℂ • u)) ↔
      AnnihilationGraph μ g u v := by
  constructor
  · intro h
    have h' := W.annihilation_shift (-f) g _ _ h
    rw [weyl_neg_apply] at h'
    have hv : W.weyl (-f)
        (W.weyl f (v + ⟪g, f⟫_ℂ • u) + ⟪g, -f⟫_ℂ • W.weyl f u) = v := by
      rw [inner_neg_right, ← map_smul, ← map_add, weyl_neg_apply]
      simp
    rwa [hv] at h'
  · exact W.annihilation_shift f g u v

theorem field_shift_iff (f g : Lp ℂ 2 μ) (u v : Fock μ) :
    SegalGraph μ g (W.weyl f u)
      (W.weyl f (v + ((2 * (⟪g, f⟫_ℂ).re : ℝ) : ℂ) • u)) ↔
      SegalGraph μ g u v := by
  constructor
  · intro h
    have h' := W.field_shift (-f) g _ _ h
    rw [weyl_neg_apply] at h'
    have hs : ((2 * (⟪g, -f⟫_ℂ).re : ℝ) : ℂ) =
        -((2 * (⟪g, f⟫_ℂ).re : ℝ) : ℂ) := by
      simp [inner_neg_right]
    rw [hs, ← map_smul, ← map_add, weyl_neg_apply] at h'
    simpa using h'
  · exact W.field_shift f g u v

/-- Vanishing symplectic pairing gives commuting Weyl displacements. -/
theorem commute_of_im_inner_zero (f g : Lp ℂ 2 μ)
    (h : (⟪f, g⟫_ℂ).im = 0) (u : Fock μ) :
    W.weyl f (W.weyl g u) = W.weyl g (W.weyl f u) := by
  have h' : (⟪g, f⟫_ℂ).im = 0 := by
    rw [← inner_conj_symm g f, Complex.conj_im, h, neg_zero]
  rw [W.compose, W.compose, h, h', add_comm f g]

/-- Strong commutation in its unitary-group formulation. -/
theorem field_groups_commute (h g : Lp ℂ 2 μ)
    (hreal : (⟪h, g⟫_ℂ).im = 0) (s t : ℝ) (u : Fock μ) :
    W.weyl ((Complex.I * (t : ℂ)) • h)
        (W.weyl ((Complex.I * (s : ℂ)) • g) u) =
      W.weyl ((Complex.I * (s : ℂ)) • g)
        (W.weyl ((Complex.I * (t : ℂ)) • h) u) := by
  apply W.commute_of_im_inner_zero μ
  simp [inner_smul_left, inner_smul_right, Complex.mul_re, Complex.mul_im, hreal]

/-- The inverse, hence the Hilbert-space adjoint, is the negative displacement. -/
theorem weyl_symm (f : Lp ℂ 2 μ) : (W.weyl f).symm = W.weyl (-f) := by
  apply LinearIsometryEquiv.ext
  intro u
  apply (W.weyl f).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  simpa only [neg_neg] using (weyl_neg_apply W (-f) u).symm

theorem weyl_adjoint (f : Lp ℂ 2 μ) :
    (W.weyl f).toLinearIsometry.toContinuousLinearMap.adjoint =
      (W.weyl (-f)).toLinearIsometry.toContinuousLinearMap := by
  change ContinuousLinearMap.adjoint (W.weyl f : Fock μ →L[ℂ] Fock μ) =
    (W.weyl (-f) : Fock μ →L[ℂ] Fock μ)
  rw [LinearIsometryEquiv.adjoint_eq_symm]
  exact congrArg (fun U : Fock μ ≃ₗᵢ[ℂ] Fock μ =>
    U.toLinearIsometry.toContinuousLinearMap) (W.weyl_symm μ f)

/-- The conjugate field is the Segal field with imaginary kernel. -/
theorem conjugate_field_shift (f g : Lp ℂ 2 μ) (u v : Fock μ)
    (h : SegalGraph μ (Complex.I • g) u v) :
    SegalGraph μ (Complex.I • g) (W.weyl f u)
      (W.weyl f (v + ((2 * (⟪g, f⟫_ℂ).im : ℝ) : ℂ) • u)) := by
  have h' := W.field_shift f (Complex.I • g) u v h
  simpa [inner_smul_left, Complex.mul_re] using h'

end GptLean.Representability.ConcreteWeylLaw
