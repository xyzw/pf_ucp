import GptLean.PhysicalNormalCoordinates

/-!
Real and imaginary bounded observable tests are represented by ordinary
self-adjoint operator parts. Positive spectral expansions transfer these
identities to the actual normal trace representation.
-/

noncomputable section
namespace GptLean.PhysicalNormalTrace

open PhotonLocalizationChannel
open scoped InnerProductSpace BoundedContinuousFunction

variable {H T : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : Gaussian.RankOneData H T}

def realOperatorPart (A : H →L[ℂ] H) : H →L[ℂ] H :=
  (1 / 2 : ℂ) • (A + A.adjoint)

def imaginaryOperatorPart (A : H →L[ℂ] H) : H →L[ℂ] H :=
  (-Complex.I / 2) • (A - A.adjoint)

omit [CompleteSpace T] in
theorem realOperatorPart_inner (A : H →L[ℂ] H) (u : H) :
    ⟪u, realOperatorPart A u⟫_ℂ = ((⟪u, A u⟫_ℂ).re : ℂ) := by
  have ha : ⟪A u, u⟫_ℂ = star ⟪u, A u⟫_ℂ := (inner_conj_symm (A u) u).symm
  rw [realOperatorPart, smul_apply,
    add_apply, inner_smul_right, inner_add_right,
    A.adjoint_inner_right, ha]
  generalize ⟪u, A u⟫_ℂ = z
  apply Complex.ext <;> simp
  ring

omit [CompleteSpace T] in
theorem imaginaryOperatorPart_inner (A : H →L[ℂ] H) (u : H) :
    ⟪u, imaginaryOperatorPart A u⟫_ℂ = ((⟪u, A u⟫_ℂ).im : ℂ) := by
  have ha : ⟪A u, u⟫_ℂ = star ⟪u, A u⟫_ℂ := (inner_conj_symm (A u) u).symm
  rw [imaginaryOperatorPart, smul_apply,
    sub_apply, inner_smul_right, inner_sub_right,
    A.adjoint_inner_right, ha]
  generalize ⟪u, A u⟫_ℂ = z
  apply Complex.ext <;> simp
  ring

omit [CompleteSpace T] in
theorem realOperatorPart_trace (normal : NormalTraceData R) (F : NormalFunctionalData R)
    (A : H →L[ℂ] H) {x : T} (hx : x ∈ R.positive) :
    F.repr x (realOperatorPart A) = ((F.repr x A).re : ℂ) := by
  obtain ⟨v, hv⟩ := normal.positive_decomposition x hx
  have h := F.observable_hasSum hv (realOperatorPart A)
  have hr := Complex.ofRealCLM.hasSum (Complex.reCLM.hasSum (F.observable_hasSum hv A))
  simp only [realOperatorPart_inner] at h
  exact h.unique hr

omit [CompleteSpace T] in
theorem imaginaryOperatorPart_trace (normal : NormalTraceData R) (F : NormalFunctionalData R)
    (A : H →L[ℂ] H) {x : T} (hx : x ∈ R.positive) :
    F.repr x (imaginaryOperatorPart A) = ((F.repr x A).im : ℂ) := by
  obtain ⟨v, hv⟩ := normal.positive_decomposition x hx
  have h := F.observable_hasSum hv (imaginaryOperatorPart A)
  have hr := Complex.ofRealCLM.hasSum (Complex.imCLM.hasSum (F.observable_hasSum hv A))
  simp only [imaginaryOperatorPart_inner] at h
  exact h.unique hr

/-- Encode both real coordinate tests in one natural-number family. -/
def realCoordinateTests (n : ℕ) : (ℕ →ᵇ ℂ) →L[ℝ] ℝ :=
  (if (Nat.unpair n).2 = 0 then Complex.reCLM else Complex.imCLM).comp
    (BoundedContinuousFunction.evalCLM ℝ (Nat.unpair n).1)

theorem realCoordinateTests_separate (x y : ℕ →ᵇ ℂ)
    (h : ∀ n, realCoordinateTests n x = realCoordinateTests n y) : x = y := by
  ext n
  apply Complex.ext
  · simpa only [realCoordinateTests, Nat.unpair_pair, ite_true,
      ContinuousLinearMap.comp_apply, BoundedContinuousFunction.evalCLM_apply,
      Complex.reCLM_apply] using h (Nat.pair n 0)
  · simpa only [realCoordinateTests, Nat.unpair_pair, Nat.one_ne_zero, ite_false,
      ContinuousLinearMap.comp_apply, BoundedContinuousFunction.evalCLM_apply,
      Complex.imCLM_apply] using h (Nat.pair n 1)

end GptLean.PhysicalNormalTrace
