import GptLean.ElectronicH1Symmetry

/-!
Testing an L2 candidate derivative against the actual H1 domain recovers
the full vector-valued weak derivative identity.
-/

noncomputable section

namespace GptLean.ElectronicH1Maximal

open MeasureTheory ElectronicH1Complex SymmetricLift
open scoped ENNReal InnerProductSpace ContDiff

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000

variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype I] [DecidableEq I]

private theorem inner_scalar_test {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (φ : X → ℝ) (hφ : MemLp φ 2 μ) (z : H) (t g : Lp H 2 μ)
    (ht : t =ᵐ[μ] fun x => φ x • z) :
    ⟪t, g⟫_ℂ = ⟪z, l2TestIntegral φ g⟫_ℂ := by
  rw [L2.inner_def]
  apply Eq.trans _ (integral_inner (𝕜 := ℂ) (integrable_l2_test hφ g) z)
  apply integral_congr_ae
  filter_upwards [ht] with x hx
  rw [hx, inner_smul_left_eq_smul, inner_smul_right_eq_smul]

theorem hasWeakH1Local_of_adjoint
    (f : ElectronicH1Space.L2 H I) (d : I → ElectronicH1Space.L2 H I)
    (h : ∀ i (v : ComplexH1 H I), ⟪value v, d i⟫_ℂ = -⟪derivative i v, f⟫_ℂ) :
    HasWeakH1Local (fun x => f x) (fun i x => d i x) := by
  refine ⟨fun K _ => (Lp.memLp f).restrict K,
    fun i K _ => (Lp.memLp (d i)).restrict K, ?_⟩
  intro i φ hφ hs
  apply ext_inner_left ℂ
  intro z
  let θ : EuclideanSpace ℝ I → H := fun x => φ x • z
  have hθ : ContDiff ℝ ∞ θ := hφ.smul contDiff_const
  have hsθ : HasCompactSupport θ := hs.smul_right
  let v₀ : ElectronicH1Space.H1 H I := ElectronicH1Space.ofSmoothCompact θ hθ hsθ
  let v : ComplexH1 H I := ⟨v₀.val, v₀.property⟩
  have hv : (value v : EuclideanSpace ℝ I → H) =ᵐ[volume] θ :=
    (hθ.continuous.memLp_of_hasCompactSupport hsθ (p := (2 : ℝ≥0∞))
      (μ := volume)).coeFn_toLp
  have hdv : (derivative i v : EuclideanSpace ℝ I → H) =ᵐ[volume]
      fun x => fderiv ℝ φ x (EuclideanSpace.single i 1) • z := by
    have hcont : Continuous (fun x => fderiv ℝ θ x (EuclideanSpace.single i 1)) :=
      (hθ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hmem : MemLp (fun x => fderiv ℝ θ x (EuclideanSpace.single i 1)) 2 volume :=
      hcont.memLp_of_hasCompactSupport (hsθ.fderiv_apply ℝ (EuclideanSpace.single i 1))
    filter_upwards [hmem.coeFn_toLp] with x hx
    exact hx.trans (by
      simp only [θ, fderiv_smul_const (hφ.differentiable (by simp) x),
        ContinuousLinearMap.smulRight_apply])
  have hφmem := hφ.continuous.memLp_of_hasCompactSupport hs
    (p := (2 : ℝ≥0∞)) (μ := volume)
  have hdφcont : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφmem : MemLp (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) 2 volume :=
    hdφcont.memLp_of_hasCompactSupport (hs.fderiv_apply ℝ (EuclideanSpace.single i 1))
  have hl := inner_scalar_test φ hφmem z (value v) (d i) hv
  have hr := inner_scalar_test (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))
    hdφmem z (derivative i v) f hdv
  exact hl.symm.trans ((h i v).trans
    ((congrArg Neg.neg hr).trans (inner_neg_right z _).symm))

def ofAdjoint (f : ElectronicH1Space.L2 H I) (d : I → ElectronicH1Space.L2 H I)
    (h : ∀ i (v : ComplexH1 H I), ⟪value v, d i⟫_ℂ = -⟪derivative i v, f⟫_ℂ) :
    ComplexH1 H I := ⟨(f, d), hasWeakH1Local_of_adjoint f d h⟩

@[simp] theorem value_ofAdjoint (f : ElectronicH1Space.L2 H I)
    (d : I → ElectronicH1Space.L2 H I)
    (h : ∀ i (v : ComplexH1 H I), ⟪value v, d i⟫_ℂ = -⟪derivative i v, f⟫_ℂ) :
    value (ofAdjoint f d h) = f := rfl

@[simp] theorem derivative_ofAdjoint (f : ElectronicH1Space.L2 H I)
    (d : I → ElectronicH1Space.L2 H I)
    (h : ∀ i (v : ComplexH1 H I), ⟪value v, d i⟫_ℂ = -⟪derivative i v, f⟫_ℂ)
    (i : I) : derivative i (ofAdjoint f d h) = d i := rfl

end GptLean.ElectronicH1Maximal
