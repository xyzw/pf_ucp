import GptLean.RepresentabilityCoherentBackground
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
Bochner integrals of the concrete Weyl representation. The operator is
constructed from an integrable scalar coefficient and a measurable family
of one-photon directions. Its annihilation commutator and field commutation
are proved sector by sector from the actual Weyl graph identities.

This is the integration step in the Fourier construction of functions of
commuting Segal fields. There is no functional-calculus or chain-rule
background in this module.
-/

noncomputable section

namespace GptLean.PhysicalWeyl

open MeasureTheory Filter PhysicalFock Representability
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option maxHeartbeats 800000

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} [SigmaFinite μ] {ν : Measure X}

/-- Integration preserves the maximal concrete annihilation graph. -/
theorem annihilationGraph_integral (g : Lp ℂ 2 μ) {u v : X → Fock μ}
    (hu : Integrable u ν) (hv : Integrable v ν)
    (h : ∀ᵐ x ∂ν, AnnihilationGraph μ g (u x) (v x)) :
    AnnihilationGraph μ g (∫ x, u x ∂ν) (∫ x, v x ∂ν) := by
  intro n
  let A := (annihilationSector μ n g).comp (lp.evalCLM ℂ (Sector μ) 2 (n + 1))
  change (lp.evalCLM ℂ (Sector μ) 2 n) (∫ x, v x ∂ν) = A (∫ x, u x ∂ν)
  rw [← (lp.evalCLM ℂ (Sector μ) 2 n).integral_comp_comm hv,
    ← A.integral_comp_comm hu]
  exact integral_congr_ae (h.mono fun x hx => hx n)

/-- Integration preserves the maximal concrete Segal graph. -/
theorem segalGraph_integral (g : Lp ℂ 2 μ) {u v : X → Fock μ}
    (hu : Integrable u ν) (hv : Integrable v ν)
    (h : ∀ᵐ x ∂ν, SegalGraph μ g (u x) (v x)) :
    SegalGraph μ g (∫ x, u x ∂ν) (∫ x, v x ∂ν) := by
  intro n
  change (lp.evalCLM ℂ (Sector μ) 2 n) (∫ x, v x ∂ν) =
    segalCoordinate μ g n (∫ x, u x ∂ν)
  rw [← (lp.evalCLM ℂ (Sector μ) 2 n).integral_comp_comm hv,
    ← (segalCoordinate μ g n).integral_comp_comm hu]
  exact integral_congr_ae (h.mono fun x hx => hx n)

variable (W : ConcreteWeylLaw μ) (f : X → Lp ℂ 2 μ)
  (hf : AEStronglyMeasurable f ν) (a : X → ℂ) (ha : Integrable a ν)

theorem integrable_conjugate {a : X → ℂ} (ha : Integrable a ν) :
    Integrable (fun x => starRingEnd ℂ (a x)) ν :=
  Complex.conjLIE.toLinearIsometry.toContinuousLinearMap.integrable_comp ha

include hf ha in
theorem weighted_weyl_integrable (u : Fock μ) :
    Integrable (fun x => a x • W.weyl (f x) u) ν := by
  have hm : AEStronglyMeasurable (fun x => a x • W.weyl (f x) u) ν :=
    ha.aestronglyMeasurable.smul
      (W.continuous.comp_aestronglyMeasurable
        (hf.prodMk (aestronglyMeasurable_const (b := u))))
  apply (ha.norm.mul_const ‖u‖).mono' hm
  exact ae_of_all _ fun x => by rw [norm_smul, LinearIsometryEquiv.norm_map]

/-- The strongly integrated Weyl operator. No operator-norm continuity of
the Weyl representation is needed. -/
def weylIntegral : Fock μ →L[ℂ] Fock μ :=
  LinearMap.mkContinuous
    { toFun := fun u => ∫ x, a x • W.weyl (f x) u ∂ν
      map_add' := by
        intro u v
        simp only [map_add, smul_add]
        exact integral_add (weighted_weyl_integrable W f hf a ha u)
          (weighted_weyl_integrable W f hf a ha v)
      map_smul' := by
        intro c u
        simp only [map_smul, smul_comm (a _) c]
        exact integral_smul c _ }
    (∫ x, ‖a x‖ ∂ν) (by
      intro u
      calc ‖∫ x, a x • W.weyl (f x) u ∂ν‖
          ≤ ∫ x, ‖a x • W.weyl (f x) u‖ ∂ν := norm_integral_le_integral_norm _
        _ = (∫ x, ‖a x‖ ∂ν) * ‖u‖ := by
          simp only [norm_smul, LinearIsometryEquiv.norm_map]
          exact integral_mul_const _ _)

theorem weylIntegral_apply (u : Fock μ) :
    weylIntegral W f hf a ha u = ∫ x, a x • W.weyl (f x) u ∂ν := rfl

theorem weylIntegral_norm_le (u : Fock μ) :
    ‖weylIntegral W f hf a ha u‖ ≤ (∫ x, ‖a x‖ ∂ν) * ‖u‖ := by
  change ‖∫ x, a x • W.weyl (f x) u ∂ν‖ ≤ _
  calc ‖∫ x, a x • W.weyl (f x) u ∂ν‖
      ≤ ∫ x, ‖a x • W.weyl (f x) u‖ ∂ν := norm_integral_le_integral_norm _
    _ = _ := by
      simp only [norm_smul, LinearIsometryEquiv.norm_map]
      exact integral_mul_const _ _

/-- The negative direction is the inverse Weyl operator. -/
theorem weyl_neg_apply (g : Lp ℂ 2 μ) (u : Fock μ) :
    W.weyl (-g) (W.weyl g u) = u := by
  have him : (⟪-g, g⟫_ℂ).im = 0 := by
    rw [inner_neg_left, Complex.neg_im,
      show (⟪g, g⟫_ℂ).im = 0 from inner_self_im (𝕜 := ℂ) g, neg_zero]
  rw [W.compose, him]
  simp [W.zero]

theorem inner_weyl (g : Lp ℂ 2 μ) (u v : Fock μ) :
    ⟪W.weyl g u, v⟫_ℂ = ⟪u, W.weyl (-g) v⟫_ℂ := by
  have h := (W.weyl (-g)).inner_map_map (W.weyl g u) v
  rw [weyl_neg_apply] at h
  exact h.symm

/-- The adjoint is obtained by conjugating the coefficient and reversing
the one-photon direction. -/
theorem weylIntegral_adjoint_inner (u v : Fock μ) :
    ⟪weylIntegral W f hf a ha u, v⟫_ℂ =
      ⟪u, weylIntegral W (fun x => -f x) hf.neg
        (fun x => starRingEnd ℂ (a x)) (integrable_conjugate ha) v⟫_ℂ := by
  have hi := weighted_weyl_integrable W f hf a ha u
  have hj := weighted_weyl_integrable W (fun x => -f x) hf.neg
    (fun x => starRingEnd ℂ (a x)) (integrable_conjugate ha) v
  change ⟪∫ x, a x • W.weyl (f x) u ∂ν, v⟫_ℂ =
    ⟪u, ∫ x, starRingEnd ℂ (a x) • W.weyl (-f x) v ∂ν⟫_ℂ
  rw [← inner_conj_symm (∫ x, a x • W.weyl (f x) u ∂ν) v,
    ← integral_inner hi v, ← integral_conj,
    ← integral_inner hj u]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    change starRingEnd ℂ ⟪v, a x • W.weyl (f x) u⟫_ℂ =
      ⟪u, starRingEnd ℂ (a x) • W.weyl (-f x) v⟫_ℂ
    rw [inner_conj_symm (𝕜 := ℂ), inner_smul_left, inner_smul_right, inner_weyl]

/-- The commutator is another explicit Weyl integral. Its extra coefficient
is the actual scalar product with the displacement direction. -/
theorem annihilationGraph_weylIntegral (g : Lp ℂ 2 μ)
    (hag : Integrable (fun x => a x * ⟪g, f x⟫_ℂ) ν)
    {u v : Fock μ} (hgraph : AnnihilationGraph μ g u v) :
    AnnihilationGraph μ g (weylIntegral W f hf a ha u)
      (weylIntegral W f hf a ha v +
        weylIntegral W f hf (fun x => a x * ⟪g, f x⟫_ℂ) hag u) := by
  have h₁ := weighted_weyl_integrable W f hf a ha v
  have h₂ := weighted_weyl_integrable W f hf _ hag u
  have hi : Integrable (fun x => a x • W.weyl (f x) (v + ⟪g, f x⟫_ℂ • u)) ν := by
    simpa only [map_add, map_smul, smul_add, smul_smul] using! h₁.fun_add h₂
  have hg : AnnihilationGraph μ g
      (∫ x, a x • W.weyl (f x) u ∂ν)
      (∫ x, a x • W.weyl (f x) (v + ⟪g, f x⟫_ℂ • u) ∂ν) := by
    apply annihilationGraph_integral g (weighted_weyl_integrable W f hf a ha u) hi
    exact ae_of_all _ fun x n => by
      have hn := W.annihilation_shift (f x) g u v hgraph n
      simpa only [lp.coeFn_smul, Pi.smul_apply, map_smul] using congrArg (a x • ·) hn
  simpa only [map_add, map_smul, smul_add, smul_smul, integral_add h₁ h₂,
    weylIntegral_apply] using hg

/-- If every displacement has zero real pairing with a field kernel,
the integrated operator commutes with that actual Segal field. -/
theorem segalGraph_weylIntegral (g : Lp ℂ 2 μ)
    (hreal : ∀ᵐ x ∂ν, (⟪g, f x⟫_ℂ).re = 0)
    {u v : Fock μ} (hgraph : SegalGraph μ g u v) :
    SegalGraph μ g (weylIntegral W f hf a ha u) (weylIntegral W f hf a ha v) := by
  apply segalGraph_integral g (weighted_weyl_integrable W f hf a ha u)
    (weighted_weyl_integrable W f hf a ha v)
  filter_upwards [hreal] with x hx
  have hs := W.field_shift (f x) g u v hgraph
  simp only [hx, mul_zero, Complex.ofReal_zero, zero_smul, add_zero] at hs
  intro n
  change (a x • W.weyl (f x) v) n = segalCoordinate μ g n (a x • W.weyl (f x) u)
  rw [map_smul]
  exact congrArg (a x • ·) (hs n)

end GptLean.PhysicalWeyl
