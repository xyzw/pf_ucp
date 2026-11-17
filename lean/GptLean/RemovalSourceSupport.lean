import GptLean.RemovalSourceProduct
import GptLean.RemovalChannel

/-!
Spatial support and conditional mass of the actual localized WIS source.
Only the usual multiplication intertwining and Fubini-isometry
representative identity are assumed. Source support and source mass
identifications are then derived for the fixed spectral enumeration.
-/

noncomputable section

namespace GptLean.RemovalSource

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open MeasureTheory MeasureTheory.Measure Filter ElectronicLocalization Gaussian

variable {Q X H K : Type*} [MeasurableSpace Q] [MeasurableSpace X]
  {μ : Measure Q} {ν : Measure X} [SFinite μ] [SFinite ν]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

def productLocalizedVector (f : ℕ → X → ℝ)
    (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν) (ψ : Lp K 2 (μ.prod ν)) (a : ℕ) :
    Lp K 2 (μ.prod ν) :=
  localizedVector (fun a qx => f a qx.2) (fun qx => hpart qx.2)
    (fun a => (hf a).comp_quasiMeasurePreserving quasiMeasurePreserving_snd) ψ a

theorem localizedFiber_product_eq_mul
    (U : Lp H 2 ν ≃ₗᵢ[ℂ] Lp K 2 (μ.prod ν))
    (f : ℕ → X → ℝ) (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν)
    (hcommute : ∀ (ψ : Lp H 2 ν) a,
      U (localizedVector f hpart hf ψ a) = productLocalizedVector f hpart hf (U ψ) a)
    (ψ : ℕ → Lp H 2 ν) (i : ℕ) :
    localizedFiber U f hpart hf ψ i =ᵐ[μ.prod ν]
      (fun qx => (f (Nat.unpair i).2 qx.2 : ℂ) • U (ψ (Nat.unpair i).1) qx) := by
  change (fun qx => U (localizedVector f hpart hf (ψ (Nat.unpair i).1) (Nat.unpair i).2) qx) =ᵐ[_] _
  rw [hcommute]
  let g : ℕ → Q × X → ℝ := fun a qx => f a qx.2
  have hgm (a : ℕ) : AEStronglyMeasurable (g a) (μ.prod ν) :=
    (hf a).comp_quasiMeasurePreserving quasiMeasurePreserving_snd
  have hp := (localized_memLp (ν := μ.prod ν) g (fun qx => hpart qx.2) hgm
    (U (ψ (Nat.unpair i).1)) (Nat.unpair i).2).coeFn_toLp
  filter_upwards [hp] with qx hqx
  exact hqx

theorem localizedFiber_product_support [TopologicalSpace X]
    (U : Lp H 2 ν ≃ₗᵢ[ℂ] Lp K 2 (μ.prod ν))
    (f : ℕ → X → ℝ) (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν)
    (hcommute : ∀ (ψ : Lp H 2 ν) a,
      U (localizedVector f hpart hf ψ a) = productLocalizedVector f hpart hf (U ψ) a)
    (ψ : ℕ → Lp H 2 ν) (i : ℕ) :
    ∀ᵐ qx ∂μ.prod ν, qx.2 ∉ tsupport (f (Nat.unpair i).2) →
      localizedFiber U f hpart hf ψ i qx = 0 := by
  filter_upwards [localizedFiber_product_eq_mul U f hpart hf hcommute ψ i] with qx hqx
  intro hx
  rw [hqx, image_eq_zero_of_notMem_tsupport hx, Complex.ofReal_zero, zero_smul]

/-- The source mass used by the field moment bound is exactly the squared
norm of the nested WIS fibre under the ordinary Fubini representative map. -/
theorem product_sourceMass_fubini
    (Fubini : Lp K 2 (μ.prod ν) ≃ₗᵢ[ℂ] Lp (Lp K 2 ν) 2 μ)
    (hrep : ∀ v : Lp K 2 (μ.prod ν), ∀ᵐ q ∂μ,
      (fun x => v (q, x)) =ᵐ[ν] (fun x => Fubini v q x)) (v : Lp K 2 (μ.prod ν)) :
    ∀ᵐ q ∂μ, RemovalEnergy.sourceMass (ν := ν) v q = ‖Fubini v q‖ ^ 2 := by
  filter_upwards [hrep v] with q hq
  change (∫ x, ‖v (q, x)‖ ^ 2 ∂ν) = ‖Fubini v q‖ ^ 2
  exact (integral_congr_ae (hq.fun_comp (fun x : K => ‖x‖ ^ 2))).trans
    (lp_norm_sq (Fubini v q)).symm

theorem phased_product_sourceMass_fubini
    (Fubini : Lp K 2 (μ.prod ν) ≃ₗᵢ[ℂ] Lp (Lp K 2 ν) 2 μ)
    (hrep : ∀ v : Lp K 2 (μ.prod ν), ∀ᵐ q ∂μ,
      (fun x => v (q, x)) =ᵐ[ν] (fun x => Fubini v q x))
    (v : Lp K 2 (μ.prod ν)) (w : Q × X → ℂ)
    (hw : ∀ᵐ qx ∂μ.prod ν, ‖w qx‖ = 1) :
    ∀ᵐ q ∂μ, RemovalEnergy.sourceMass (ν := ν) (fun qx => phaseSource (w qx) (v qx)) q =
      ‖Fubini v q‖ ^ 2 := by
  filter_upwards [product_sourceMass_fubini Fubini hrep v, ae_ae_of_ae_prod hw] with q hq hunit
  change (∫ x, ‖phaseSource (w (q, x)) (v (q, x))‖ ^ 2 ∂ν) = _
  have he := integral_congr_ae (hunit.mono (fun x hx => phaseSource_mass (w (q, x)) hx (v (q, x))))
  exact he.trans hq

end GptLean.RemovalSource
