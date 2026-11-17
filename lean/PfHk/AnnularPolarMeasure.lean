import PfHk.CarlemanPolarMeasure
import PfHk.OrdinaryPolarSobolevChart

/-! Localization of the ordinary logarithmic change of measure to a
finite annular slab. No physical coefficient is involved. -/

noncomputable section
namespace PfHk.OrdinaryPolarSobolevChart

open MeasureTheory PfHk.PolarCalculus
open scoped ENNReal
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 150000

variable {N : ℕ}

theorem isOpen_annulus (a b : ℝ) : IsOpen (annulus N a b) :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

theorem chartPoint_norm (p : Slab N) : ‖chartPoint N p‖ = Real.exp (-p.1) := by
  unfold chartPoint
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), unitSphere_norm, mul_one]

theorem chartPoint_mem_annulus (a b : ℝ) (p : Slab N) :
    chartPoint N p ∈ annulus N a b ↔ p.1 ∈ Set.Ioo a b := by
  change Real.exp (-b) < ‖chartPoint N p‖ ∧ ‖chartPoint N p‖ < Real.exp (-a) ↔ a < p.1 ∧ p.1 < b
  rw [chartPoint_norm, Real.exp_lt_exp, Real.exp_lt_exp]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

theorem integrable_slab_pullback
    (L : StandardLogPolarCalculus (Fin N × Fin 3)) (hN : 0 < Fintype.card (Fin N × Fin 3))
    (a b : ℝ) (f : Position (Fin N × Fin 3) → ℝ) (hf : Integrable f) :
    Integrable (fun p : Slab N => logarithmicJacobian (Fin N × Fin 3) p.1 * f (chartPoint N p))
      (slabMeasure N a b) := by
  have hp := (L.integrable_change hN f).mp hf
  exact hp.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)

theorem integral_annular_slab
    (L : StandardLogPolarCalculus (Fin N × Fin 3)) (hN : 0 < Fintype.card (Fin N × Fin 3))
    (a b : ℝ) (f : Position (Fin N × Fin 3) → ℝ) (hf : Integrable f)
    (hs : ∀ X, X ∉ annulus N a b → f X = 0) :
    (∫ X, f X) = ∫ p : Slab N, logarithmicJacobian (Fin N × Fin 3) p.1 * f (chartPoint N p)
      ∂slabMeasure N a b := by
  have hp := integral_logPolar (Fin N × Fin 3) L hN f hf
  have hz (t : ℝ) (ht : t ∉ Set.Icc a b) :
      (∫ θ : PfHk.SphereAngularField.Sphere N,
        logarithmicJacobian (Fin N × Fin 3) t * f (chartPoint N (t, θ)) ∂sphereMeasure (Fin N × Fin 3)) = 0 := by
    apply integral_eq_zero_of_ae
    exact ae_of_all _ fun θ => by
      have hx : chartPoint N (t, θ) ∉ annulus N a b := by
        intro h
        have h' := (chartPoint_mem_annulus a b (t, θ)).mp h
        exact ht ⟨h'.1.le, h'.2.le⟩
      change logarithmicJacobian (Fin N × Fin 3) t * f (chartPoint N (t, θ)) = 0
      rw [hs _ hx, mul_zero]
  have hrestrict := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := (volume : Measure ℝ)) hz
  exact hp.trans (hrestrict.symm.trans
    (integral_prod _ (integrable_slab_pullback L hN a b f hf)).symm)

end PfHk.OrdinaryPolarSobolevChart
