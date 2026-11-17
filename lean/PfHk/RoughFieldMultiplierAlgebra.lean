import PfHk.FieldMultiplierNormAlgebra
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! Rough scalar multiplication of a field and an affine derivative in an
arbitrary complex Hilbert-valued L2 space. No physical-space instance enters
these Hölder-domain and norm calculations. -/

noncomputable section
namespace PfHk.RoughFieldMultiplierAlgebra

open MeasureTheory PfHk.MultiplierNormAlgebra
open scoped ENNReal

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 30000

variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [NormedSpace ℝ H] {μ : Measure X}

def multiply (b : X → ℝ) (u : Lp H 2 μ)
    (h : MemLp (fun x => b x • u x) 2 μ) : Lp H 2 μ := h.toLp _

omit [InnerProductSpace ℂ H] in
theorem multiply_ae (b : X → ℝ) (u : Lp H 2 μ)
    (h : MemLp (fun x => b x • u x) 2 μ) :
    multiply b u h =ᵐ[μ] fun x => b x • u x := h.coeFn_toLp

theorem field_multiplier (b : X → ℝ) (hb : AEStronglyMeasurable b μ)
    (M : ℝ) (f r v : Lp H 2 μ)
    (hfield : ∀ᵐ x ∂μ, ‖f x‖ ≤ 2 * M * ‖r x‖ + M * ‖v x‖)
    (hR : MemLp (fun x => b x • r x) 2 μ)
    (hV : MemLp (fun x => b x • v x) 2 μ) :
    ∃ hF : MemLp (fun x => b x • f x) 2 μ,
      ‖multiply b f hF‖ ^ 2 ≤ 8 * M ^ 2 * ‖multiply b r hR‖ ^ 2 +
        2 * M ^ 2 * ‖multiply b v hV‖ ^ 2 := by
  have hp : ∀ᵐ x ∂μ, ‖b x • f x‖ ≤ 2 * M * ‖b x • r x‖ + M * ‖b x • v x‖ := by
    filter_upwards [hfield] with x hx
    exact weighted_norm_le (b x) (2 * M) M _ _ _ hx
  have hg : MemLp (fun x => 2 * M * ‖b x • r x‖ + M * ‖b x • v x‖) 2 μ :=
    (hR.norm.const_mul (2 * M)).add (hV.norm.const_mul M)
  have hF := hg.mono' (hb.smul (Lp.aestronglyMeasurable f)) hp
  refine ⟨hF, l2_square_bound μ (multiply b f hF) (multiply b r hR) (multiply b v hV)
    (8 * M ^ 2) (2 * M ^ 2) ?_⟩
  filter_upwards [hp, multiply_ae b f hF, multiply_ae b r hR, multiply_ae b v hV]
    with x hx hf hr hv
  have hl := congrArg (fun z : H => ‖z‖ ^ 2) hf
  have hh := congrArg₂ (fun r v : H => 8 * M ^ 2 * ‖r‖ ^ 2 + 2 * M ^ 2 * ‖v‖ ^ 2) hr hv
  exact hl.le.trans ((field_square M _ _ _ hx).trans_eq hh.symm)

theorem covariant_multiplier [SMulCommClass ℝ ℂ H]
    (b : X → ℝ) (hb : AEStronglyMeasurable b μ) (e M : ℝ)
    (p f r v d : Lp H 2 μ) (hd : d = (-Complex.I) • p - (e : ℂ) • f)
    (hfield : ∀ᵐ x ∂μ, ‖f x‖ ≤ 2 * M * ‖r x‖ + M * ‖v x‖)
    (hP : MemLp (fun x => b x • p x) 2 μ)
    (hR : MemLp (fun x => b x • r x) 2 μ)
    (hV : MemLp (fun x => b x • v x) 2 μ) :
    ∃ hD : MemLp (fun x => b x • d x) 2 μ,
      ‖multiply b d hD‖ ^ 2 ≤ 2 * ‖multiply b p hP‖ ^ 2 +
        16 * e ^ 2 * M ^ 2 * ‖multiply b r hR‖ ^ 2 +
        4 * e ^ 2 * M ^ 2 * ‖multiply b v hV‖ ^ 2 := by
  obtain ⟨hF, hFb⟩ := field_multiplier b hb M f r v hfield hR hV
  have heq : (fun x => b x • d x) =ᵐ[μ]
      fun x => (-Complex.I) • (b x • p x) - (e : ℂ) • (b x • f x) := by
    filter_upwards [Lp.coeFn_sub ((-Complex.I) • p) ((e : ℂ) • f),
      Lp.coeFn_smul (-Complex.I) p, Lp.coeFn_smul (e : ℂ) f] with x hs hp hf
    have hsub : (((-Complex.I) • p) - (e : ℂ) • f) x =
        (-Complex.I) • p x - (e : ℂ) • f x :=
      hs.trans (congrArg₂ (fun p f : H => p - f) hp hf)
    have hc := (congrArg (fun w : Lp H 2 μ => w x) hd).trans hsub
    exact (congrArg (fun z : H => b x • z) hc).trans (real_smul_complex_sub (b x) e _ _)
  have hD : MemLp (fun x => b x • d x) 2 μ :=
    ((hP.const_smul (-Complex.I)).sub (hF.const_smul (e : ℂ))).ae_eq heq.symm
  refine ⟨hD, ?_⟩
  have hn : ‖multiply b d hD‖ ^ 2 ≤ 2 * ‖multiply b p hP‖ ^ 2 +
      (2 * e ^ 2) * ‖multiply b f hF‖ ^ 2 := by
    refine l2_square_bound μ (multiply b d hD) (multiply b p hP) (multiply b f hF)
      2 (2 * e ^ 2) ?_
    filter_upwards [heq, multiply_ae b d hD, multiply_ae b p hP, multiply_ae b f hF]
      with x hx hd hp hf
    have hl := congrArg (fun z : H => ‖z‖ ^ 2) (hd.trans hx)
    have hr := congrArg₂ (fun p f : H => 2 * ‖p‖ ^ 2 + 2 * e ^ 2 * ‖f‖ ^ 2) hp hf
    exact hl.le.trans ((complex_difference_square e _ _).trans_eq hr.symm)
  exact covariant_square_combine e M _ _ _ _ _ hn hFb

end PfHk.RoughFieldMultiplierAlgebra
