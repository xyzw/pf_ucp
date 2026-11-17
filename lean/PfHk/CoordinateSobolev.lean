import GptLean.PhysicalH1Fourier
import GptLean.PhysicalSourceMarginal
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
The ordinary Hilbert-valued fractional Sobolev input, stated on the actual
coordinate Fourier multiplier. This background contains no electromagnetic
coefficient, Fock field, Carleman weight, localization or physical multiplier
estimate. Hölder's inequality is proved below from Mathlib.

The inhomogeneous Bessel potential is used since it is dominated directly by
the comparison operator `-Δ + Hrad + 1`.
-/

noncomputable section
namespace PfHk.CoordinateSobolev

open MeasureTheory GptLean.ElectronicH1Space
open GptLean.PhysicalSourceCoordinates GptLean.PhysicalSourceMarginal
open GptLean.PhysicalH1Fourier
open scoped ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

def besselSymbol (n : Fin N) (s : ℝ) (ξ : Configuration N) : ℝ :=
  (1 + (2 * Real.pi) ^ 2 * ∑ a : Fin 3, (ξ (n, a)) ^ 2) ^ (s / 2)

/-- The maximal graph of the actual coordinate Bessel multiplier. -/
def BesselPair (n : Fin N) (s : ℝ) (u v : L2 H (Fin N × Fin 3)) : Prop :=
  fourier v =ᵐ[volume] fun ξ => besselSymbol n s ξ • fourier u ξ

def sourceExponent (q : ℝ) : ℝ := 2 * q / (q - 2)

/-- Standard fractional Sobolev embedding in three variables with an arbitrary
Hilbert-valued spectator space. This is the sole Sobolev background. -/
structure Data (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H] (N : ℕ) where
  constant : ℝ → ℝ
  constant_nonneg : ∀ q, 0 ≤ constant q
  embedding : ∀ (q : ℝ), 2 < q → ∀ (n : Fin N) (u v : L2 H (Fin N × Fin 3)),
    BesselPair n (3 / q) u v →
      MemLp (particleMap n u) (ENNReal.ofReal (sourceExponent q)) volume ∧
      (eLpNorm (particleMap n u) (ENNReal.ofReal (sourceExponent q)) volume).toReal ≤
        constant q * ‖v‖

theorem holderTriple {q : ℝ} (hq : 2 < q) :
    ENNReal.HolderTriple (ENNReal.ofReal q)
      (ENNReal.ofReal (sourceExponent q)) 2 := by
  have hq0 : 0 < q := by linarith
  have hd : 0 < q - 2 := by linarith
  have h : Real.HolderTriple q (sourceExponent q) 2 := by
    constructor
    · dsimp [sourceExponent]
      field_simp [hq0.ne', hd.ne']
      ring
    · exact hq0
    · exact div_pos (mul_pos (by norm_num) hq0) hd
  simpa using h.ennrealOfReal

/-- Hölder yields the actual L2 product of a scalar coefficient and a
Hilbert-valued Sobolev source. -/
theorem holder_multiplier {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure X}
    {q : ℝ} (hq : 2 < q) (b : X → ℝ) (f : X → E)
    (hb : MemLp b (ENNReal.ofReal q) μ)
    (hf : MemLp f (ENNReal.ofReal (sourceExponent q)) μ) :
    ∃ hm : MemLp (fun x => b x • f x) 2 μ,
      ‖hm.toLp _‖ ≤ (eLpNorm b (ENNReal.ofReal q) μ).toReal *
        (eLpNorm f (ENNReal.ofReal (sourceExponent q)) μ).toReal := by
  let := holderTriple hq
  have hm : MemLp (fun x => b x • f x) 2 μ := hf.smul hb
  refine ⟨hm, ?_⟩
  rw [Lp.norm_toLp]
  have he := eLpNorm_smul_le_mul_eLpNorm (p := ENNReal.ofReal q)
    (q := ENNReal.ofReal (sourceExponent q)) (r := 2)
    hf.aestronglyMeasurable hb.aestronglyMeasurable
  exact (ENNReal.toReal_mono (ENNReal.mul_ne_top hb.eLpNorm_ne_top hf.eLpNorm_ne_top) he).trans_eq
    ENNReal.toReal_mul

end PfHk.CoordinateSobolev
