import PfHk.CoordinateMultiplication

/-! Holder multiplication transported through the actual coordinate Fubini
isometry. This lemma has no H1 or spectral objects in its proof context. -/

noncomputable section
namespace PfHk.OrdinaryCoordinateLpMultiplier

open MeasureTheory GptLean GptLean.ElectronicH1Space
open GptLean.PhysicalSourceCoordinates GptLean.PhysicalSourceMarginal
open GptLean.PhysicalSourceFubini PfHk.CoordinateSobolev
open scoped ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
set_option maxHeartbeats 200000

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

theorem multiplier (n : Fin N) (b : Position → ℝ) (hb : MemLp b 3 volume)
    (u : L2 H (Fin N × Fin 3))
    (hs : MemLp (particleMap n u) 6 volume) (M : ℝ)
    (hM : (eLpNorm (particleMap n u) 6 volume).toReal ≤ M) :
    ∃ hm : MemLp (fun x => coordinateCoefficient n b x • u x) 2 volume,
      ‖hm.toLp (fun x => coordinateCoefficient n b x • u x)‖ ≤
        (eLpNorm b 3 volume).toReal * M := by
  have hb' : MemLp b (ENNReal.ofReal (3 : ℝ)) volume := by simpa using hb
  have hs' : MemLp (particleMap n u) (ENNReal.ofReal (sourceExponent 3)) volume := by
    simpa only [sourceExponent, show (2 : ℝ) * 3 / (3 - 2) = 6 by norm_num,
      ENNReal.ofReal_ofNat] using hs
  obtain ⟨hmarg, hmargbound⟩ := holder_multiplier (by norm_num : (2 : ℝ) < 3)
    b (particleMap n u) hb' hs'
  let U := productMap (split n) (split_symm_measurePreserving n) (u)
  obtain ⟨hp, hpnorm⟩ := CoordinateMultiplierFubini.product_multiplier U b
    hb.aestronglyMeasurable hmarg
  have hpull := hp.comp_measurePreserving (split_measurePreserving n)
  have hrep := (split_measurePreserving n).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_compMeasurePreserving (u) (split_symm_measurePreserving n))
  have heq : (fun x => b (split n x).1 • U (split n x)) =ᵐ[volume]
      (fun x => coordinateCoefficient n b x • u x) := by
    filter_upwards [hrep] with x hx
    have hx' : U (split n x) = u x := by
      change (Lp.compMeasurePreserving (split n).symm (split_symm_measurePreserving n) (u))
        (split n x) = u x
      simpa only [Function.comp_apply, (split n).symm_apply_apply] using hx
    exact congrArg (fun v : H => b (split n x).1 • v) hx'
  have hm : MemLp (fun x => coordinateCoefficient n b x • u x) 2 volume :=
    hpull.ae_eq heq
  refine ⟨hm, ?_⟩
  let wP : Lp H 2 (volume.prod volume) := hp.toLp (fun p => b p.1 • U p)
  let wM := hmarg.toLp (fun x => b x • particleMap (H := H) n (u) x)
  let wX : L2 H (Fin N × Fin 3) :=
    Lp.compMeasurePreserving (split n) (split_measurePreserving n) wP
  have hwP := (split_measurePreserving n).quasiMeasurePreserving.ae_eq_comp hp.coeFn_toLp
  have hwX : (wX : Configuration N → H) =ᵐ[volume]
      fun x => coordinateCoefficient n b x • u x :=
    (Lp.coeFn_compMeasurePreserving wP (split_measurePreserving n)).trans (hwP.trans heq)
  have hclass : hm.toLp (fun x => coordinateCoefficient n b x • u x) = wX :=
    Lp.ext (hm.coeFn_toLp.trans hwX.symm)
  have hn : ‖hm.toLp (fun x => coordinateCoefficient n b x • u x)‖ = ‖wP‖ := by
    rw [hclass]
    exact Lp.norm_compMeasurePreserving wP (split_measurePreserving n)
  have hn' : ‖wP‖ = ‖wM‖ :=
    (sq_eq_sq₀ (norm_nonneg wP) (norm_nonneg wM)).mp hpnorm
  have harg : ‖wM‖ ≤ (eLpNorm b 3 volume).toReal *
      (eLpNorm (particleMap n u) 6 volume).toReal := by
    simpa only [sourceExponent, show (2 : ℝ) * 3 / (3 - 2) = 6 by norm_num,
      ENNReal.ofReal_ofNat] using hmargbound
  exact (hn.trans hn').le.trans (harg.trans
    (mul_le_mul_of_nonneg_left hM ENNReal.toReal_nonneg))

end PfHk.OrdinaryCoordinateLpMultiplier
