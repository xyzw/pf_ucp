import PfHk.CoordinateSobolev
import PfHk.CoordinateMultiplierFubini

/-! Actual coordinate multiplication derived from ordinary Sobolev embedding,
Hölder and the constructed Fubini isometry. -/

noncomputable section
namespace PfHk.CoordinateSobolev

open MeasureTheory GptLean.ElectronicH1Space
open GptLean.PhysicalSourceCoordinates GptLean.PhysicalSourceMarginal
open GptLean.PhysicalSourceFubini
open scoped ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 30000
set_option Elab.async false

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

def coordinateCoefficient (n : Fin N) (b : Position → ℝ) (x : Configuration N) : ℝ :=
  b (split n x).1

theorem coordinateCoefficient_measurable (n : Fin N) {b : Position → ℝ}
    (hb : AEStronglyMeasurable b volume) :
    AEStronglyMeasurable (coordinateCoefficient n b) volume :=
  hb.comp_fst.comp_measurePreserving (split_measurePreserving n)

/-- Coefficient multiplication is a theorem about actual L2 representatives,
not an additional domain or multiplier assumption. -/
theorem coordinate_multiplier (S : Data H N) {q : ℝ} (hq : 2 < q)
    (n : Fin N) (b : Position → ℝ) (hb : MemLp b (ENNReal.ofReal q) volume)
    (u v : L2 H (Fin N × Fin 3)) (hv : BesselPair n (3 / q) u v) :
    ∃ hm : MemLp (fun x => coordinateCoefficient n b x • u x) 2 volume,
      ‖hm.toLp _‖ ≤ S.constant q * (eLpNorm b (ENNReal.ofReal q) volume).toReal * ‖v‖ := by
  obtain ⟨hs, hsbound⟩ := S.embedding q hq n u v hv
  obtain ⟨hmarg, hmargbound⟩ := holder_multiplier hq b (particleMap n u) hb hs
  let U := productMap (split n) (split_symm_measurePreserving n) u
  obtain ⟨hp, hpnorm⟩ := CoordinateMultiplierFubini.product_multiplier U b
    hb.aestronglyMeasurable hmarg
  have hpull := hp.comp_measurePreserving (split_measurePreserving n)
  have hrep := (split_measurePreserving n).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_compMeasurePreserving u (split_symm_measurePreserving n))
  have heq : (fun x => b (split n x).1 • U (split n x)) =ᵐ[volume]
      (fun x => coordinateCoefficient n b x • u x) := by
    filter_upwards [hrep] with x hx
    have hx' : U (split n x) = u x := by
      change (Lp.compMeasurePreserving (split n).symm (split_symm_measurePreserving n) u)
        (split n x) = u x
      simpa only [Function.comp_apply, (split n).symm_apply_apply] using hx
    exact congrArg (fun v : H => b (split n x).1 • v) hx'
  have hm : MemLp (fun x => coordinateCoefficient n b x • u x) 2 volume :=
    hpull.ae_eq heq
  refine ⟨hm, ?_⟩
  let wP : Lp H 2 (volume.prod volume) := hp.toLp (fun p => b p.1 • U p)
  let wM := hmarg.toLp (fun x => b x • particleMap n u x)
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
  have hn' : ‖wP‖ = ‖wM‖ := by
    have hsquare : ‖wP‖ ^ 2 = ‖wM‖ ^ 2 := hpnorm
    exact (sq_eq_sq₀ (norm_nonneg wP) (norm_nonneg wM)).mp hsquare
  rw [hn, hn']
  calc
    _ ≤ (eLpNorm b (ENNReal.ofReal q) volume).toReal *
        (eLpNorm (particleMap n u) (ENNReal.ofReal (sourceExponent q)) volume).toReal :=
      hmargbound
    _ ≤ (eLpNorm b (ENNReal.ofReal q) volume).toReal * (S.constant q * ‖v‖) :=
      mul_le_mul_of_nonneg_left hsbound ENNReal.toReal_nonneg
    _ = _ := by ring

end PfHk.CoordinateSobolev
