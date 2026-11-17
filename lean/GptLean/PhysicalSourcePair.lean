import GptLean.PhysicalSourceMarginal
import GptLean.PhysicalPairRealization

/-!
The article density-current pair of an actual electronic H1 vector.
The selected-particle source is constructed by coordinate splitting and
L2 Fubini. Its stronger integrability follows from the proved H1 Sobolev
theorem. Both components agree with the actual spectator integrals.
The same construction applies to square-summable H1 ensembles.
-/

noncomputable section

namespace GptLean.PhysicalSourcePair

open MeasureTheory GptLean.ElectronicH1Space GptLean.PhysicalSourceCoordinates
open GptLean.PhysicalSourceMarginal GptLean.PhysicalSourceFubini
open GptLean.PhysicalPairSpace GptLean.PhysicalPairRealization
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types false

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

omit [CompleteSpace H] in
theorem particleMap_norm_sq_ae (i : Fin N) (v : L2 H (Fin N × Fin 3)) :
    (fun x => ‖particleMap i v x‖ ^ 2) =ᵐ[volume]
      (fun x => ∫ y, ‖v ((split i).symm (x, y))‖ ^ 2) := by
  have hrep := Measure.ae_ae_of_ae_prod
    (Lp.coeFn_compMeasurePreserving v (split_symm_measurePreserving i))
  filter_upwards [curry_norm_sq_ae
    (productMap (split i) (split_symm_measurePreserving i) v), hrep] with x hx hrep
  change ‖curry (productMap (split i) (split_symm_measurePreserving i) v) x‖ ^ 2 = _
  rw [hx]
  apply integral_congr_ae
  filter_upwards [hrep] with y hy
  change ‖(Lp.compMeasurePreserving (split i).symm
    (split_symm_measurePreserving i) v) (x, y)‖ ^ 2 = _
  rw [hy]
  rfl

omit [CompleteSpace H] in
theorem particleMap_inner_ae (i : Fin N) (v w : L2 H (Fin N × Fin 3)) :
    (fun x => inner ℂ (particleMap i v x) (particleMap i w x)) =ᵐ[volume]
      (fun x => ∫ y, inner ℂ (v ((split i).symm (x, y)))
        (w ((split i).symm (x, y)))) := by
  have hv := Measure.ae_ae_of_ae_prod
    (Lp.coeFn_compMeasurePreserving v (split_symm_measurePreserving i))
  have hw := Measure.ae_ae_of_ae_prod
    (Lp.coeFn_compMeasurePreserving w (split_symm_measurePreserving i))
  filter_upwards [curry_inner_ae
    (productMap (split i) (split_symm_measurePreserving i) v)
    (productMap (split i) (split_symm_measurePreserving i) w), hv, hw] with x hx hv hw
  change inner ℂ (curry (productMap (split i) (split_symm_measurePreserving i) v) x)
    (curry (productMap (split i) (split_symm_measurePreserving i) w) x) = _
  rw [hx]
  apply integral_congr_ae
  filter_upwards [hv, hw] with y hyv hyw
  change inner ℂ (Lp.compMeasurePreserving (split i).symm
    (split_symm_measurePreserving i) v (x, y))
    (Lp.compMeasurePreserving (split i).symm
    (split_symm_measurePreserving i) w (x, y)) = _
  rw [hyv, hyw]
  rfl

/-- The actual electronic source yields the full article Banach-space pair. -/
def ofWaveFunction (i : Fin N) (u : H1 H (Fin N × Fin 3))
    (d : Fin 3 → L2 H (Fin N × Fin 3)) : Pair :=
  ofSource N (particleMap i (value u)) (fun a => particleMap i (d a))
    (Lp.memLp _) (particleSource_memLp_six i u) (fun _ => Lp.memLp _)

theorem density_ofWaveFunction_ae (i : Fin N) (u : H1 H (Fin N × Fin 3))
    (d : Fin 3 → L2 H (Fin N × Fin 3)) :
    (densityL1 (ofWaveFunction i u d) : PhysicalPairSpace.Position → ℝ) =ᵐ[volume]
      (fun x => (N : ℝ) * ∫ y, ‖value u ((split i).symm (x, y))‖ ^ 2) := by
  filter_upwards [density_ofSource_ae N (particleMap i (value u))
    (fun a => particleMap i (d a)) (Lp.memLp _) (particleSource_memLp_six i u)
    (fun _ => Lp.memLp _), particleMap_norm_sq_ae i (value u)] with x hρ hx
  exact hρ.trans (congrArg (fun t : ℝ => (N : ℝ) * t) hx)

theorem current_ofWaveFunction_ae (i : Fin N) (u : H1 H (Fin N × Fin 3))
    (d : Fin 3 → L2 H (Fin N × Fin 3)) (a : Fin 3) :
    (fun x => currentL1 (ofWaveFunction i u d) x a) =ᵐ[volume]
      (fun x => (N : ℝ) * (∫ y, inner ℂ (value u ((split i).symm (x, y)))
        (d a ((split i).symm (x, y)))).re) := by
  filter_upwards [current_ofSource_ae N (particleMap i (value u))
    (fun a => particleMap i (d a)) (Lp.memLp _) (particleSource_memLp_six i u)
    (fun _ => Lp.memLp _), particleMap_inner_ae i (value u) (d a)] with x hj hx
  change currentL1 (ofWaveFunction i u d) x a = _
  exact (congrArg (fun z : Vector => z a) hj).trans
    (congrArg (fun t : ℂ => (N : ℝ) * t.re) hx)

theorem integral_density_ofWaveFunction (i : Fin N) (u : H1 H (Fin N × Fin 3))
    (d : Fin 3 → L2 H (Fin N × Fin 3)) :
    (∫ x, densityL1 (ofWaveFunction i u d) x) = (N : ℝ) * ‖value u‖ ^ 2 := by
  unfold ofWaveFunction
  rw [integral_congr_ae (density_ofSource_ae N (particleMap i (value u))
    (fun a => particleMap i (d a)) (Lp.memLp _) (particleSource_memLp_six i u)
    (fun _ => Lp.memLp _))]
  change (∫ x, (N : ℝ) * ‖particleMap i (value u) x‖ ^ 2) = _
  rw [integral_const_mul]
  have hn := Repair.toL2_norm_sq (Lp.memLp (particleMap i (value u)))
  simp only [Lp.toLp_coeFn] at hn
  rw [← hn, (particleMap i).norm_map]

end GptLean.PhysicalSourcePair
