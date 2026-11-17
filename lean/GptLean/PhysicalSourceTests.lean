import GptLean.PhysicalSourcePair
import GptLean.SymmetricLift.MetricGeometry

/-!
Bounded tests of the actual marginal pair equal the original
configuration-space integrals. These formulas connect the constructed
article-space pair to multiplication traces and covariant source tests.
-/

noncomputable section

namespace GptLean.PhysicalSourceH1

open MeasureTheory GptLean.PhysicalSourceFubini
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types false

variable {I J H : Type*} [Fintype I] [Fintype J]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [TopologicalSpace.SeparableSpace H]

theorem curry_tested_inner
    (u v : Lp H 2 ((volume : Measure (Position I)).prod (volume : Measure (Position J))))
    (a : Position I → ℝ) (ha : AEStronglyMeasurable a volume) {C : ℝ}
    (hb : ∀ᵐ x ∂volume, ‖a x‖ ≤ C) :
    (∫ x, a x • inner ℂ (curry u x) (curry v x)) =
      ∫ p, a p.1 • inner ℂ (u p) (v p) := by
  have hi := (L2.integrable_inner (𝕜 := ℂ) u v).bdd_smul C ha.comp_fst
    (Measure.quasiMeasurePreserving_fst.ae hb)
  calc
    _ = ∫ x, a x • (∫ y, inner ℂ (u (x, y)) (v (x, y))) := by
      apply integral_congr_ae
      filter_upwards [curry_inner_ae u v] with x hx
      rw [hx]
    _ = ∫ x, ∫ y, a x • inner ℂ (u (x, y)) (v (x, y)) := by
      simp_rw [integral_smul]
    _ = _ := (integral_prod _ hi).symm

theorem curry_tested_re_inner
    (u v : Lp H 2 ((volume : Measure (Position I)).prod (volume : Measure (Position J))))
    (a : Position I → ℝ) (ha : AEStronglyMeasurable a volume) {C : ℝ}
    (hb : ∀ᵐ x ∂volume, ‖a x‖ ≤ C) :
    (∫ x, a x * (inner ℂ (curry u x) (curry v x)).re) =
      ∫ p, a p.1 * (inner ℂ (u p) (v p)).re := by
  have hl := Complex.reCLM.integral_comp_comm
    ((L2.integrable_inner (𝕜 := ℂ) (curry u) (curry v)).bdd_smul C ha hb)
  have hr := Complex.reCLM.integral_comp_comm
    ((L2.integrable_inner (𝕜 := ℂ) u v).bdd_smul C ha.comp_fst
      (Measure.quasiMeasurePreserving_fst.ae hb))
  simp only [Complex.reCLM_apply, Pi.smul_apply', Complex.smul_re, smul_eq_mul] at hl hr
  exact hl.trans ((congrArg Complex.re (curry_tested_inner u v a ha hb)).trans hr.symm)

theorem curry_tested_norm_sq
    (u : Lp H 2 ((volume : Measure (Position I)).prod (volume : Measure (Position J))))
    (a : Position I → ℝ) (ha : AEStronglyMeasurable a volume) {C : ℝ}
    (hb : ∀ᵐ x ∂volume, ‖a x‖ ≤ C) :
    (∫ x, a x * ‖curry u x‖ ^ 2) = ∫ p, a p.1 * ‖u p‖ ^ 2 := by
  simpa [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal,
    ← Complex.ofReal_pow] using curry_tested_re_inner u u a ha hb

end GptLean.PhysicalSourceH1

namespace GptLean.PhysicalSourcePair

open MeasureTheory GptLean.ElectronicH1Space GptLean.PhysicalSourceCoordinates
open GptLean.PhysicalSourceMarginal GptLean.PhysicalSourceH1 GptLean.PhysicalSourceFubini
open GptLean.PhysicalPairSpace GptLean.PhysicalPairRealization

set_option backward.isDefEq.respectTransparency.types false

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [TopologicalSpace.SeparableSpace H]

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [TopologicalSpace.SeparableSpace H] in
theorem split_fst_eq_particle (i : Fin N) (z : Configuration N) :
    ((split i) z).1 = SymmetricLift.particle z i := by
  ext a
  rfl

theorem particleMap_tested_re_inner (i : Fin N) (v w : L2 H (Fin N × Fin 3))
    (a : PhysicalPairSpace.Position → ℝ) (ha : AEStronglyMeasurable a volume) {C : ℝ}
    (hb : ∀ᵐ x ∂volume, ‖a x‖ ≤ C) :
    (∫ x, a x * (inner ℂ (particleMap i v x) (particleMap i w x)).re) =
      ∫ z, a ((split i) z).1 * (inner ℂ (v z) (w z)).re := by
  calc
    _ = ∫ p, a p.1 * (inner ℂ
        (productMap (split i) (split_symm_measurePreserving i) v p)
        (productMap (split i) (split_symm_measurePreserving i) w p)).re :=
      curry_tested_re_inner _ _ a ha hb
    _ = ∫ p, a ((split i) ((split i).symm p)).1 *
        (inner ℂ (v ((split i).symm p)) (w ((split i).symm p))).re := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_compMeasurePreserving v (split_symm_measurePreserving i),
        Lp.coeFn_compMeasurePreserving w (split_symm_measurePreserving i)] with p hv hw
      change a p.1 * (inner ℂ
        (Lp.compMeasurePreserving (split i).symm (split_symm_measurePreserving i) v p)
        (Lp.compMeasurePreserving (split i).symm (split_symm_measurePreserving i) w p)).re = _
      rw [hv, hw]
      simp
    _ = _ := (split_symm_measurePreserving i).integral_comp
      (split i).symm.toHomeomorph.measurableEmbedding
      (fun z => a ((split i) z).1 * (inner ℂ (v z) (w z)).re)

theorem particleMap_tested_norm_sq (i : Fin N) (v : L2 H (Fin N × Fin 3))
    (a : PhysicalPairSpace.Position → ℝ) (ha : AEStronglyMeasurable a volume) {C : ℝ}
    (hb : ∀ᵐ x ∂volume, ‖a x‖ ≤ C) :
    (∫ x, a x * ‖particleMap i v x‖ ^ 2) =
      ∫ z, a ((split i) z).1 * ‖v z‖ ^ 2 := by
  simpa [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal,
    ← Complex.ofReal_pow] using particleMap_tested_re_inner i v v a ha hb

omit [TopologicalSpace.SeparableSpace H] in
theorem tested_current_ofSource (f : PhysicalPairSpace.Position → H)
    (d : Fin 3 → PhysicalPairSpace.Position → H)
    (hf₂ : MemLp f 2 volume) (hf₆ : MemLp f 6 volume)
    (hd : ∀ b, MemLp (d b) 2 volume) (b : Fin 3)
    (a : PhysicalPairSpace.Position → ℝ) :
    (∫ x, a x * currentL1 (ofSource N f d hf₂ hf₆ hd) x b) =
      (N : ℝ) * ∫ x, a x * (inner ℂ (f x) (d b x)).re := by
  calc
    _ = ∫ x, (N : ℝ) * (a x * (inner ℂ (f x) (d b x)).re) := by
      apply integral_congr_ae
      filter_upwards [current_ofSource_ae N f d hf₂ hf₆ hd] with x hx
      rw [hx, PhysicalPairIntegrability.current_apply]
      simp only [PhysicalPairIntegrability.currentComponent]
      ring
    _ = _ := integral_const_mul _ _

variable [CompleteSpace H]

theorem tested_density_ofWaveFunction (i : Fin N) (u : H1 H (Fin N × Fin 3))
    (d : Fin 3 → L2 H (Fin N × Fin 3))
    (a : PhysicalPairSpace.Position → ℝ) (ha : AEStronglyMeasurable a volume) {C : ℝ}
    (hb : ∀ᵐ x ∂volume, ‖a x‖ ≤ C) :
    (∫ x, a x * densityL1 (ofWaveFunction i u d) x) =
      (N : ℝ) * ∫ z, a ((split i) z).1 * ‖value u z‖ ^ 2 := by
  calc
    _ = ∫ x, (N : ℝ) * (a x * ‖particleMap i (value u) x‖ ^ 2) := by
      apply integral_congr_ae
      filter_upwards [density_ofSource_ae N (particleMap i (value u))
        (fun b => particleMap i (d b)) (Lp.memLp _) (particleSource_memLp_six i u)
        (fun _ => Lp.memLp _)] with x hx
      change a x * densityL1 (ofSource N _ _ _ _ _) x = _
      rw [hx]
      simp only [PhysicalPairIntegrability.density]
      ring
    _ = (N : ℝ) * (∫ x, a x * ‖particleMap i (value u) x‖ ^ 2) := integral_const_mul _ _
    _ = _ := congrArg (fun t : ℝ => (N : ℝ) * t)
      (particleMap_tested_norm_sq i (value u) a ha hb)

theorem tested_current_ofWaveFunction (i : Fin N) (u : H1 H (Fin N × Fin 3))
    (d : Fin 3 → L2 H (Fin N × Fin 3)) (b : Fin 3)
    (a : PhysicalPairSpace.Position → ℝ) (ha : AEStronglyMeasurable a volume) {C : ℝ}
    (hb : ∀ᵐ x ∂volume, ‖a x‖ ≤ C) :
    (∫ x, a x * currentL1 (ofWaveFunction i u d) x b) =
      (N : ℝ) * ∫ z, a ((split i) z).1 * (inner ℂ (value u z) (d b z)).re := by
  exact (tested_current_ofSource (particleMap i (value u))
    (fun c => particleMap i (d c)) (Lp.memLp _) (particleSource_memLp_six i u)
    (fun _ => Lp.memLp _) b a).trans
      (congrArg (fun t : ℝ => (N : ℝ) * t)
        (particleMap_tested_re_inner i (value u) (d b) a ha hb))

end GptLean.PhysicalSourcePair
