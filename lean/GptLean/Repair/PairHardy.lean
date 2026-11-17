import GptLean.Repair.CovariantHardy
import GptLean.PhysicalRelativeCoordinates

/-!
The pair Hardy estimate on actual configuration-space H1 vectors.
Relative-coordinate Fubini converts each inverse-square pair potential
to scalar Hardy on a Hilbert-valued source. The two choices of selected
particle give the exact coefficient two after averaging.
-/

noncomputable section

namespace GptLean.Repair

open MeasureTheory Filter SymmetricLift ElectronicH1Space PhysicalSourceFubini
  PhysicalSourceMarginal PhysicalSourceCoordinates PhysicalRelativeCoordinates
open scoped ENNReal Topology InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {I K J H : Type*} [Fintype I] [DecidableEq I]
  [Fintype K] [DecidableEq K] [Fintype J]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

/-- A real field expectation stays real after any measure-preserving
configuration split and integration over the spectator coordinates. -/
theorem sourceMap_inner_im_zero
    (L : EuclideanSpace ℝ I ≃L[ℝ] EuclideanSpace ℝ K × EuclideanSpace ℝ J)
    (hL : MeasurePreserving L.symm ((volume : Measure (EuclideanSpace ℝ K)).prod volume) volume)
    (v w : L2 H I)
    (h : ∀ᵐ x ∂volume, inner ℂ (v x) (w x) = inner ℂ (w x) (v x)) :
    ∀ᵐ x ∂volume,
      (inner ℂ (sourceMap L hL v x) (sourceMap L hL w x)).im = 0 := by
  have hp : ∀ᵐ p ∂(volume : Measure (EuclideanSpace ℝ K)).prod (volume : Measure (EuclideanSpace ℝ J)),
      inner ℂ (productMap L hL v p) (productMap L hL w p) =
        inner ℂ (productMap L hL w p) (productMap L hL v p) := by
    filter_upwards [hL.quasiMeasurePreserving.ae h,
      Lp.coeFn_compMeasurePreserving v hL, Lp.coeFn_compMeasurePreserving w hL]
      with p hp hv hw
    change inner ℂ (Lp.compMeasurePreserving L.symm hL v p)
      (Lp.compMeasurePreserving L.symm hL w p) =
        inner ℂ (Lp.compMeasurePreserving L.symm hL w p)
          (Lp.compMeasurePreserving L.symm hL v p)
    rw [hv, hw]
    exact hp
  filter_upwards [curry_inner_ae (productMap L hL v) (productMap L hL w),
    curry_inner_ae (productMap L hL w) (productMap L hL v),
    Measure.ae_ae_of_ae_prod hp] with x h₁ h₂ h₃
  have hs : inner ℂ (sourceMap L hL v x) (sourceMap L hL w x) =
      inner ℂ (sourceMap L hL w x) (sourceMap L hL v x) :=
    h₁.trans ((integral_congr_ae h₃).trans h₂.symm)
  exact Complex.conj_eq_iff_im.mp ((congrArg (starRingEnd ℂ) hs).trans
    (inner_conj_symm (sourceMap L hL v x) (sourceMap L hL w x)))

/-- Covariant differentiation commutes with the same source isometry. -/
theorem sourceMap_covariant_ae
    (L : EuclideanSpace ℝ I ≃L[ℝ] EuclideanSpace ℝ K × EuclideanSpace ℝ J)
    (hL : MeasurePreserving L.symm ((volume : Measure (EuclideanSpace ℝ K)).prod volume) volume)
    (d a D : L2 H I) (e : ℝ) (hD : D = (-Complex.I) • d - (e : ℂ) • a) :
    ∀ᵐ x ∂volume, sourceMap L hL D x =
      (-Complex.I) • sourceMap L hL d x - (e : ℂ) • sourceMap L hL a x := by
  have hm : sourceMap L hL D = (-Complex.I) • sourceMap L hL d -
      (e : ℂ) • sourceMap L hL a := by rw [hD, map_sub, map_smul, map_smul]
  filter_upwards [Lp.coeFn_sub ((-Complex.I) • sourceMap L hL d)
      ((e : ℂ) • sourceMap L hL a),
    Lp.coeFn_smul (-Complex.I) (sourceMap L hL d),
    Lp.coeFn_smul (e : ℂ) (sourceMap L hL a)] with x hs hd ha
  rw [hm]
  exact hs.trans (congrArg₂ (· - ·) hd ha)

/-- Fubini for a nonnegative, possibly unbounded multiplication weight.
Finiteness on the Hilbert-valued marginal implies finiteness on the
original product vector and equality of the two form integrals. -/
theorem product_weighted_norm_sq
    (v : Lp H 2 ((volume : Measure (EuclideanSpace ℝ K)).prod (volume : Measure (EuclideanSpace ℝ J))))
    (w : EuclideanSpace ℝ K → ℝ) (hw : AEStronglyMeasurable w volume)
    (hw0 : ∀ x, 0 ≤ w x)
    (hint : Integrable (fun x => w x * ‖curry v x‖ ^ 2) volume) :
    Integrable (fun p => w p.1 * ‖v p‖ ^ 2) (volume.prod volume) ∧
      (∫ p, w p.1 * ‖v p‖ ^ 2 ∂volume.prod volume) =
        ∫ x, w x * ‖curry v x‖ ^ 2 := by
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v)
  have hm : AEStronglyMeasurable (fun p => w p.1 * ‖v p‖ ^ 2) (volume.prod volume) :=
    hw.comp_fst.mul ((Lp.aestronglyMeasurable v).norm.pow 2)
  have hprod : Integrable (fun p => w p.1 * ‖v p‖ ^ 2) (volume.prod volume) := by
    apply (integrable_prod_iff hm).mpr
    refine ⟨?_, ?_⟩
    · filter_upwards [hi.prod_right_ae] with x hx
      exact hx.const_mul (w x)
    · apply hint.congr
      filter_upwards [curry_norm_sq_ae v] with x hx
      simp only [norm_mul, norm_pow, norm_norm, Real.norm_of_nonneg (hw0 x)]
      rw [integral_const_mul, hx]
  refine ⟨hprod, ?_⟩
  rw [integral_prod _ hprod]
  apply integral_congr_ae
  filter_upwards [curry_norm_sq_ae v] with x hx
  rw [integral_const_mul, hx]

variable {N : ℕ}

/-- One selected particle controls the inverse-square pair potential
with constant four. The source, field and derivative are actual L2
vectors on the full configuration space. -/
theorem pair_hardy_one_particle (Hardy : Representability.StandardScalarHardy)
    (i j : Fin N) (hij : i ≠ j) (u : H1 H (Fin N × Fin 3))
    (a D : Fin 3 → L2 H (Fin N × Fin 3)) (e : ℝ)
    (ha : ∀ b, ∀ᵐ x ∂volume, inner ℂ (value u x) (a b x) =
      inner ℂ (a b x) (value u x))
    (hD : ∀ b, D b = (-Complex.I) • derivative (i, b) u - (e : ℂ) • a b) :
    Integrable (fun x => (‖particle x i - particle x j‖ ^ 2)⁻¹ * ‖value u x‖ ^ 2) volume ∧
      (∫ x, (‖particle x i - particle x j‖ ^ 2)⁻¹ * ‖value u x‖ ^ 2) ≤
        4 * ∑ b : Fin 3, ‖D b‖ ^ 2 := by
  let L := relativeSplit i j hij
  let hL := relativeSplit_symm_measurePreserving i j hij
  let s := relativeSource i j hij u
  have hc := covariant_hardy Hardy (weak s) (Lp.memLp (value s))
    (fun b => Lp.memLp (derivative b s))
    (fun b => Lp.memLp (sourceMap L hL (D b))) e
    (fun b => sourceMap_inner_im_zero L hL (value u) (a b) (ha b))
    (fun b => sourceMap_covariant_ae L hL (derivative (i, b) u) (a b) (D b) e (hD b)) 0
  simp only [sub_zero, ← Lp.norm_def, (sourceMap L hL).norm_map] at hc
  have hp := product_weighted_norm_sq (productMap L hL (value u))
    (fun x => (‖x‖ ^ 2)⁻¹)
    (continuous_norm.measurable.pow_const 2).inv.aestronglyMeasurable
    (fun x => inv_nonneg.mpr (sq_nonneg _)) hc.1
  have hrep : (fun p : EuclideanSpace ℝ (Fin 3) × Spectator i =>
      (‖p.1‖ ^ 2)⁻¹ * ‖productMap L hL (value u) p‖ ^ 2) =ᵐ[volume.prod volume]
      fun p => (‖(L (L.symm p)).1‖ ^ 2)⁻¹ * ‖value u (L.symm p)‖ ^ 2 := by
    filter_upwards [Lp.coeFn_compMeasurePreserving (value u) hL] with p hp
    change (‖p.1‖ ^ 2)⁻¹ * ‖Lp.compMeasurePreserving L.symm hL (value u) p‖ ^ 2 = _
    rw [hp, ContinuousLinearEquiv.apply_symm_apply]
    rfl
  have hi := (hL.integrable_comp_emb
    (g := fun x => (‖(L x).1‖ ^ 2)⁻¹ * ‖value u x‖ ^ 2)
    L.symm.toHomeomorph.measurableEmbedding).mp (hp.1.congr hrep)
  have he : (∫ x, (‖(L x).1‖ ^ 2)⁻¹ * ‖value u x‖ ^ 2) =
      ∫ x, (‖x‖ ^ 2)⁻¹ * ‖value s x‖ ^ 2 := by
    calc
      _ = ∫ p, (‖(L (L.symm p)).1‖ ^ 2)⁻¹ * ‖value u (L.symm p)‖ ^ 2
          ∂volume.prod volume :=
        (hL.integral_comp L.symm.toHomeomorph.measurableEmbedding _).symm
      _ = ∫ p, (‖p.1‖ ^ 2)⁻¹ * ‖productMap L hL (value u) p‖ ^ 2
          ∂volume.prod volume :=
        integral_congr_ae hrep.symm
      _ = _ := hp.2
  refine ⟨?_, ?_⟩
  · simpa only [L, relativeSplit_fst] using hi
  · have hb := he.trans_le hc.2
    simpa only [L, relativeSplit_fst] using hb

/-- The exact pair coefficient used in Appendix C follows by applying
the proved one-particle estimate in both orientations. -/
theorem pair_hardy_covariant (Hardy : Representability.StandardScalarHardy)
    (i j : Fin N) (hij : i ≠ j) (u : H1 H (Fin N × Fin 3))
    (a D : Fin N × Fin 3 → L2 H (Fin N × Fin 3)) (e : ℝ)
    (ha : ∀ q, ∀ᵐ x ∂volume, inner ℂ (value u x) (a q x) =
      inner ℂ (a q x) (value u x))
    (hD : ∀ q, D q = (-Complex.I) • derivative q u - (e : ℂ) • a q) :
    Integrable (fun x => (‖particle x i - particle x j‖ ^ 2)⁻¹ * ‖value u x‖ ^ 2) volume ∧
      (∫ x, (‖particle x i - particle x j‖ ^ 2)⁻¹ * ‖value u x‖ ^ 2) ≤
        2 * ((∑ b : Fin 3, ‖D (i, b)‖ ^ 2) + ∑ b : Fin 3, ‖D (j, b)‖ ^ 2) := by
  have hi := pair_hardy_one_particle Hardy i j hij u (fun b => a (i, b))
    (fun b => D (i, b)) e (fun b => ha (i, b)) (fun b => hD (i, b))
  have hj := pair_hardy_one_particle Hardy j i hij.symm u (fun b => a (j, b))
    (fun b => D (j, b)) e (fun b => ha (j, b)) (fun b => hD (j, b))
  have hs : (∫ x, (‖particle x j - particle x i‖ ^ 2)⁻¹ * ‖value u x‖ ^ 2) =
      ∫ x, (‖particle x i - particle x j‖ ^ 2)⁻¹ * ‖value u x‖ ^ 2 :=
    integral_congr_ae (ae_of_all _ fun x =>
      congrArg (fun r : ℝ => (r ^ 2)⁻¹ * ‖value u x‖ ^ 2)
        (norm_sub_rev (particle x j) (particle x i)))
  have hj' := hs.symm.trans_le hj.2
  exact ⟨hi.1, by linarith [hi.2, hj']⟩

/-- The actual pair-energy multiplier in the symmetric lift is integrable
on every covariant H1 vector. Each particle derivative occurs N minus one
times, giving the constant used by general current repair. -/
theorem pairEnergy_covariant (Hardy : Representability.StandardScalarHardy)
    (u : H1 H (Fin N × Fin 3))
    (a D : Fin N × Fin 3 → L2 H (Fin N × Fin 3)) (e : ℝ)
    (ha : ∀ q, ∀ᵐ x ∂volume, inner ℂ (value u x) (a q x) =
      inner ℂ (a q x) (value u x))
    (hD : ∀ q, D q = (-Complex.I) • derivative q u - (e : ℂ) • a q) :
    Integrable (fun x => pairEnergy x * ‖value u x‖ ^ 2) volume ∧
      (∫ x, pairEnergy x * ‖value u x‖ ^ 2) ≤
        2 * (N - 1 : ℝ) * ∑ q, ‖D q‖ ^ 2 := by
  let P := fun i j : Fin N =>
    ∫ x, (‖particle x i - particle x j‖ ^ 2)⁻¹ * ‖value u x‖ ^ 2
  let d := fun i : Fin N => ∑ b : Fin 3, ‖D (i, b)‖ ^ 2
  have hP (i j : Fin N) : P i j = P j i :=
    integral_congr_ae (ae_of_all _ fun x =>
      congrArg (fun r : ℝ => (r ^ 2)⁻¹ * ‖value u x‖ ^ 2)
        (norm_sub_rev (particle x i) (particle x j)))
  have hb := pair_hardy_sum d P (fun i j hij =>
    (pair_hardy_covariant Hardy i j hij u a D e ha hD).2)
  have hi (i j : Fin N) : Integrable (fun x =>
      (if i < j then (pairDistance x i j ^ 2)⁻¹ else 0) * ‖value u x‖ ^ 2) volume := by
    by_cases hij : i < j
    · simpa only [if_pos hij, pairDistance] using
        (pair_hardy_covariant Hardy i j (ne_of_lt hij) u a D e ha hD).1
    · simp only [if_neg hij, zero_mul]
      exact integrable_zero _ _ _
  have hfinite : Integrable (fun x => pairEnergy x * ‖value u x‖ ^ 2) volume := by
    simp only [pairEnergy, Finset.sum_mul]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hi i j
  have hv : (∫ x, pairEnergy x * ‖value u x‖ ^ 2) =
      ∑ i : Fin N, ∑ j : Fin N, if i < j then P i j else 0 := by
    simp only [pairEnergy, Finset.sum_mul]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hi i j)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j _ => hi i j)]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i < j
    · simp only [if_pos hij]
      rfl
    · simp only [if_neg hij, zero_mul, integral_zero]
  rw [half_ordered_pair_sum P hP] at hb
  refine ⟨hfinite, hv.trans_le ?_⟩
  simpa only [d, Fintype.sum_prod_type] using hb

end GptLean.Repair
