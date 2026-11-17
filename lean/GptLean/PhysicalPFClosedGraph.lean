import GptLean.PhysicalPFReference

/-!
Closedness of the common physical form graph. The graph records the same
wave function, all covariant derivatives, the radiation square root and
the Coulomb square root. Its inverse is bounded by the proved field
estimate, so closedness follows from completeness of the reference domain.
-/

noncomputable section

namespace GptLean.PhysicalPFReference

open MeasureTheory PhysicalFock
open scoped NNReal

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

private theorem norm_covariant_inverse {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (u v : H) (e : ℝ) : ‖u‖ ≤ ‖(-Complex.I) • u - (e : ℂ) • v‖ + |e| * ‖v‖ := by
  calc
    ‖u‖ = ‖(-Complex.I) • u‖ := by simp [norm_smul]
    _ = ‖((-Complex.I) • u - (e : ℂ) • v) + (e : ℂ) • v‖ := by
      rw [sub_add_cancel]
    _ ≤ ‖(-Complex.I) • u - (e : ℂ) • v‖ + ‖(e : ℂ) • v‖ := norm_add_le _ _
    _ = _ := by rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]

theorem closed_range_of_norm_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : E →L[ℂ] F) (b : ℝ≥0) (h : ∀ u, ‖u‖ ≤ b * ‖L u‖) :
    IsClosed (Set.range L) :=
  (L.antilipschitz_of_bound (K := b) h).isClosed_range L.uniformContinuous

variable (I : Type*) [Fintype I] [DecidableEq I]
  (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M)

abbrev FormCoordinates := WaveSpace I × (I → WaveSpace I) × WaveSpace I × WaveSpace I

def formGraphMap (e : ℝ) : Reference I V →L[ℂ] FormCoordinates I :=
  (inclusion I V).prod ((ContinuousLinearMap.pi (covariant I V C κ hκ M hbound e)).prod
    ((radiation I V).prod (potential I V)))

def fieldBound : ℝ := ∑ i, ‖spatialField volume C (κ i) (hκ i) M (hbound i)‖

omit [DecidableEq I] in
theorem fieldBound_nonneg : 0 ≤ fieldBound I C κ hκ M hbound :=
  Finset.sum_nonneg fun i _ => (spatialField volume C (κ i) (hκ i) M (hbound i)).opNorm_nonneg

theorem field_norm_le (i : I) (u : Reference I V) :
    ‖field I V C κ hκ M hbound i u‖ ≤
      fieldBound I C κ hκ M hbound * (‖inclusion I V u‖ + ‖radiation I V u‖) := by
  have hb : ‖spatialField volume C (κ i) (hκ i) M (hbound i)‖ ≤
      fieldBound I C κ hκ M hbound :=
    Finset.single_le_sum (fun j _ =>
      (spatialField volume C (κ j) (hκ j) M (hbound j)).opNorm_nonneg) (Finset.mem_univ i)
  exact ((spatialField volume C (κ i) (hκ i) M (hbound i)).le_opNorm
    (radiationSource I V u)).trans (mul_le_mul hb (radiationSource_norm_le I V u)
      (norm_nonneg _) (fieldBound_nonneg I C κ hκ M hbound))

theorem ordinary_norm_le (e : ℝ) (i : I) (u : Reference I V) :
    ‖ordinary I V i u‖ ≤ ‖covariant I V C κ hκ M hbound e i u‖ +
      |e| * ‖field I V C κ hκ M hbound i u‖ :=
  norm_covariant_inverse (ordinary I V i u) (field I V C κ hκ M hbound i u) e

def formComparisonConstant (e : ℝ) : ℝ :=
  2 + 2 * |e| * fieldBound I C κ hκ M hbound

omit [DecidableEq I] in
theorem formComparisonConstant_nonneg (e : ℝ) :
    0 ≤ formComparisonConstant I C κ hκ M hbound e := by
  unfold formComparisonConstant
  have := fieldBound_nonneg I C κ hκ M hbound
  positivity

theorem reference_norm_le_formGraph (e : ℝ) (u : Reference I V) :
    ‖u‖ ≤ formComparisonConstant I C κ hκ M hbound e *
      ‖formGraphMap I V C κ hκ M hbound e u‖ := by
  let G := ‖formGraphMap I V C κ hκ M hbound e u‖
  let K := fieldBound I C κ hκ M hbound
  have hG : 0 ≤ G := norm_nonneg _
  have hK : 0 ≤ K := fieldBound_nonneg I C κ hκ M hbound
  have hi : ‖inclusion I V u‖ ≤ G := norm_fst_le (formGraphMap I V C κ hκ M hbound e u)
  have htail : ‖(formGraphMap I V C κ hκ M hbound e u).2‖ ≤ G :=
    norm_snd_le (formGraphMap I V C κ hκ M hbound e u)
  have hd : ∀ i, ‖covariant I V C κ hκ M hbound e i u‖ ≤ G := fun i =>
    (norm_le_pi_norm (formGraphMap I V C κ hκ M hbound e u).2.1 i).trans
      ((norm_fst_le _).trans htail)
  have hr : ‖radiation I V u‖ ≤ G :=
    (norm_fst_le (formGraphMap I V C κ hκ M hbound e u).2.2).trans
      ((norm_snd_le _).trans htail)
  have hp : ‖potential I V u‖ ≤ G :=
    (norm_snd_le (formGraphMap I V C κ hκ M hbound e u).2.2).trans
      ((norm_snd_le _).trans htail)
  have hf : ∀ i, ‖field I V C κ hκ M hbound i u‖ ≤ 2 * K * G := by
    intro i
    calc
      _ ≤ K * (‖inclusion I V u‖ + ‖radiation I V u‖) :=
        field_norm_le I V C κ hκ M hbound i u
      _ ≤ K * (G + G) := mul_le_mul_of_nonneg_left (add_le_add hi hr) hK
      _ = _ := by ring
  have ho : ∀ i, ‖ordinary I V i u‖ ≤ (2 + 2 * |e| * K) * G := by
    intro i
    have hn := (ordinary_norm_le I V C κ hκ M hbound e i u).trans
      (add_le_add (hd i) (mul_le_mul_of_nonneg_left (hf i) (abs_nonneg e)))
    nlinarith
  have hi' : ‖inclusion I V u‖ ≤ (2 + 2 * |e| * K) * G := by
    nlinarith [mul_nonneg (abs_nonneg e) hK]
  have hr' : ‖radiationSource I V u‖ ≤ (2 + 2 * |e| * K) * G := by
    have h := (radiationSource_norm_le I V u).trans (add_le_add hi hr)
    nlinarith [mul_nonneg (abs_nonneg e) hK]
  have hp' : ‖potentialSource I V u‖ ≤ (2 + 2 * |e| * K) * G := by
    exact (potentialSource_norm I V u).le.trans
      (max_le hi' (hp.trans (by nlinarith [mul_nonneg (abs_nonneg e) hK])))
  change max ‖electronic I V u‖ (max ‖radiationSource I V u‖ ‖potentialSource I V u‖) ≤
    (2 + 2 * |e| * K) * G
  exact max_le ((ElectronicH1Complex.norm_eq_max (electronic I V u)).le.trans
    (max_le hi' ((pi_norm_le_iff_of_nonneg (by positivity)).mpr ho))) (max_le hr' hp')

set_option backward.isDefEq.respectTransparency.types true in
/-- No form-closedness premise is supplied. -/
theorem formGraph_closed (e : ℝ) :
    IsClosed (Set.range (formGraphMap I V C κ hκ M hbound e)) := by
  let B : ℝ≥0 := ⟨formComparisonConstant I C κ hκ M hbound e,
    formComparisonConstant_nonneg I C κ hκ M hbound e⟩
  apply closed_range_of_norm_bound (E := Reference I V) (F := FormCoordinates I)
    (formGraphMap I V C κ hκ M hbound e) B
  intro u
  exact reference_norm_le_formGraph I V C κ hκ M hbound e u

end GptLean.PhysicalPFReference
