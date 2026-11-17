import GptLean.PhysicalFockPhysicalForms
import GptLean.PhysicalFockNumberMoments
import GptLean.PhysicalFockChannelReference
import GptLean.PhysicalFockChannelMoments

/-!
The localized number estimate on the actual Fourier/Fock model. The
only analytic input is the universal fractional Hardy inequality for
Hilbert-valued functions on three-dimensional Euclidean space. Exact
Fubini identifies its Fourier energy with the physical radiation form.
-/

noncomputable section
namespace GptLean.PhysicalPhotonLocalizedNumber

open MeasureTheory PhysicalFock PhysicalOnePhotonFourier Gaussian
  PhotonLocalizationChannel PhotonLocalizationFormBounds PhotonLocalizationKernelCutoffs
  PhotonLocalizationFockChannel
  PhysicalNormalTrace PhysicalNormalTrace.StandardNormalTraceBackground
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false

def halfEnergy {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (u : Lp E 2 (volume : Measure FieldSpace)) : ℝ≥0∞ :=
  ∫⁻ k, ENNReal.ofReal ‖k‖ *
    ENNReal.ofReal (‖Lp.fourierTransformₗᵢ FieldSpace E u k‖ ^ 2)

/-- A standard Fourier fractional Hardy theorem, with no physical data. -/
structure StandardFractionalHardy where
  constant : ℝ
  constant_pos : 0 < constant
  integrable : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (u : Lp E 2 (volume : Measure FieldSpace)), halfEnergy u ≠ ⊤ →
      Integrable (fun y => ‖u y‖ ^ 2 / ‖y‖) volume
  bound : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (u : Lp E 2 (volume : Measure FieldSpace)), halfEnergy u ≠ ⊤ →
      (∫ y, ‖u y‖ ^ 2 / ‖y‖) ≤ constant * (halfEnergy u).toReal

theorem radiation_value (u : PositionSpace) :
    onePhotonFamilyValue radiationFamily (fourier u) = halfEnergy u := by
  rw [radiationFamily_value]
  have hc : PhysicalSourceFubini.curry (fourier u) =
      Lp.fourierTransformₗᵢ FieldSpace Polarization u :=
    PhysicalSourceFubini.curryEquiv.apply_symm_apply _
  have hm : AEMeasurable (fun p : FieldSpace × Fin 2 =>
      ENNReal.ofReal ‖p.1‖ * ENNReal.ofReal (‖fourier u p‖ ^ 2)) photonMeasure := by
    exact ((measurable_fst.norm.ennreal_ofReal).mul
      ((Lp.stronglyMeasurable (fourier u)).norm.measurable.pow_const 2).ennreal_ofReal).aemeasurable
  refine (lintegral_prod _ hm).trans ?_
  apply lintegral_congr_ae
  filter_upwards [PhysicalSourceFubini.curry_norm_sq_ae (fourier u),
    PhysicalSourceFubini.section_memLp_ae (fourier u)] with k hk hmem
  rw [hc] at hk
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply congrArg (fun t : ℝ≥0∞ => ENNReal.ofReal ‖k‖ * t)
  exact (ofReal_integral_eq_lintegral_ofReal
    ((memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).mp hmem)
    (ae_of_all _ fun _ => sq_nonneg _)).symm.trans
      (congrArg ENNReal.ofReal hk.symm)

private theorem full_value (BF : StandardSymmetricFockExponential)
    (C : CanonicalSectorCCR photonMeasure) (B : StandardNormalTraceBackground)
    (N : ℕ) (q : OnePhotonFormFamily) (u : PositionSpace) :
    (fullFormCalculus BF C B fourier N).value q u =
      onePhotonFamilyValue q (fourier u) := rfl

variable (Hardy : StandardFractionalHardy)

def numberConstant (m : ℕ) : ℝ := 2 * Hardy.constant * radius m

theorem numberConstant_pos (m : ℕ) : 0 < numberConstant Hardy m :=
  mul_pos (mul_pos (by norm_num) Hardy.constant_pos) (radius_pos m)

theorem localized_number_le (BF : StandardSymmetricFockExponential)
    (C : CanonicalSectorCCR photonMeasure) (B : StandardNormalTraceBackground) (N m : ℕ)
    {x : B.FullTrace N} (hx : x ∈ (B.realization (FullHilbert N)).rank.positive) :
    (fullNumberForm B N).expectation (B.normal.extend (physicalKraus BF N m) x) ≤
      ENNReal.ofReal (numberConstant Hardy m) *
        (PhysicalPhotonMarginal.fullForm B (volume : Measure (SymmetricLift.Configuration N))
          (NormalPhoton.radiationForm B.normal (B.realization PhotonFock).functional)).expectation x := by
  have hval (u : PositionSpace) :
      (fullFormCalculus BF C B fourier N).value radiationFamily u = halfEnergy u :=
    (full_value BF C B N radiationFamily u).trans (radiation_value u)
  have hweighted (u : PositionSpace)
      (hu : (fullFormCalculus BF C B fourier N).value radiationFamily u ≠ ⊤) :
      Integrable (fun y => ‖u y‖ ^ 2 / ‖y‖) volume :=
    Hardy.integrable Polarization u (fun ht => hu ((hval u).trans ht))
  have hHardy (u : PositionSpace)
      (hu : (fullFormCalculus BF C B fourier N).value radiationFamily u ≠ ⊤) :
      (∫ y, ‖u y‖ ^ 2 / ‖y‖) ≤
        Hardy.constant * ((fullFormCalculus BF C B fourier N).value radiationFamily u).toReal :=
    (Hardy.bound Polarization u (fun ht => hu ((hval u).trans ht))).trans_eq
      (congrArg (fun t : ℝ≥0∞ => Hardy.constant * t.toReal) (hval u).symm)
  have h := localized_number_le_radiation
    (fullFormCalculus BF C B fourier N) B.normal (fun _ hx => hx)
    numberFamily radiationFamily (fun u =>
      (full_value BF C B N numberFamily u).trans
        ((numberFamily_value (fourier u)).trans
          (congrArg (fun t : ℝ => ENNReal.ofReal (t ^ 2)) (fourier.norm_map u))))
    (radius_pos m) Hardy.constant_pos
    (by filter_upwards [volume.ae_ne (0 : FieldSpace)] with y hy
        exact norm_pos_iff.mpr hy)
    hweighted hHardy hx
  exact (fullFormCalculus_number_eq BF C B fourier N
    (B.normal.positive (physicalKraus BF N m) hx)).symm.le.trans
      (h.trans_eq (congrArg
        (fun t : ℝ≥0∞ => ENNReal.ofReal (numberConstant Hardy m) * t)
        (fullFormCalculus_radiation_eq BF C B fourier N hx)))

private theorem cutoff_coordinate (M n : ℕ) (u : PhotonFock) :
    cutoff (Sector photonMeasure) M u n = if n ≤ M then u n else 0 := by
  simp only [cutoff, sum_apply, lp.coeFn_sum, Finset.sum_apply]
  by_cases hn : n ≤ M
  · rw [ite_eq_left hn]
    calc
      _ = sector (Sector photonMeasure) n u n :=
        Finset.sum_eq_single n
          (fun j _ h => sector_coordinate_ne (Sector photonMeasure) j n h.symm u)
          (fun h => False.elim (h (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))))
      _ = _ := PhysicalFock.sector_coordinate (Sector photonMeasure) n u
  · rw [ite_eq_right hn]
    apply Finset.sum_eq_zero
    intro j hj
    apply sector_coordinate_ne
    have hjM := Finset.mem_range.mp hj
    omega

private theorem tail_operator (M : ℕ)
    (hw : ∀ n, |(tailWeight M).val n| ≤ 1) :
    boundedWeightOperator (Sector photonMeasure) (tailWeight M).val hw =
      1 - cutoff (Sector photonMeasure) M := by
  apply ContinuousLinearMap.ext
  intro u
  apply lp.ext
  funext n
  simp only [boundedWeightOperator_apply, sub_apply, one_apply_eq_self, lp.coeFn_sub,
    Pi.sub_apply, cutoff_coordinate, tailWeight]
  by_cases hn : n ≤ M
  · simp only [ite_eq_left hn, ite_eq_right (not_lt.mpr hn), Complex.ofReal_zero, zero_smul, sub_self]
  · simp only [ite_eq_right hn, ite_eq_left (lt_of_not_ge hn), Complex.ofReal_one, one_smul, sub_zero]

private theorem compLpL_complement {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [NormedSpace ℂ H] (μ : Measure X) (P : H →L[ℂ] H) :
    1 - P.compLpL 2 μ = (1 - P).compLpL 2 μ := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [(1 - P).coeFn_compLpL u, P.coeFn_compLpL u,
    Lp.coeFn_sub u (P.compLpL 2 μ u)] with y h₁ h₂ h₃
  change (u - P.compLpL 2 μ u) y = _
  exact h₃.trans ((congrArg (fun z : H => u y - z) h₂).trans h₁.symm)

theorem full_tail_eq (B : StandardNormalTraceBackground) (N M : ℕ)
    (x : B.FullTrace N) :
    ((B.realization (FullHilbert N)).functional.repr x
      (1 - (cutoff (Sector photonMeasure) M).compLpL 2 volume)).re =
        FullNumberLaw.tail (volume : Measure (SymmetricLift.Configuration N)) B M x := by
  have hw (n : ℕ) : |(tailWeight M).val n| ≤ 1 := by
    rw [abs_of_nonneg ((tailWeight M).property n).1]
    exact ((tailWeight M).property n).2
  have ht := congrArg (fun A : PhotonFock →L[ℂ] PhotonFock =>
    A.compLpL 2 (volume : Measure (SymmetricLift.Configuration N))) (tail_operator M hw)
  change _ = ((B.realization (FullHilbert N)).functional.repr x
    ((boundedWeightOperator (Sector photonMeasure) (tailWeight M).val hw).compLpL 2 volume)).re
  exact congrArg (fun a => ((B.realization (FullHilbert N)).functional.repr x a).re)
    ((compLpL_complement (volume : Measure (SymmetricLift.Configuration N))
      (cutoff (Sector photonMeasure) M)).trans ht.symm)

theorem number_tail_bound (B : StandardNormalTraceBackground) (N M : ℕ)
    {x : B.FullTrace N} (hx : x ∈ (B.realization (FullHilbert N)).rank.positive)
    {b : ℝ} (hb : 0 ≤ b) (hnumber : (fullNumberForm B N).expectation x ≤ ENNReal.ofReal b) :
    ((B.realization (FullHilbert N)).functional.repr x
      (1 - (cutoff (Sector photonMeasure) M).compLpL 2 volume)).re ≤ b / (M + 1) := by
  rw [full_tail_eq]
  apply (ChannelMoments.tail_markov (volume : Measure (SymmetricLift.Configuration N)) B M hx
    (hnumber.trans_lt ENNReal.ofReal_lt_top)).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hnumber).trans_eq (ENNReal.toReal_ofReal hb)

end GptLean.PhysicalPhotonLocalizedNumber
