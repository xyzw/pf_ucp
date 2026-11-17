import GptLean.PhysicalFockNumberMoments
import GptLean.PhysicalFockFullNumberLaw

/-!
The actual bounded joint-number laws determine the unbounded number
moments by nonnegative disintegration. This gives number decrease and
the spectral Markov bound on the same full normal state space.
-/

noncomputable section
namespace GptLean.PhysicalFock.ChannelMoments

open MeasureTheory PhotonLocalizationChannel PhotonLocalizationFockChannel
open PhysicalNormalTrace ChannelNumber
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false

private theorem hasSum_limit {ι : Type*} {f : ι → ℝ} {a b : ℝ}
    (hf : HasSum f a) (hab : a = b) : HasSum f b := hab ▸ hf

private def singletonWeight (n k : ℕ) : ℝ := if k = n then 1 else 0

private theorem singleton_bound (n k : ℕ) : |singletonWeight n k| ≤ 1 := by
  unfold singletonWeight
  split_ifs <;> norm_num

private theorem singleton_nonneg (n k : ℕ) : 0 ≤ singletonWeight n k := by
  unfold singletonWeight
  split_ifs <;> norm_num

private theorem singleton_operator
    (K : ℕ → Type*) [∀ n, NormedAddCommGroup (K n)]
    [∀ n, InnerProductSpace ℂ (K n)] (n : ℕ) :
    boundedWeightOperator K (singletonWeight n) (singleton_bound n) = PhysicalFock.sector K n := by
  apply ContinuousLinearMap.ext
  intro u
  apply lp.ext
  funext k
  rw [boundedWeightOperator_apply, PhysicalFock.sector_apply]
  by_cases hk : k = n
  · subst k
    simp only [singletonWeight, ite_true, Complex.ofReal_one, one_smul, lp.single_apply_self]
  · rw [lp.single_apply_ne _ _ _ hk]
    simp only [singletonWeight, ite_eq_right hk, Complex.ofReal_zero, zero_smul]

variable {X : Type} [MeasurableSpace X] (μ : Measure X) [IsSeparable μ]
  (BF : StandardSymmetricFockExponential) (BT : StandardNormalTraceBackground)

theorem full_weight_sectors (w : ℕ → ℝ) (hw : ∀ n, |w n| ≤ 1) (hpos : ∀ n, 0 ≤ w n)
    {x : BT.Trace (Lp PhotonFock 2 μ)}
    (hx : x ∈ (BT.realization (Lp PhotonFock 2 μ)).rank.positive) :
    HasSum (fun n => w n * NumberMoments.sector BT μ n x) (fullNumberTest μ BT w hw x) := by
  have h := boundedWeightTrace_hasSum (Sector photonMeasure) BT.normal
    (BT.realization PhotonFock).functional w hw hpos (PhysicalPhotonMarginal.marginal_positive BT μ hx)
  have he : fullNumberTest μ BT w hw x =
      boundedWeightTrace (Sector photonMeasure) (BT.realization PhotonFock).functional w hw
        (PhysicalPhotonMarginal.marginal BT μ x) :=
    congrArg Complex.re (PhysicalPhotonMarginal.marginal_evaluation BT μ
      (boundedWeightOperator (Sector photonMeasure) w hw) hx).symm
  exact hasSum_limit h he.symm

theorem full_singleton (n : ℕ) {x : BT.Trace (Lp PhotonFock 2 μ)}
    (hx : x ∈ (BT.realization (Lp PhotonFock 2 μ)).rank.positive) :
    fullNumberTest μ BT (singletonWeight n) (singleton_bound n) x =
      NumberMoments.sector BT μ n x := by
  change ((BT.realization (Lp PhotonFock 2 μ)).functional.repr x
    ((boundedWeightOperator (Sector photonMeasure) (singletonWeight n) (singleton_bound n)).compLpL 2 μ)).re =
      ((BT.realization PhotonFock).functional.repr (PhysicalPhotonMarginal.marginal BT μ x)
        (PhysicalFock.sector (Sector photonMeasure) n)).re
  exact (congrArg (fun A : PhotonFock →L[ℂ] PhotonFock =>
    ((BT.realization (Lp PhotonFock 2 μ)).functional.repr x (A.compLpL 2 μ)).re)
      (singleton_operator (Sector photonMeasure) n)).trans
        (congrArg Complex.re (PhysicalPhotonMarginal.marginal_evaluation BT μ
          (PhysicalFock.sector (Sector photonMeasure) n) hx).symm)

variable (j : Lp ℂ 2 photonMeasure →ₗᵢ[ℂ]
  WithLp 2 (Lp ℂ 2 photonMeasure × Lp ℂ 2 photonMeasure))

theorem total_moment {x : BT.Trace (Lp PhotonFock 2 μ)}
    (hx : x ∈ (BT.realization (Lp PhotonFock 2 μ)).rank.positive) :
    (PhysicalPhotonMarginal.fullForm BT μ
      (NormalPhoton.numberForm BT.normal (BT.realization PhotonFock).functional)).expectation x =
      ∑' p : ℕ × ℕ, ENNReal.ofReal (((p.1 + p.2 : ℕ) : ℝ) * fullJointEffect μ BF BT j p x) := by
  refine (NumberMoments.full_number_sectors BT μ hx).trans ?_
  apply NumberMoments.moment_disintegration (fun p => fullJointEffect μ BF BT j p x)
    (fun p => FullNumberLaw.joint_nonneg μ BF BT j p hx)
    (fun n => NumberMoments.sector BT μ n x) (fun p => p.1 + p.2)
  intro n
  have h := full_total_hasSum μ BF BT j (singletonWeight n) (singleton_bound n)
    (singleton_nonneg n) hx
  have h' := hasSum_limit h (full_singleton μ BT n hx)
  simpa only [singletonWeight, ite_mul, one_mul, zero_mul] using h'

theorem retained_moment {x : BT.Trace (Lp PhotonFock 2 μ)}
    (hx : x ∈ (BT.realization (Lp PhotonFock 2 μ)).rank.positive) :
    (PhysicalPhotonMarginal.fullForm BT μ
      (NormalPhoton.numberForm BT.normal (BT.realization PhotonFock).functional)).expectation
        (BT.normal.extend ((electronicFactorization μ (photonFactorization BF)).factor j) x) =
      ∑' p : ℕ × ℕ, ENNReal.ofReal ((p.1 : ℝ) * fullJointEffect μ BF BT j p x) := by
  have hout := BT.normal.positive ((electronicFactorization μ (photonFactorization BF)).factor j) hx
  refine (NumberMoments.full_number_sectors BT μ hout).trans ?_
  apply NumberMoments.moment_disintegration (fun p => fullJointEffect μ BF BT j p x)
    (fun p => FullNumberLaw.joint_nonneg μ BF BT j p hx)
    (fun n => NumberMoments.sector BT μ n
      (BT.normal.extend ((electronicFactorization μ (photonFactorization BF)).factor j) x)) Prod.fst
  intro n
  have h := full_retained_hasSum μ BF BT j (singletonWeight n) (singleton_bound n)
    (singleton_nonneg n) hx
  have h' := hasSum_limit h (full_singleton μ BT n hout)
  simpa only [singletonWeight, ite_mul, one_mul, zero_mul] using h'

theorem number_decrease {x : BT.Trace (Lp PhotonFock 2 μ)}
    (hx : x ∈ (BT.realization (Lp PhotonFock 2 μ)).rank.positive) :
    (PhysicalPhotonMarginal.fullForm BT μ
      (NormalPhoton.numberForm BT.normal (BT.realization PhotonFock).functional)).expectation
        (BT.normal.extend ((electronicFactorization μ (photonFactorization BF)).factor j) x) ≤
      (PhysicalPhotonMarginal.fullForm BT μ
        (NormalPhoton.numberForm BT.normal (BT.realization PhotonFock).functional)).expectation x := by
  apply (retained_moment μ BF BT j hx).le.trans
  apply le_trans _ (total_moment μ BF BT j hx).symm.le
  apply ENNReal.tsum_le_tsum
  intro p
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_add_right p.1 p.2)
    (FullNumberLaw.joint_nonneg μ BF BT j p hx)

theorem tail_markov (M : ℕ) {x : BT.Trace (Lp PhotonFock 2 μ)}
    (hx : x ∈ (BT.realization (Lp PhotonFock 2 μ)).rank.positive)
    (hfinite : (PhysicalPhotonMarginal.fullForm BT μ
      (NormalPhoton.numberForm BT.normal (BT.realization PhotonFock).functional)).expectation x < ⊤) :
    FullNumberLaw.tail μ BT M x ≤
      ((PhysicalPhotonMarginal.fullForm BT μ
        (NormalPhoton.numberForm BT.normal (BT.realization PhotonFock).functional)).expectation x).toReal /
          ((M : ℝ) + 1) := by
  have ht := full_weight_sectors μ BT (tailWeight M).val
    (fun n => by rw [abs_of_nonneg ((tailWeight M).property n).1]; exact ((tailWeight M).property n).2)
    (fun n => ((tailWeight M).property n).1) hx
  have he : FullNumberLaw.tail μ BT M x =
      ∑' n, if M < n then NumberMoments.sector BT μ n x else 0 := by
    simpa only [FullNumberLaw.tail, tailWeight, ite_mul, one_mul, zero_mul] using ht.tsum_eq.symm
  apply he.le.trans
  exact NumberMoments.tail_markov_of_series (fun n => NumberMoments.sector BT μ n x)
    (fun n => NumberMoments.sector_nonneg BT μ n hx) (NumberMoments.sector_hasSum BT μ hx) M _
    (NumberMoments.full_number_sectors BT μ hx) hfinite

end GptLean.PhysicalFock.ChannelMoments
