import PfHk.CylinderIntegrationConditions
import PfHk.WeightedCylinderDensity
import Mathlib.Tactic.FunProp

/-! The cylinder integration conditions follow from ordinary continuity
and a common compact support interval inside the working half-cylinder. -/

noncomputable section
namespace PfHk.CylinderEstimate

open MeasureTheory Filter Set CylinderIdentity
open scoped InnerProductSpace Topology
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 250000

theorem integrableOn_compact_interval {f : ℝ → ℝ} {a b t₀ : ℝ}
    (hta : t₀ < a) (hc : ContinuousOn f (Ioi t₀))
    (hs : ∀ t, t ∉ Icc a b → f t = 0) : IntegrableOn f (Ioi t₀) := by
  have hi : IntegrableOn f (Icc a b) :=
    (hc.mono fun t ht => hta.trans_le ht.1).integrableOn_Icc
  have hf : Integrable f :=
    (integrableOn_iff_integrable_of_support_subset
      (show Function.support f ⊆ Icc a b from fun t ht => by
        by_contra h
        exact ht (hs t h))).mp hi
  exact hf.integrableOn

private theorem tendsto_zero_of_interval_support {f : ℝ → ℝ} {a b : ℝ}
    (hs : ∀ t, t ∉ Icc a b → f t = 0) : Tendsto f atTop (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop b] with t ht
  exact (hs t (fun h => (not_le_of_gt ht) h.2)).symm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem originalDensity_integrable (τ c t₀ a b : ℝ) (f β r : ℝ → ℝ)
    (w dw k q : ℝ → H) (hta : t₀ < a)
    (hf : ContinuousOn f (Ioi t₀)) (hb : ContinuousOn β (Ioi t₀))
    (hr : ContinuousOn r (Ioi t₀)) (hw : ContinuousOn w (Ioi t₀))
    (hdw : ContinuousOn dw (Ioi t₀))
    (hK : ContinuousOn (fun t => inner ℝ (w t) (k t)) (Ioi t₀))
    (hT : ContinuousOn (fun t => inner ℝ (w t) (q t)) (Ioi t₀))
    (hs : ∀ t, t ∉ Icc a b → w t = 0 ∧ dw t = 0) :
    IntegrableOn (fun t => Real.exp (2*τ*f t) *
      CylinderConjugation.originalDensity τ c β r w dw k q t) (Ioi t₀) := by
  apply integrableOn_compact_interval (b := b) hta
  · unfold CylinderConjugation.originalDensity
    fun_prop
  · intro t ht
    obtain ⟨hz, hdz⟩ := hs t ht
    simp [CylinderConjugation.originalDensity, hz, hdz]

theorem IntegrationConditions.of_compact (τ c t₀ a b : ℝ)
    (p β db ddb r kv qv : ℝ → ℝ) (z dz ddz k q : ℝ → H)
    (hta : t₀ < a)
    (hp : ContinuousOn p (Ioi t₀)) (hb : ContinuousOn β (Ioi t₀))
    (hdb : ContinuousOn db (Ioi t₀)) (hddb : ContinuousOn ddb (Ioi t₀))
    (hr : ContinuousOn r (Ioi t₀)) (hkv : ContinuousOn kv (Ioi t₀))
    (hqv : ContinuousOn qv (Ioi t₀))
    (hz : ContinuousOn z (Ioi t₀)) (hdz : ContinuousOn dz (Ioi t₀))
    (hddz : ContinuousOn ddz (Ioi t₀)) (hk : ContinuousOn k (Ioi t₀))
    (hq : ContinuousOn q (Ioi t₀))
    (hs : ∀ t, t ∉ Icc a b → z t = 0 ∧ dz t = 0 ∧ ddz t = 0 ∧
      k t = 0 ∧ q t = 0 ∧ kv t = 0 ∧ qv t = 0) :
    IntegrationConditions τ c t₀ p β db ddb r kv qv z dz ddz k q := by
  have hS : ContinuousOn (symmetricPart τ c p r z ddz k q) (Ioi t₀) := by
    unfold symmetricPart
    fun_prop
  have hB : ContinuousOn (skewPart τ p β z dz) (Ioi t₀) := by
    unfold skewPart
    fun_prop
  have hzeroS (t : ℝ) (ht : t ∉ Icc a b) : symmetricPart τ c p r z ddz k q t = 0 := by
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := hs t ht
    simp only [symmetricPart, h₁, h₃, h₄, h₅, smul_zero, neg_zero, add_zero, sub_zero]
  have hzeroB (t : ℝ) (ht : t ∉ Icc a b) : skewPart τ p β z dz t = 0 := by
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := hs t ht
    simp only [skewPart, h₁, h₂, smul_zero, add_zero]
  have hzeroFlux (t : ℝ) (ht : t ∉ Icc a b) : boundaryFlux τ c p β db r z dz k q t = 0 := by
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := hs t ht
    simp [boundaryFlux, h₁, h₂]
  have hzeroMult (t : ℝ) (ht : t ∉ Icc a b) : multiplierFlux β db z dz t = 0 := by
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := hs t ht
    simp [multiplierFlux, h₁, h₂]
  have ht₀ : t₀ ∉ Icc a b := fun h => (not_le_of_gt hta) h.1
  refine ⟨hzeroFlux t₀ ht₀, tendsto_zero_of_interval_support hzeroFlux,
    hzeroMult t₀ ht₀, tendsto_zero_of_interval_support hzeroMult,
    integrableOn_compact_interval (b := b) hta (hS.norm.pow 2) ?_,
    integrableOn_compact_interval (b := b) hta (hB.norm.pow 2) ?_,
    integrableOn_compact_interval (b := b) hta (continuousOn_const.mul (hS.inner hB)) ?_,
    integrableOn_compact_interval (b := b) hta ?_ ?_,
    integrableOn_compact_interval (b := b) hta ?_ ?_,
    integrableOn_compact_interval (b := b) hta (hS.inner (hb.smul hz)) ?_,
    integrableOn_compact_interval (b := b) hta ?_ ?_⟩
  · intro t ht
    rw [hzeroS t ht, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
  · intro t ht
    rw [hzeroB t ht, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
  · intro t ht
    simp only [hzeroS t ht, inner_zero_left, mul_zero]
  · unfold commutatorDensity
    fun_prop
  · intro t ht
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := hs t ht
    simp [commutatorDensity, h₁, h₂, h₆, h₇]
  · unfold multiplierDensity
    fun_prop
  · intro t ht
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := hs t ht
    simp [multiplierDensity, h₁, h₂]
  · intro t ht
    simp only [hzeroS t ht, inner_zero_left]
  · unfold retained
    exact (((((hS.norm.pow 2).div_const 2).add (hB.norm.pow 2)).add
      ((continuousOn_const.mul hb).mul (hdz.norm.pow 2))).add
      ((continuousOn_const.mul hb).mul (hz.norm.pow 2))).add
      (((continuousOn_const.mul hb).mul (hz.inner hk)).div_const 4) |>.add
      ((continuousOn_const.mul hr).mul (hz.inner hq))
  · intro t ht
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := hs t ht
    simp [retained, hzeroS t ht, hzeroB t ht, h₁, h₂]

end PfHk.CylinderEstimate
