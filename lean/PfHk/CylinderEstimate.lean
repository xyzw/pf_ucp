import PfHk.CylinderCarleman

/-!
The cylinder estimate for actual integrals over the half line. This theorem
uses coefficient derivative bounds and the product rules of the moving
forms. Both integration identities are proved from those product rules.
The physical realization of the angular and radiation curves is separate.
-/

noncomputable section
namespace PfHk.CylinderEstimate
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open MeasureTheory Filter Set
open scoped InnerProductSpace Topology
open CylinderIdentity CylinderCarleman

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

private theorem integral_add_apply {μ : Measure ℝ} {f g : ℝ → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    (∫ t, f t + g t ∂μ) = (∫ t, f t ∂μ) + ∫ t, g t ∂μ := by
  exact integral_add hf hg

private theorem integral_sub_apply {μ : Measure ℝ} {f g : ℝ → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    (∫ t, f t - g t ∂μ) = (∫ t, f t ∂μ) - ∫ t, g t ∂μ := by
  exact integral_sub hf hg

/-- The retained coercive density includes the full symmetric norm, so it
also controls subsequent graph estimates. -/
def retained (τ c : ℝ) (p b r : ℝ → ℝ) (z dz ddz k q : ℝ → H) (t : ℝ) : ℝ :=
  ‖symmetricPart τ c p r z ddz k q t‖ ^ 2 / 2 +
    ‖skewPart τ p b z dz t‖ ^ 2 + τ * b t * ‖dz t‖ ^ 2 +
    τ ^ 3 * b t * ‖z t‖ ^ 2 + τ * b t * inner ℝ (z t) (k t) / 4 +
    τ * r t * inner ℝ (z t) (q t)

/-- Coercivity on the half cylinder. No commutator or multiplier identity
is assumed in the conclusion's premises. The derivative and endpoint
conditions imply both identities by the fundamental theorem of calculus. -/
theorem cylinder_coercivity (τ c t₀ : ℝ)
    {p b db ddb r kv qv : ℝ → ℝ} {z dz ddz k q : ℝ → H}
    (hτ : 1 ≤ τ)
    (hp : ∀ t ∈ Ici t₀, HasDerivAt p (b t) t)
    (hb : ∀ t ∈ Ici t₀, HasDerivAt b (db t) t)
    (hdb : ∀ t ∈ Ici t₀, HasDerivAt db (ddb t) t)
    (hr : ∀ t ∈ Ici t₀, HasDerivAt r (-2 * r t) t)
    (hz : ∀ t ∈ Ici t₀, HasDerivAt z (dz t) t)
    (hdz : ∀ t ∈ Ici t₀, HasDerivAt dz (ddz t) t)
    (hk : ∀ t ∈ Ici t₀, HasDerivAt (fun s => inner ℝ (z s) (k s))
      (2 * inner ℝ (dz t) (k t) + kv t) t)
    (hq : ∀ t ∈ Ici t₀, HasDerivAt (fun s => inner ℝ (z s) (q s))
      (2 * inner ℝ (dz t) (q t) + qv t) t)
    (hzero : boundaryFlux τ c p b db r z dz k q t₀ = 0)
    (hinfty : Tendsto (boundaryFlux τ c p b db r z dz k q) atTop (𝓝 0))
    (hmzero : multiplierFlux b db z dz t₀ = 0)
    (hminfty : Tendsto (multiplierFlux b db z dz) atTop (𝓝 0))
    (hS : IntegrableOn (fun t => ‖symmetricPart τ c p r z ddz k q t‖ ^ 2) (Ioi t₀))
    (hB : IntegrableOn (fun t => ‖skewPart τ p b z dz t‖ ^ 2) (Ioi t₀))
    (hcross : IntegrableOn (fun t => 2 * inner ℝ
      (symmetricPart τ c p r z ddz k q t) (skewPart τ p b z dz t)) (Ioi t₀))
    (hmain : IntegrableOn (commutatorDensity τ p b ddb r kv qv z dz q) (Ioi t₀))
    (hmult : IntegrableOn (multiplierDensity τ c p b ddb r z dz k q) (Ioi t₀))
    (hpair : IntegrableOn (fun t =>
      inner ℝ (symmetricPart τ c p r z ddz k q t) (b t • z t)) (Ioi t₀))
    (hret : IntegrableOn (retained τ c p b r z dz ddz k q) (Ioi t₀))
    (hbounds : ∀ t ∈ Ioi t₀, 0 ≤ b t ∧ b t ≤ 1 ∧ 3 / 4 ≤ p t ∧ p t ≤ 1 ∧
      0 ≤ r t ∧ 0 ≤ inner ℝ (z t) (k t) ∧ 0 ≤ inner ℝ (z t) (q t) ∧
      |ddb t| ≤ τ ^ 2 * b t / 8 ∧
      |kv t| ≤ b t / 16 * inner ℝ (z t) (k t) +
        r t / 16 * inner ℝ (z t) (q t) + τ ^ 2 * b t / 16 * ‖z t‖ ^ 2 ∧
      r t * |qv t| ≤ r t / 8 * inner ℝ (z t) (q t) +
        τ ^ 2 * b t / 16 * ‖z t‖ ^ 2) :
    (∫ t in Ioi t₀, retained τ c p b r z dz ddz k q t) ≤
      ∫ t in Ioi t₀, ‖symmetricPart τ c p r z ddz k q t +
        skewPart τ p b z dz t‖ ^ 2 := by
  have hcomm := integrated_commutator_Ioi τ c t₀ hp hb hdb hr hz hdz hk hq
    hzero hinfty hcross hmain
  have hmul := integrated_multiplier_Ioi τ c t₀ hb hdb hz hdz
    hmzero hminfty hmult hpair
  have hmono := integral_mono_ae hret (((hS.add hB).add hmain).add
    ((hmult.sub hpair).const_mul (τ / 2))) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      obtain ⟨hb₀, hb₁, hp₀, hp₁, hr₀, hK, hT, hf, hkv, hqv⟩ := hbounds t ht
      exact pointwise_coercivity τ c hτ hb₀ hb₁ hp₀ hp₁ hr₀ hK hT hf hkv hqv)
  have hnorm : (∫ t in Ioi t₀,
      ‖symmetricPart τ c p r z ddz k q t + skewPart τ p b z dz t‖ ^ 2) =
      (∫ t in Ioi t₀, ‖symmetricPart τ c p r z ddz k q t‖ ^ 2) +
      (∫ t in Ioi t₀, ‖skewPart τ p b z dz t‖ ^ 2) +
      ∫ t in Ioi t₀, commutatorDensity τ p b ddb r kv qv z dz q t := by
    calc
      _ = ∫ t in Ioi t₀,
          (‖symmetricPart τ c p r z ddz k q t‖ ^ 2 + ‖skewPart τ p b z dz t‖ ^ 2) +
          2 * inner ℝ (symmetricPart τ c p r z ddz k q t) (skewPart τ p b z dz t) := by
        apply integral_congr_ae
        filter_upwards with t
        nlinarith [norm_add_sq_real (symmetricPart τ c p r z ddz k q t) (skewPart τ p b z dz t)]
      _ = _ := by
        have h₁ := integral_add_apply (hS.add hB) hcross
        have h₂ := integral_add_apply hS hB
        simp only [Pi.add_apply] at h₁ h₂
        rw [h₁, h₂, hcomm]
  have h₁ := integral_add_apply ((hS.add hB).add hmain) ((hmult.sub hpair).const_mul (τ / 2))
  have h₂ := integral_add_apply (hS.add hB) hmain
  have h₃ := integral_add_apply hS hB
  have h₄ := integral_sub_apply hmult hpair
  simp only [Pi.add_apply, Pi.sub_apply] at hmono h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, integral_const_mul, h₄, ← hmul, sub_self,
    mul_zero, add_zero, ← hnorm] at hmono
  exact hmono

end PfHk.CylinderEstimate
