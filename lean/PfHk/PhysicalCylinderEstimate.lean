import PfHk.CylinderIntegrationConditions
import PfHk.CenteredPhysicalCylinderBounds
import PfHk.SphereCoreForms

/-! The cylinder commutator estimate for the genuine centered angular
and radiation forms. All form derivatives and their absorption bounds
are proved. Ordinary endpoint and integrability conditions are explicit. -/

noncomputable section

namespace PfHk.PhysicalCylinderEstimate
private theorem angular_transport {K T M K₀ T₀ M₀ v b r τ : ℝ}
    (hK : K = K₀) (hT : T = T₀) (hM : M = M₀)
    (h : |v| ≤ b/16*K + r/16*T + τ^2*b/16*M) :
    |v| ≤ b/16*K₀ + r/16*T₀ + τ^2*b/16*M₀ := by
  simpa only [hK, hT, hM] using h

private theorem radiation_transport {T M T₀ M₀ v b r τ : ℝ}
    (hT : T = T₀) (hM : M = M₀)
    (h : r*|v| ≤ r/8*T + τ^2*b/16*M) :
    r*|v| ≤ r/8*T₀ + τ^2*b/16*M₀ := by
  simpa only [hT, hM] using h
end PfHk.PhysicalCylinderEstimate

namespace PfHk.PhysicalCylinderEstimate

open MeasureTheory Filter Set GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.SymmetricLift GptLean.Representability PfHk.PhysicalFieldRegularity
  PfHk.PolarCalculus PfHk.SphereCoreGeometry PfHk.CylinderIdentity
  PfHk.CylinderEstimate PfHk.CarlemanWeights
open PfHk.SphereAngularField (SpherePhoton)
open scoped ENNReal Topology InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 500000

local instance : InnerProductSpace ℝ PhotonFock := InnerProductSpace.rclikeToReal ℂ _
attribute [local irreducible] CenteredSphereAngularField.energy CenteredSphereAngularField.formDerivative
  CenteredSphereRadiationEnergy.energy CenteredSphereRadiationEnergy.formDerivative

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (C : CanonicalSectorCCR photonMeasure) (W : ConcreteWeylLaw photonMeasure)

def angularDerivative (O : Configuration N) (u : CoreCurve N) (t : ℝ) : ℝ :=
  CenteredSphereAngularField.formDerivative F χ hUV e O C
    (u.value t).gradient (u.value t).radiation t

def radiationDerivative (O : Configuration N) (u : CoreCurve N) (t : ℝ) : ℝ :=
  CenteredSphereRadiationEnergy.formDerivative F χ hUV e O (u.value t).radiation t

include W

/-- One threshold gives coercivity for every center and every genuine
sphere core curve with represented angular and radiation operators. -/
theorem exists_uniform_coercivity (α : ℝ) (hα : 0 < α) :
    ∃ t₀ : ℝ, 2 ≤ t₀ ∧ ∀ (τ c : ℝ), 9 ≤ τ →
      ∀ (O : Configuration N) (u : CoreCurve N) (k q : ℝ → SpherePhoton N),
      (∀ t, IsAngularRepresentative F χ hUV e O C t (u.value t) (k t)) →
      (∀ t, IsRadiationRepresentative F χ hUV e O t (u.value t) (q t)) →
      IntegrationConditions τ c t₀ (weightPrime α) (beta α) (betaPrime α) (betaSecond α)
        (fun t => Real.exp (-2*t)) (angularDerivative F χ hUV e C O u)
        (radiationDerivative F χ hUV e O u) u.ambient u.firstAmbient u.second k q →
      (∫ t in Ioi t₀, retained τ c (weightPrime α) (beta α) (fun t => Real.exp (-2*t))
        u.ambient u.firstAmbient u.second k q t) ≤
      ∫ t in Ioi t₀, ‖symmetricPart τ c (weightPrime α) (fun t => Real.exp (-2*t))
        u.ambient u.second k q t + skewPart τ (weightPrime α) (beta α)
        u.ambient u.firstAmbient t‖ ^ 2 := by
  obtain ⟨t₁, ht₁, herrors⟩ := CenteredPhysicalCylinderBounds.exists_uniform_cylinder
    (N := N) F χ hUV e C W α hα
  -- The half-cylinder also starts above the exponent threshold `4 α`, where the
  -- explicit bounds on `f'` and on the fourth derivative of the weight hold.
  have ht₁₀ : t₁ ≤ max t₁ (4 * α) := le_max_left _ _
  have hα₀ : 4 * α ≤ max t₁ (4 * α) := le_max_right _ _
  have ht₀ : 2 ≤ max t₁ (4 * α) := ht₁.trans ht₁₀
  refine ⟨max t₁ (4 * α), ht₀, ?_⟩
  intro τ c hτ O u k q hk hq hi
  have hr (t : ℝ) : HasDerivAt (fun s => Real.exp (-2*s)) (-2 * Real.exp (-2*t)) t := by
    simpa only [id_eq, mul_one, one_mul, mul_comm] using ((hasDerivAt_id t).const_mul (-2)).exp
  have hpos (t : ℝ) (ht : t ∈ Ici (max t₁ (4 * α))) : 0 < t :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (ht₀.trans ht)
  apply cylinder_coercivity τ c (max t₁ (4 * α)) (by linarith)
    (fun t ht => weightPrime_hasDerivAt α (hpos t ht))
    (fun t ht => beta_hasDerivAt α (hpos t ht))
    (fun t ht => betaPrime_hasDerivAt α (hpos t ht))
    (fun t _ => hr t) (fun t _ => u.ambient_hasDerivAt t)
    (fun t _ => u.first_hasDerivAt t)
    (fun t _ => angular_product_rule F χ hUV e O C u k hk t)
    (fun t _ => radiation_product_rule F χ hUV e O u q hq t)
    hi.boundary_zero hi.boundary_infty hi.multiplier_zero hi.multiplier_infty
    hi.symmetric_integrable hi.skew_integrable hi.cross_integrable hi.commutator_integrable
    hi.multiplier_integrable hi.pairing_integrable hi.retained_integrable
  · intro t ht
    have ht₂ : 2 ≤ t := ht₀.trans ht.le
    have hkdiag := (hk t).diagonal F χ hUV e O C
    have hqdiag := (hq t).diagonal F χ hUV e O
    have hm : CenteredPhysicalCylinderBounds.mass (u.value t).radiation = ‖u.ambient t‖ ^ 2 :=
      CenteredPhysicalCylinderBounds.mass_eq_norm_sq (u.value t).radiation
    have htα : 4 * α ≤ t := hα₀.trans ht.le
    have ht₁' : t₁ ≤ t := ht₁₀.trans ht.le
    have hp := weightPrime_bounds hα ht₂ htα
    obtain ⟨ha, hr⟩ := herrors τ t hτ ht₁' O (u.value t).gradient (u.value t).radiation
    have hK := CenteredSphereAngularField.energy_nonneg F χ hUV e O C
      (u.value t).gradient (u.value t).radiation t
    have hT := CenteredSphereRadiationEnergy.energy_nonneg F χ hUV e O (u.value t).radiation t
    exact ⟨(beta_pos hα (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) ht₂)).le, beta_le_one hα ht₂,
      hp.1, hp.2, (Real.exp_pos _).le, hK.trans_eq hkdiag.symm, hT.trans_eq hqdiag.symm,
      fourth_derivative_small hα hτ ht₂ htα,
      angular_transport hkdiag.symm hqdiag.symm hm ha,
      radiation_transport hqdiag.symm hm hr⟩

omit W

/-- An opaque proposition packages the established cylinder estimate. -/
def CoerciveAt (α t₀ : ℝ) : Prop :=
    ∀ (τ c : ℝ), 9 ≤ τ →
      ∀ (O : Configuration N) (u : CoreCurve N) (k q : ℝ → SpherePhoton N),
      (∀ t, IsAngularRepresentative F χ hUV e O C t (u.value t) (k t)) →
      (∀ t, IsRadiationRepresentative F χ hUV e O t (u.value t) (q t)) →
      IntegrationConditions τ c t₀ (weightPrime α) (beta α) (betaPrime α) (betaSecond α)
        (fun t => Real.exp (-2*t)) (angularDerivative F χ hUV e C O u)
        (radiationDerivative F χ hUV e O u) u.ambient u.firstAmbient u.second k q →
      (∫ t in Ioi t₀, retained τ c (weightPrime α) (beta α) (fun t => Real.exp (-2*t))
        u.ambient u.firstAmbient u.second k q t) ≤
      ∫ t in Ioi t₀, ‖symmetricPart τ c (weightPrime α) (fun t => Real.exp (-2*t))
        u.ambient u.second k q t + skewPart τ (weightPrime α) (beta α)
        u.ambient u.firstAmbient t‖ ^ 2

include W

theorem exists_uniform_coercivity_packed (α : ℝ) (hα : 0 < α) :
    ∃ t₀ : ℝ, 2 ≤ t₀ ∧ CoerciveAt (N := N) F χ hUV e C α t₀ := by
  exact exists_uniform_coercivity (N := N) F χ hUV e C W α hα

end PfHk.PhysicalCylinderEstimate
