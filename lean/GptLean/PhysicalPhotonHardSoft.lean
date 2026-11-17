import GptLean.PhysicalFockSupportedSubspaces
import GptLean.PhysicalPhotonNormalMoments
import GptLean.PhotonLocalizationLocalFormsOperators

/-!
The actual orthogonal hard/soft one-photon decomposition.

The two projections are multiplication by complementary measurable
indicators. Their ranges are closed subspaces, and addition is the
inverse of the resulting Hilbert direct-sum isometry. No momentum
factorization or range equality is assumed.
-/

noncomputable section

namespace GptLean.PhysicalFock.MomentumSplit

open MeasureTheory PhotonLocalization PhotonLocalizationFockChannel
open scoped ENNReal InnerProductSpace

set_option Elab.async false

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  (s : Set Ω) (hs : MeasurableSet s)

def weight : Ω → ℝ := s.indicator (fun _ => 1)

include hs in
theorem weight_measurable : Measurable (weight s) :=
  measurable_const.indicator hs

omit [MeasurableSpace Ω] in
theorem weight_bound (x : Ω) : |weight s x| ≤ 1 := by
  classical
  by_cases hx : x ∈ s <;> simp [weight, hx]

/-- Orthogonal momentum restriction on the original one-photon L2 space. -/
def projection : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  realL2Multiplier (weight s) (weight_measurable s hs).aestronglyMeasurable
    1 (ae_of_all μ (weight_bound s))

theorem projection_selfadjoint : IsSelfAdjoint (projection μ s hs) :=
  realL2Multiplier_selfadjoint _ _ _ _

theorem projection_adjoint : (projection μ s hs).adjoint = projection μ s hs :=
  (projection_selfadjoint μ s hs).adjoint_eq

theorem projection_ae (u : Lp ℂ 2 μ) :
    projection μ s hs u =ᵐ[μ] s.indicator u := by
  unfold projection
  filter_upwards [realL2Multiplier_apply (weight s)
    (weight_measurable s hs).aestronglyMeasurable 1
    (ae_of_all μ (weight_bound s)) u] with x hx
  rw [hx]
  classical
  by_cases hx : x ∈ s <;> simp [weight, hx]

theorem projection_add_compl (u : Lp ℂ 2 μ) :
    projection μ s hs u + projection μ sᶜ hs.compl u = u := by
  apply Lp.ext
  filter_upwards [projection_ae μ s hs u, projection_ae μ sᶜ hs.compl u,
    Lp.coeFn_add (projection μ s hs u) (projection μ sᶜ hs.compl u)]
    with x h₁ h₂ ha
  rw [ha, Pi.add_apply, h₁, h₂]
  classical
  by_cases hx : x ∈ s <;> simp [hx]

theorem projection_compl (u : Lp ℂ 2 μ) :
    projection μ s hs (projection μ sᶜ hs.compl u) = 0 := by
  apply Lp.ext
  filter_upwards [projection_ae μ s hs (projection μ sᶜ hs.compl u),
    projection_ae μ sᶜ hs.compl u, Lp.coeFn_zero ℂ 2 μ] with x h₁ h₂ hz
  rw [h₁, hz]
  classical
  by_cases hx : x ∈ s <;> simp [hx, h₂]

theorem projection_idempotent (u : Lp ℂ 2 μ) :
    projection μ s hs (projection μ s hs u) = projection μ s hs u := by
  apply Lp.ext
  filter_upwards [projection_ae μ s hs (projection μ s hs u),
    projection_ae μ s hs u] with x h₁ h₂
  rw [h₁]
  classical
  by_cases hx : x ∈ s <;> simp [hx, h₂]

theorem projection_inner_compl (u v : Lp ℂ 2 μ) :
    ⟪projection μ s hs u, projection μ sᶜ hs.compl v⟫_ℂ = 0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [projection_ae μ s hs u, projection_ae μ sᶜ hs.compl v]
    with x h₁ h₂
  rw [h₁, h₂]
  classical
  by_cases hx : x ∈ s <;> simp [hx]

theorem projection_norm_partition (u : Lp ℂ 2 μ) :
    ‖projection μ s hs u‖ ^ 2 + ‖projection μ sᶜ hs.compl u‖ ^ 2 = ‖u‖ ^ 2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
    (projection_inner_compl μ s hs u u)
  rw [projection_add_compl] at h
  simpa only [pow_two] using h.symm

/-- The closed one-photon subspace supported in `s`. -/
def supported : Submodule ℂ (Lp ℂ 2 μ) := (projection μ sᶜ hs.compl).ker

theorem mem_supported_iff (u : Lp ℂ 2 μ) :
    u ∈ supported μ s hs ↔ ∀ᵐ x ∂μ, x ∉ s → u x = 0 := by
  constructor
  · intro hu
    have hz : projection μ sᶜ hs.compl u = 0 := hu
    have ha := projection_ae μ sᶜ hs.compl u
    rw [hz] at ha
    filter_upwards [ha, Lp.coeFn_zero ℂ 2 μ] with x hx hzero
    intro hxs
    simpa only [Set.indicator_of_mem (show x ∈ sᶜ from hxs), Pi.zero_apply]
      using hx.symm.trans hzero
  · intro hu
    change projection μ sᶜ hs.compl u = 0
    apply Lp.ext
    filter_upwards [projection_ae μ sᶜ hs.compl u, hu, Lp.coeFn_zero ℂ 2 μ]
      with x hx hu hz
    rw [hx, hz]
    classical
    by_cases hxs : x ∈ s <;> simp [hxs, hu]

theorem supported_closed : IsClosed (supported μ s hs : Set (Lp ℂ 2 μ)) :=
  (projection μ sᶜ hs.compl).isClosed_ker

instance supported_complete : CompleteSpace (supported μ s hs) :=
  (supported_closed μ s hs).completeSpace_coe

theorem projection_mem_supported (u : Lp ℂ 2 μ) :
    projection μ s hs u ∈ supported μ s hs := by
  change projection μ sᶜ hs.compl (projection μ s hs u) = 0
  simpa only [compl_compl] using projection_compl μ sᶜ hs.compl u

theorem projection_of_supported (u : supported μ s hs) :
    projection μ s hs u.val = u.val := by
  have hu : projection μ sᶜ hs.compl u.val = 0 := u.property
  simpa only [hu, add_zero] using projection_add_compl μ s hs u.val

/-- The one-photon isometry fed to the already matched exponential law. -/
def split : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ) where
  toLinearMap := (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap.comp
    ((projection μ s hs).toLinearMap.prod (projection μ sᶜ hs.compl).toLinearMap)
  norm_map' u := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2]
    exact projection_norm_partition μ s hs u

theorem retained_split (u : Lp ℂ 2 μ) :
    retainedMap (split μ s hs) u = projection μ s hs u := rfl

theorem discarded_split (u : Lp ℂ 2 μ) :
    discardedMap μ (split μ s hs) u = projection μ sᶜ hs.compl u := rfl

theorem split_supported (u : supported μ s hs) :
    split μ s hs u.val = WithLp.toLp 2 (u.val, 0) := by
  change WithLp.toLp 2 (projection μ s hs u.val,
    projection μ sᶜ hs.compl u.val) = _
  rw [projection_of_supported, show projection μ sᶜ hs.compl u.val = 0 from u.property]

theorem split_compl_supported (u : supported μ sᶜ hs.compl) :
    split μ s hs u.val = WithLp.toLp 2 (0, u.val) := by
  have hu : projection μ s hs u.val = 0 := by
    have h : projection μ sᶜᶜ hs.compl.compl u.val = 0 := u.property
    simpa only [compl_compl] using h
  change WithLp.toLp 2 (projection μ s hs u.val,
    projection μ sᶜ hs.compl u.val) = _
  rw [hu, projection_of_supported]

def projectionInto : Lp ℂ 2 μ →L[ℂ] supported μ s hs :=
  (projection μ s hs).codRestrict (supported μ s hs) (projection_mem_supported μ s hs)

/-- The same split has range exactly the product of the two support spaces. -/
def splitInto : Lp ℂ 2 μ →ₗᵢ[ℂ]
    WithLp 2 (supported μ s hs × supported μ sᶜ hs.compl) where
  toLinearMap := (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap.comp
    ((projectionInto μ s hs).toLinearMap.prod (projectionInto μ sᶜ hs.compl).toLinearMap)
  norm_map' u := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2]
    exact projection_norm_partition μ s hs u

theorem splitInto_surjective : Function.Surjective (splitInto μ s hs) := by
  intro x
  let p := WithLp.ofLp x
  refine ⟨p.1.val + p.2.val, ?_⟩
  apply (WithLp.ext_iff 2).mpr
  apply Prod.ext
  · apply Subtype.ext
    change projection μ s hs (p.1.val + p.2.val) = p.1.val
    have hz : projection μ s hs p.2.val = 0 := by
      have h : projection μ sᶜᶜ hs.compl.compl p.2.val = 0 := p.2.property
      simpa only [compl_compl] using h
    rw [map_add, projection_of_supported, hz, add_zero]
  · apply Subtype.ext
    change projection μ sᶜ hs.compl (p.1.val + p.2.val) = p.2.val
    have hz : projection μ sᶜ hs.compl p.1.val = 0 := p.1.property
    rw [map_add, hz, projection_of_supported, zero_add]

def equivalence : Lp ℂ 2 μ ≃ₗᵢ[ℂ]
    WithLp 2 (supported μ s hs × supported μ sᶜ hs.compl) :=
  LinearIsometryEquiv.ofSurjective (splitInto μ s hs) (splitInto_surjective μ s hs)

end GptLean.PhysicalFock.MomentumSplit

namespace GptLean.PhysicalFock

open MeasureTheory
open scoped ENNReal

def softMomentumSet (κ : ℝ) : Set PhotonMode := {p | NormalPhoton.frequency p < κ}

theorem softMomentumSet_measurable (κ : ℝ) : MeasurableSet (softMomentumSet κ) :=
  measurableSet_lt NormalPhoton.frequency_measurable measurable_const

def softOnePhoton (κ : ℝ) : Submodule ℂ (Lp ℂ 2 photonMeasure) :=
  MomentumSplit.supported photonMeasure (softMomentumSet κ) (softMomentumSet_measurable κ)

def hardOnePhoton (κ : ℝ) : Submodule ℂ (Lp ℂ 2 photonMeasure) :=
  MomentumSplit.supported photonMeasure (softMomentumSet κ)ᶜ
    (softMomentumSet_measurable κ).compl

def hardSoftSplit (κ : ℝ) : Lp ℂ 2 photonMeasure →ₗᵢ[ℂ]
    WithLp 2 (Lp ℂ 2 photonMeasure × Lp ℂ 2 photonMeasure) :=
  MomentumSplit.split photonMeasure (softMomentumSet κ) (softMomentumSet_measurable κ)

end GptLean.PhysicalFock
