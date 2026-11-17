import PfHk.CarlemanSpatialDensity
import PfHk.CarlemanWeightDerivatives
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! On a fixed spatial annulus every Carleman multiplier is bounded and
preserves integrability. This supplies the spatial integrability needed
before applying the logarithmic change of measure. -/

noncomputable section
namespace PfHk.CarlemanSpatialDensity

open MeasureTheory Set PfHk.PolarCalculus PfHk.CarlemanWeights
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000

variable {I : Type*} [Fintype I] [DecidableEq I]

def annulus (ρ R : ℝ) : Set (Position I) := Metric.closedBall 0 R \ Metric.ball 0 ρ

theorem annulus_compact (ρ R : ℝ) : IsCompact (annulus (I := I) ρ R) :=
  (isCompact_closedBall 0 R).diff Metric.isOpen_ball

theorem annulus_norm {ρ R : ℝ} {X : Position I} (hX : X ∈ annulus ρ R) :
    ρ ≤ ‖X‖ ∧ ‖X‖ ≤ R := by
  simpa only [annulus, mem_diff, Metric.mem_closedBall, Metric.mem_ball,
    dist_zero_right, not_lt, and_comm] using hX

def massWeight (τ α : ℝ) (X : Position I) : ℝ :=
  Real.exp (2*τ*weight α (-Real.log ‖X‖)) * τ^3*beta α (-Real.log ‖X‖)*(‖X‖^2)⁻¹

def kineticWeight (τ α : ℝ) (X : Position I) : ℝ :=
  Real.exp (2*τ*weight α (-Real.log ‖X‖)) * τ*beta α (-Real.log ‖X‖)

def radiationWeight (τ α : ℝ) (X : Position I) : ℝ :=
  Real.exp (2*τ*weight α (-Real.log ‖X‖)) * (2*τ)

def sourceWeight (τ α : ℝ) (X : Position I) : ℝ :=
  Real.exp (2*τ*weight α (-Real.log ‖X‖)) * ‖X‖^2

theorem weights_continuousAt (τ α : ℝ) {X : Position I}
    (hpos : 0 < ‖X‖) (hsmall : ‖X‖ < 1) :
    ContinuousAt (massWeight τ α) X ∧ ContinuousAt (kineticWeight τ α) X ∧
      ContinuousAt (radiationWeight τ α) X ∧ ContinuousAt (sourceWeight τ α) X := by
  have ht : 0 < -Real.log ‖X‖ := neg_pos.mpr (Real.log_neg hpos hsmall)
  have hc : ContinuousAt (fun Y : Position I => -Real.log ‖Y‖) X :=
    (continuous_norm.continuousAt.log hpos.ne').neg
  have hf : ContinuousAt (fun Y : Position I => weight α (-Real.log ‖Y‖)) X :=
    (weight_hasDerivAt α ht).continuousAt.comp (f := fun Y : Position I => -Real.log ‖Y‖) hc
  have hb : ContinuousAt (fun Y : Position I => beta α (-Real.log ‖Y‖)) X :=
    (beta_hasDerivAt α ht).continuousAt.comp (f := fun Y : Position I => -Real.log ‖Y‖) hc
  have he : ContinuousAt (fun Y : Position I =>
      Real.exp (2*τ*weight α (-Real.log ‖Y‖))) X :=
    Real.continuous_exp.continuousAt.comp (f := fun Y : Position I =>
      2*τ*weight α (-Real.log ‖Y‖)) (continuousAt_const.mul hf)
  have hinv : ContinuousAt (fun Y : Position I => (‖Y‖^2)⁻¹) X :=
    (continuous_norm.continuousAt.pow 2).inv₀ (pow_ne_zero 2 hpos.ne')
  exact ⟨((he.mul continuousAt_const).mul hb).mul hinv,
    (he.mul continuousAt_const).mul hb, he.mul continuousAt_const,
    he.mul (continuous_norm.continuousAt.pow 2)⟩

theorem weights_continuousOn (τ α : ℝ) {ρ R : ℝ} (hρ : 0 < ρ) (hR : R < 1) :
    ContinuousOn (massWeight (I := I) τ α) (annulus ρ R) ∧
      ContinuousOn (kineticWeight (I := I) τ α) (annulus ρ R) ∧
      ContinuousOn (radiationWeight (I := I) τ α) (annulus ρ R) ∧
      ContinuousOn (sourceWeight (I := I) τ α) (annulus ρ R) := by
  have h (X : Position I) (hX : X ∈ annulus ρ R) :=
    weights_continuousAt τ α (hρ.trans_le (annulus_norm hX).1) ((annulus_norm hX).2.trans_lt hR)
  exact ⟨fun X hX => (h X hX).1.continuousWithinAt,
    fun X hX => (h X hX).2.1.continuousWithinAt,
    fun X hX => (h X hX).2.2.1.continuousWithinAt,
    fun X hX => (h X hX).2.2.2.continuousWithinAt⟩

theorem annular_mul_integrable (ρ R : ℝ) (w f : Position I → ℝ)
    (hw : ContinuousOn w (annulus ρ R)) (hf : Integrable f)
    (hs : ∀ᵐ X ∂volume, X ∉ annulus ρ R → f X = 0) :
    Integrable (fun X => w X*f X) := by
  have hA := annulus_compact (I := I) ρ R
  have hi : IntegrableOn (fun X => w X*f X) (annulus ρ R) :=
    IntegrableOn.continuousOn_mul hw hf.integrableOn hA
  apply ((integrable_indicator_iff hA.measurableSet).mpr hi).congr
  filter_upwards [hs] with X hX
  by_cases hmem : X ∈ annulus ρ R
  · rw [indicator_of_mem hmem]
  · rw [indicator_of_notMem hmem, hX hmem, mul_zero]

theorem density_integrable (τ α : ℝ) {ρ R : ℝ} (hρ : 0 < ρ) (hR : R < 1)
    (M D Q : Position I → ℝ) (hM : Integrable M) (hD : Integrable D) (hQ : Integrable Q)
    (hs : ∀ᵐ X ∂volume, X ∉ annulus ρ R → M X=0 ∧ D X=0 ∧ Q X=0) :
    Integrable (density τ α M D Q) := by
  obtain ⟨hw₀, hw₁, hw₂, _⟩ := weights_continuousOn (I := I) τ α hρ hR
  have h₀ := annular_mul_integrable ρ R _ M hw₀ hM (hs.mono fun _ h hx => (h hx).1)
  have h₁ := annular_mul_integrable ρ R _ D hw₁ hD (hs.mono fun _ h hx => (h hx).2.1)
  have h₂ := annular_mul_integrable ρ R _ Q hw₂ hQ (hs.mono fun _ h hx => (h hx).2.2)
  apply ((h₀.add h₁).add h₂).congr
  exact ae_of_all _ fun X => by
    simp only [Pi.add_apply]
    unfold density massWeight kineticWeight radiationWeight
    ring

theorem source_integrable (τ α : ℝ) {ρ R : ℝ} (hρ : 0 < ρ) (hR : R < 1)
    (S : Position I → ℝ) (hS : Integrable S)
    (hs : ∀ᵐ X ∂volume, X ∉ annulus ρ R → S X=0) :
    Integrable (source τ α S) :=
  annular_mul_integrable ρ R _ S (weights_continuousOn τ α hρ hR).2.2.2 hS hs

end PfHk.CarlemanSpatialDensity
