import PfHk.ScalarCutoffGeometry
import PfHk.PhysicalCarlemanInput

/-! The ordinary cutoff support and convergence specialized to actual
PF reference vectors through their checked inclusion identity. -/

noncomputable section
namespace PfHk.PhysicalCarlemanInput

open MeasureTheory Filter GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open PfHk.PhysicalCutoffCommutator PfHk.SmoothCutoffBounds
open scoped ENNReal Topology

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 20000
set_option Elab.async false

attribute [local irreducible] PhysicalPFReference.inclusion PhysicalPFScalarMultiplier.multiply
  GptLean.ElectronicH1Multiplier.DifferentiableMultiplier.multiplier

variable {I : Type} [Fintype I] [DecidableEq I]

theorem buffered_annular_support (V : Position I → ℝ) (u : Reference I V)
    {x₀ : Position I} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (hεR : ε ≤ R / 4)
    (a b : TwiceDifferentiableMultiplier I)
    (ha : a.scalar.weight = scaled (bufferedBump I) x₀ (R / 2))
    (hb : b.scalar.weight = scaled (bufferedBump I) x₀ ε) :
    AnnularSupport
      (inclusion I V (PhysicalPFScalarMultiplier.multiply V (twiceSub a b).scalar u)) x₀ R := by
  have h : AnnularSupport ((twiceSub a b).scalar.multiplier (H := PhotonFock) (inclusion I V u)) x₀ R :=
    scalar_buffered_annular_support (inclusion I V u) hR hε hεR a b ha hb
  exact (congrArg (fun z : WaveSpace I => AnnularSupport z x₀ R)
    (PhysicalPFScalarMultiplier.value_multiply V (twiceSub a b).scalar u)).mpr h

theorem buffered_cutoff_eventually_identity [Nonempty I]
    (V : Position I → ℝ) (u : Reference I V)
    {x₀ : Position I} {R inner : ℝ} (hR : 0 < R) (hi : inner ≤ R / 2)
    (a : TwiceDifferentiableMultiplier I) (b : ℕ → TwiceDifferentiableMultiplier I)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεlim : Tendsto ε atTop (𝓝 0))
    (ha : a.scalar.weight = scaled (bufferedBump I) x₀ (R / 2))
    (hb : ∀ n, (b n).scalar.weight = scaled (bufferedBump I) x₀ (ε n)) :
    ∀ᵐ x ∂volume.restrict (Metric.ball x₀ inner), ∀ᶠ n in atTop,
      inclusion I V (PhysicalPFScalarMultiplier.multiply V (twiceSub a (b n)).scalar u) x =
        inclusion I V u x := by
  filter_upwards [scalar_buffered_cutoff_eventually_identity (inclusion I V u)
    hR hi a b ε hε hεlim ha hb] with x hx
  filter_upwards [hx] with n hn
  exact (congrArg (fun z : WaveSpace I => z x)
    (PhysicalPFScalarMultiplier.value_multiply V (twiceSub a (b n)).scalar u)).trans hn

end PfHk.PhysicalCarlemanInput
