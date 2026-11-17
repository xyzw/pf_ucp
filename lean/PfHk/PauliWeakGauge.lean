import PfHk.PauliReference
import PfHk.PauliCurrentCovariance
import GptLean.TransformationsGaugeWeakReference

/-! Actual admissible weak gauges on the finite-spin common form domain.
The transformation acts on every orbital reference component and preserves
the joint spinor norm. Its Pauli contraction follows from the already
proved covariant derivative identity and the finite-spin algebra. -/

noncomputable section
namespace PfHk.PauliWeakGauge

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.TransformationsGauge GptLean.TransformationsPhase GptLean.SymmetricLift
  PauliSpin PauliCurrentAlgebra
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 25000

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

variable {N : ℕ}

local instance referenceAddCommGroup : AddCommGroup (Reference (Fin N × Fin 3) (fun _ => 0)) :=
  (referenceSubspace (Fin N × Fin 3) (fun _ => 0)).addCommGroup
local instance referenceModule : Module ℂ (Reference (Fin N × Fin 3) (fun _ => 0)) :=
  (referenceNormedSpace (Fin N × Fin 3) (fun _ => 0)).toModule
local instance referenceSMul : SMul ℂ (Reference (Fin N × Fin 3) (fun _ => 0)) :=
  (referenceModule (N := N)).toSMul

attribute [local irreducible] referenceSubspace

abbrev Ref := PauliReference.Ref N

def gauge (G : WeakSpatialGauge) (u : Ref (N := N)) : Ref (N := N) :=
  fun s => G.gaugeReference (fun _ => 0) (u s)

theorem inverse_left (G : WeakSpatialGauge) (u : Ref (N := N)) :
    gauge G.neg (gauge G u) = u := by
  funext s
  exact G.neg_gaugeReference (fun _ => 0) (u s)

theorem injective (G : WeakSpatialGauge) : Function.Injective (gauge G (N := N)) :=
  Function.LeftInverse.injective (inverse_left G)

theorem inverse_right (G : WeakSpatialGauge) (u : Ref (N := N)) :
    gauge G (gauge G.neg u) = u :=
  injective G.neg (inverse_left G (gauge G.neg u))

theorem surjective (G : WeakSpatialGauge) : Function.Surjective (gauge G (N := N)) :=
  fun u => ⟨gauge G.neg u, inverse_right G u⟩

theorem sigma_gauge (G : WeakSpatialGauge) (n : Fin N) (a : Fin 3) (u : Ref (N := N)) :
    sigmaFamily n a (gauge G u) = gauge G (sigmaFamily n a u) :=
  sigmaFamily_map (H := Reference (Fin N × Fin 3) (fun _ => 0))
    (K := Reference (Fin N × Fin 3) (fun _ => 0)) n a
    (G.gaugeReferenceLinear (fun _ => 0)) u

private theorem bundle_phase {S X H : Type*} [Fintype S] [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {μ : Measure X}
    {θ : X → ℝ} (hθ : AEStronglyMeasurable θ μ) (u : S → Lp H 2 μ) :
    FiniteFiberL2.bundle (fun s => phase hθ (u s)) = phase hθ (FiniteFiberL2.bundle u) := by
  apply Lp.ext
  filter_upwards [FiniteFiberL2.bundle_ae (fun s => phase hθ (u s)),
    phase_ae hθ (FiniteFiberL2.bundle u), FiniteFiberL2.bundle_ae u,
    ae_all_iff.mpr (fun s => phase_ae hθ (u s))] with x hb hp hu hs
  rw [hb, hp, hu]
  apply PiLp.ext
  intro s
  exact hs s

private theorem phase_norm_ae {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [NormedSpace ℂ H] {μ : Measure X}
    {θ : X → ℝ} (hθ : AEStronglyMeasurable θ μ) (u : Lp H 2 μ) :
    (fun x => ‖phase hθ u x‖) =ᵐ[μ] fun x => ‖u x‖ := by
  filter_upwards [phase_ae hθ u] with x hx
  rw [hx, norm_smul, norm_factor, one_mul]

abbrev spinPhase (G : WeakSpatialGauge) :
    PauliReference.Wave N ≃ₗᵢ[ℂ] PauliReference.Wave N :=
  phase (G.configurationAngle_measurable N)

theorem wave_gauge (G : WeakSpatialGauge) (u : Ref (N := N)) :
    PauliReference.wave (gauge G u) = spinPhase G (PauliReference.wave u) := by
  unfold PauliReference.wave gauge
  simp only [G.inclusion_gaugeReference]
  exact bundle_phase (G.configurationAngle_measurable N) _

theorem wave_norm_gauge (G : WeakSpatialGauge) (u : Ref (N := N)) :
    ‖PauliReference.wave (gauge G u)‖ = ‖PauliReference.wave u‖ :=
  (congrArg norm (wave_gauge (N := N) G u)).trans ((spinPhase (N := N) G).norm_map _)

theorem wave_norm_gauge_ae (G : WeakSpatialGauge) (u : Ref (N := N)) :
    (fun X => ‖PauliReference.wave (gauge G u) X‖) =ᵐ[volume]
      fun X => ‖PauliReference.wave u X‖ := by
  have he := congrArg (fun w : PauliReference.Wave N => fun X => ‖w X‖)
    (wave_gauge (N := N) G u)
  have hp : (fun X => ‖spinPhase (N := N) G (PauliReference.wave u) X‖) =ᵐ[volume]
      fun X => ‖PauliReference.wave u X‖ :=
    phase_norm_ae (H := Fiber N PhotonFock) (G.configurationAngle_measurable N)
      (PauliReference.wave u)
  have he' : (fun X => ‖PauliReference.wave (gauge G u) X‖) =ᵐ[volume]
      fun X => ‖spinPhase (N := N) G (PauliReference.wave u) X‖ :=
    Filter.Eventually.of_forall (fun X => congrFun he X)
  exact he'.trans hp

theorem radiation_gauge (G : WeakSpatialGauge) (u : Ref (N := N)) (s : SpinIndex N) :
    radiation (Fin N × Fin 3) (fun _ => 0) (gauge G u s) =
      G.wavePhase (radiation (Fin N × Fin 3) (fun _ => 0) (u s)) :=
  G.radiation_gaugeReference (fun _ => 0) (u s)

theorem radiation_norm_sq_gauge (G : WeakSpatialGauge) (u : Ref (N := N)) :
    (∑ s, ‖radiation (Fin N × Fin 3) (fun _ => 0) (gauge G u s)‖^2) =
      ∑ s, ‖radiation (Fin N × Fin 3) (fun _ => 0) (u s)‖^2 := by
  simp only [radiation_gauge, G.wavePhase.norm_map]

variable (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Configuration N → WeightedPhotonKernel)
  (hκ : ∀ q, AEStronglyMeasurable (κ q) volume)
  (M : ℝ) (hbound : ∀ q, ∀ᵐ X ∂volume, ‖(κ q X).val‖ ≤ M) (e : ℝ)

theorem contraction_gauge (G : WeakSpatialGauge) (n : Fin N) (u : Ref (N := N)) :
    contraction (H := WaveSpace (Fin N × Fin 3)) n (fun a s => covariant (Fin N × Fin 3) (fun _ => 0)
      C κ hκ M hbound e (n, a) (gauge G u s)) =
      fun s => G.wavePhase (contraction (H := WaveSpace (Fin N × Fin 3)) n (fun a t =>
        covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hbound e (n, a) (u t) +
          G.gradientSource (fun _ => 0) (n, a) (u t)) s) := by
  have hc : (fun a s => covariant (Fin N × Fin 3) (fun _ => 0)
      C κ hκ M hbound e (n, a) (gauge G u s)) =
      fun a s => G.wavePhase (covariant (Fin N × Fin 3) (fun _ => 0)
        C κ hκ M hbound e (n, a) (u s) + G.gradientSource (fun _ => 0) (n, a) (u s)) := by
    funext a s
    exact G.covariant_gaugeReference (fun _ => 0) C κ hκ M hbound e (n, a) (u s)
  exact (congrArg (contraction (H := WaveSpace (Fin N × Fin 3)) n) hc).trans
    (contraction_map (H := WaveSpace (Fin N × Fin 3))
      (K := WaveSpace (Fin N × Fin 3)) n G.wavePhase.toLinearMap _)

theorem covariant_gauge_ae (G : WeakSpatialGauge) (q : Fin N × Fin 3)
    (u : Ref (N := N)) (s : SpinIndex N) :
    ∀ᵐ X ∂volume, covariant (Fin N × Fin 3) (fun _ => 0)
      C κ hκ M hbound e q (gauge G u s) X =
      factor (G.configurationAngle N) X •
        (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hbound e q (u s) X +
          (G.gradient q.2 (particle X q.1) : ℂ) •
            inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X) := by
  have hc : covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hbound e q
      (gauge G u s) = G.wavePhase
        (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hbound e q (u s) +
          G.gradientSource (fun _ => 0) q (u s)) :=
    G.covariant_gaugeReference (fun _ => 0) C κ hκ M hbound e q (u s)
  filter_upwards [phase_ae (G.configurationAngle_measurable N)
      (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hbound e q (u s) +
        G.gradientSource (fun _ => 0) q (u s)),
    Lp.coeFn_add (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hbound e q (u s))
      (G.gradientSource (fun _ => 0) q (u s)),
    G.gradientSource_ae (fun _ => 0) q (u s)] with X hp ha hg
  have hv := congrArg (fun w : WaveSpace (Fin N × Fin 3) => w X) hc
  have hs := ha.trans (congrArg
    (fun y : PhotonFock => covariant (Fin N × Fin 3) (fun _ => 0)
      C κ hκ M hbound e q (u s) X + y)
    (hg.trans (Complex.coe_smul _ _).symm))
  exact hv.trans (hp.trans (congrArg
    (fun y : PhotonFock => factor (G.configurationAngle N) X • y) hs))

theorem current_gauge_ae (G : WeakSpatialGauge) (n : Fin N) (u : Ref (N := N)) (a : Fin 3) :
    ∀ᵐ X ∂volume,
      current (H := PhotonFock) n (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (gauge G u s) X)
        (fun b s => covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hbound e (n, b)
          (gauge G u s) X) a =
      current (H := PhotonFock) n (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X)
        (fun b s => covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hbound e (n, b)
          (u s) X) a + G.gradient a (particle X n) *
        density (H := PhotonFock) (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X) := by
  have hv (s : SpinIndex N) :
      (inclusion (Fin N × Fin 3) (fun _ => 0) (gauge G u s) : Configuration N → PhotonFock) =ᵐ[volume]
        fun X => factor (G.configurationAngle N) X •
          inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X := by
    have hi := G.inclusion_gaugeReference (fun _ => 0) (u s)
    filter_upwards [phase_ae (G.configurationAngle_measurable N)
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))] with X hX
    exact (congrArg (fun w : WaveSpace (Fin N × Fin 3) => w X) hi).trans hX
  filter_upwards [ae_all_iff.mpr hv,
    ae_all_iff.mpr (fun b : Fin 3 => ae_all_iff.mpr (fun s =>
      covariant_gauge_ae C κ hκ M hbound e G (n, b) u s))] with X hX hD
  have hVX := funext hX
  have hDX := funext (fun b => funext (hD b))
  have hj := congrArg₂ (fun (v : SpinIndex N → PhotonFock)
      (d : Fin 3 → SpinIndex N → PhotonFock) => current (H := PhotonFock) n v d a) hVX hDX
  exact hj.trans (current_isometry_shift (H := PhotonFock) (K := PhotonFock) n
    (scalarIsometry (H := PhotonFock) (factor (G.configurationAngle N) X)
      (norm_factor _ _)) _ _ _ a)

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

end PfHk.PauliWeakGauge
