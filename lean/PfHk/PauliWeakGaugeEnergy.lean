import PfHk.PauliWeakGaugeState
import PfHk.WeakGaugePotentials

/-! The actual Pauli form is unchanged by a weak spatial phase and the
simultaneous replacement of A by A minus the weak gradient. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliWeakGauge

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.SymmetricLift GptLean.TransformationsGauge GptLean.TransformationsPhase
  GptLean.PhysicalPairDuality GptLean.PhysicalPolarization
  PfHk.PauliGroundState PfHk.PauliCurrentAlgebra PfHk.PhysicalLocalEnergy
  PfHk.PhysicalCommonFormDomain PfHk.CenteredPhysicalReference

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 60000

variable {N : ℕ}
local instance gaugePhotonDirectInner : InnerProductSpace ℂ PhotonFock :=
  { (inferInstance : InnerProductSpace ℂ PhotonFock) with
    toNormedSpace := (inferInstance : NormedSpace ℂ PhotonFock) }
local instance gaugeWaveDirectInner : InnerProductSpace ℂ (WaveSpace (Fin N × Fin 3)) :=
  { (inferInstance : InnerProductSpace ℂ (WaveSpace (Fin N × Fin 3))) with
    toNormedSpace := (inferInstance : NormedSpace ℂ (WaveSpace (Fin N × Fin 3))) }
attribute [local irreducible] referenceSubspace inclusion radiation covariant
  roughMultiply externalCovariant rawCovariant rawContraction rawForm

private theorem real_complex_smul_comm {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℂ H] (r : ℝ) (z : ℂ) (w : H) : r • (z • w) = z • (r • w) :=
  smul_comm r z w

private theorem gradient_cancel {H : Type*} [AddCommGroup H] [Module ℝ H]
    (r a : ℝ) (w : H) : r • w + (a - r) • w = a • w := by
  rw [sub_smul]
  abel

theorem roughMultiply_gauge (G : WeakSpatialGauge)
    (f : Configuration N → ℝ) (u : Reference (Fin N × Fin 3) (fun _ => 0))
    (hu : HasMultiplier f (inclusion (Fin N × Fin 3) (fun _ => 0) u))
    (hg : HasMultiplier f (inclusion (Fin N × Fin 3) (fun _ => 0)
      (G.gaugeReference (fun _ => 0) u))) :
    roughMultiply f (inclusion (Fin N × Fin 3) (fun _ => 0)
      (G.gaugeReference (fun _ => 0) u)) hg =
      G.wavePhase (roughMultiply f (inclusion (Fin N × Fin 3) (fun _ => 0) u) hu) := by
  apply Lp.ext
  have hi := G.inclusion_gaugeReference (fun _ => 0) u
  filter_upwards [roughMultiply_ae f
      (inclusion (Fin N × Fin 3) (fun _ => 0) (G.gaugeReference (fun _ => 0) u)) hg,
    roughMultiply_ae f (inclusion (Fin N × Fin 3) (fun _ => 0) u) hu,
    phase_ae (E := PhotonFock) (G.configurationAngle_measurable N)
      (inclusion (Fin N × Fin 3) (fun _ => 0) u),
    phase_ae (E := PhotonFock) (G.configurationAngle_measurable N)
      (roughMultiply f (inclusion (Fin N × Fin 3) (fun _ => 0) u) hu)]
    with X h₁ h₂ h₃ h₄
  have hv := (congrArg (fun w : WaveSpace (Fin N × Fin 3) => w X) hi).trans h₃
  exact h₁.trans ((congrArg (fun y : PhotonFock => f X • y) hv).trans
    ((real_complex_smul_comm (H := PhotonFock) (f X) (factor (G.configurationAngle N) X)
      (inclusion (Fin N × Fin 3) (fun _ => 0) u X)).trans
      ((congrArg (fun y : PhotonFock => factor (G.configurationAngle N) X • y) h₂.symm).trans h₄.symm)))

theorem vector_gauge_ae (G : WeakSpatialGauge) (A : VectorPotential)
    (q : Fin N × Fin 3) :
    vector (N := N) (G.gaugeVector A) q =ᵐ[volume]
      fun X => vector A q X - G.gradient q.2 (particle X q.1) := by
  filter_upwards [ScalarCoordinateFormBound.coordinate_ae q.1 (G.coeFn_gaugeVector A)]
    with X hX
  have hx := congrArg (fun b : PhysicalPairSpace.Vector => b q.2) hX
  simpa only [vector, vectorCoefficient, FriedrichsDivergenceBackground.configurationVector,
    CoordinateSobolev.coordinateCoefficient, PhysicalSourcePair.split_fst_eq_particle,
    PiLp.sub_apply, G.gradientVector_apply] using hx

variable (C : CanonicalSectorCCR photonMeasure) (e : ℝ) (F : Frame) (χ : ArticleCutoff)
  (A : VectorPotential) (v : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)

set_option hygiene false in
local notation "κ" => profile (N := N) F χ 0
set_option hygiene false in
local notation "hκ" => profile_measurable (N := N) F χ 0
set_option hygiene false in
local notation "M" => profileBound F χ
set_option hygiene false in
local notation "hb" => profile_bound (N := N) F χ 0

theorem external_covariant_gauge (G : WeakSpatialGauge) (u : PauliGroundState.Ref N)
    (q : Fin N × Fin 3) (s : PauliSpin.SpinIndex N) :
    rawCovariant C κ hκ M hb e (vector (G.gaugeVector A)) (positive v c) (negative v c)
      (gauge G u) (physicalDomain (G.gaugeVector A) v c hc (gauge G u)) q s =
      G.wavePhase (rawCovariant C κ hκ M hb e (vector A) (positive v c) (negative v c)
        u (physicalDomain A v c hc u) q s) := by
  let w := inclusion (Fin N × Fin 3) (fun _ => 0) (u s)
  let d := covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hb e q (u s)
  let a := roughMultiply (vector A q) w ((physicalDomain A v c hc u s).vector q)
  let g := G.gradientSource (fun _ => 0) q (u s)
  let a' := roughMultiply (vector (G.gaugeVector A) q) w
    ((physicalDomain (G.gaugeVector A) v c hc u s).vector q)
  have hsum : g + a' = a := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_add g a', G.gradientSource_ae (fun _ => 0) q (u s),
      roughMultiply_ae (vector (G.gaugeVector A) q) w
        ((physicalDomain (G.gaugeVector A) v c hc u s).vector q),
      roughMultiply_ae (vector A q) w ((physicalDomain A v c hc u s).vector q),
      vector_gauge_ae G A q] with X hadd hg ha' ha hv
    exact hadd.trans ((congrArg₂ (fun x y : PhotonFock => x + y) hg
      (ha'.trans (congrArg (fun r : ℝ => r • w X) hv))).trans
        ((gradient_cancel (G.gradient q.2 (particle X q.1)) (vector A q X) (w X)).trans ha.symm))
  have hcvg := G.covariant_gaugeReference (fun _ => 0) C κ hκ M hb e q (u s)
  have hmul := roughMultiply_gauge G (vector (G.gaugeVector A) q) (u s)
    ((physicalDomain (G.gaugeVector A) v c hc u s).vector q)
    ((physicalDomain (G.gaugeVector A) v c hc (gauge G u) s).vector q)
  unfold rawCovariant externalCovariant
  exact (congrArg₂ (fun x y : WaveSpace (Fin N × Fin 3) => x + y) hcvg hmul).trans
    ((G.wavePhase.map_add (d + g) a').symm.trans
      (congrArg G.wavePhase ((add_assoc d g a').trans (congrArg (d + ·) hsum))))

theorem external_contraction_gauge (G : WeakSpatialGauge) (u : PauliGroundState.Ref N)
    (n : Fin N) :
    rawContraction C κ hκ M hb e (vector (G.gaugeVector A)) (positive v c) (negative v c)
      (gauge G u) (physicalDomain (G.gaugeVector A) v c hc (gauge G u)) n =
      fun s => G.wavePhase (rawContraction C κ hκ M hb e (vector A) (positive v c) (negative v c)
        u (physicalDomain A v c hc u) n s) := by
  unfold rawContraction
  have h := funext (fun a => funext (fun s => external_covariant_gauge C e F χ A v c hc G u (n,a) s))
  exact (congrArg (contraction (H := WaveSpace (Fin N × Fin 3)) n) h).trans
    (contraction_map (H := WaveSpace (Fin N × Fin 3))
      (K := WaveSpace (Fin N × Fin 3)) n G.wavePhase.toLinearMap _)

theorem form_gauge (G : WeakSpatialGauge) (z u : PauliGroundState.Ref N) :
    PauliGroundState.form C e F χ (G.gaugeVector A) v c hc (gauge G z) (gauge G u) =
      PauliGroundState.form C e F χ A v c hc z u := by
  have hkin : (∑ n, ∑ s, inner ℂ (E := WaveSpace (Fin N × Fin 3))
      (rawContraction C κ hκ M hb e (vector (G.gaugeVector A)) (positive v c) (negative v c)
        (gauge G z) (physicalDomain (G.gaugeVector A) v c hc (gauge G z)) n s)
      (rawContraction C κ hκ M hb e (vector (G.gaugeVector A)) (positive v c) (negative v c)
        (gauge G u) (physicalDomain (G.gaugeVector A) v c hc (gauge G u)) n s)) =
      ∑ n, ∑ s, inner ℂ (E := WaveSpace (Fin N × Fin 3))
        (rawContraction C κ hκ M hb e (vector A) (positive v c) (negative v c)
          z (physicalDomain A v c hc z) n s)
        (rawContraction C κ hκ M hb e (vector A) (positive v c) (negative v c)
          u (physicalDomain A v c hc u) n s) := by
    apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro s _
    exact (congrArg₂ (fun x y : WaveSpace (Fin N × Fin 3) => inner ℂ (E := WaveSpace (Fin N × Fin 3)) x y)
      (congrFun (external_contraction_gauge C e F χ A v c hc G z n) s)
      (congrFun (external_contraction_gauge C e F χ A v c hc G u n) s)).trans
        (G.wavePhase.inner_map_map _ _)
  have hrad : (∑ s, inner ℂ (E := WaveSpace (Fin N × Fin 3)) (radiation (Fin N × Fin 3) (fun _ => 0) (gauge G z s))
      (radiation (Fin N × Fin 3) (fun _ => 0) (gauge G u s))) =
      ∑ s, inner ℂ (E := WaveSpace (Fin N × Fin 3)) (radiation (Fin N × Fin 3) (fun _ => 0) (z s))
        (radiation (Fin N × Fin 3) (fun _ => 0) (u s)) := by
    simp only [radiation_gauge, G.wavePhase.inner_map_map]
  have hmul (f : Configuration N → ℝ)
      (hz : ∀ s, HasMultiplier f (inclusion (Fin N × Fin 3) (fun _ => 0) (z s)))
      (hu : ∀ s, HasMultiplier f (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)))
      (hgz : ∀ s, HasMultiplier f (inclusion (Fin N × Fin 3) (fun _ => 0) (gauge G z s)))
      (hgu : ∀ s, HasMultiplier f (inclusion (Fin N × Fin 3) (fun _ => 0) (gauge G u s))) :
      (∑ s, inner ℂ (E := WaveSpace (Fin N × Fin 3)) (roughMultiply f (inclusion (Fin N × Fin 3) (fun _ => 0) (gauge G z s)) (hgz s))
        (roughMultiply f (inclusion (Fin N × Fin 3) (fun _ => 0) (gauge G u s)) (hgu s))) =
      ∑ s, inner ℂ (E := WaveSpace (Fin N × Fin 3)) (roughMultiply f (inclusion (Fin N × Fin 3) (fun _ => 0) (z s)) (hz s))
        (roughMultiply f (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) (hu s)) := by
    apply Finset.sum_congr rfl
    intro s _
    exact (congrArg₂ (fun x y : WaveSpace (Fin N × Fin 3) => inner ℂ (E := WaveSpace (Fin N × Fin 3)) x y)
      (roughMultiply_gauge G f (z s) (hz s) (hgz s))
      (roughMultiply_gauge G f (u s) (hu s) (hgu s))).trans (G.wavePhase.inner_map_map _ _)
  have hp := hmul (positive v c)
    (fun s => (physicalDomain A v c hc z s).positive)
    (fun s => (physicalDomain A v c hc u s).positive)
    (fun s => (physicalDomain (G.gaugeVector A) v c hc (gauge G z) s).positive)
    (fun s => (physicalDomain (G.gaugeVector A) v c hc (gauge G u) s).positive)
  have hn := hmul (negative v c)
    (fun s => (physicalDomain A v c hc z s).negative)
    (fun s => (physicalDomain A v c hc u s).negative)
    (fun s => (physicalDomain (G.gaugeVector A) v c hc (gauge G z) s).negative)
    (fun s => (physicalDomain (G.gaugeVector A) v c hc (gauge G u) s).negative)
  unfold PauliGroundState.form rawForm
  exact congrArg₂ (fun x y : ℂ => x - y)
    (congrArg₂ (fun x y : ℂ => x + y)
      (congrArg₂ (fun x y : ℂ => x + y) (congrArg (fun x : ℂ => (1/2 : ℂ) * x) hkin) hrad) hp) hn

theorem energy_gauge (G : WeakSpatialGauge) (u : PauliGroundState.Ref N) :
    PauliGroundState.energy C e F χ (G.gaugeVector A) v c hc (gauge G u) =
      PauliGroundState.energy C e F χ A v c hc u :=
  congrArg Complex.re (form_gauge C e F χ A v c hc G u u)

theorem energy_gaugeState (G : WeakSpatialGauge) (p : State N) :
    PauliGroundState.energy C e F χ (G.gaugeVector A) v c hc (gaugeState G p).vector =
      PauliGroundState.energy C e F χ A v c hc p.vector :=
  energy_gauge C e F χ A v c hc G p.vector

theorem groundState_gauge (G : WeakSpatialGauge) (p : State N)
    (hp : IsGroundState C e F χ A v c hc p) :
    IsGroundState C e F χ (G.gaugeVector A) v c hc (gaugeState G p) := by
  intro q
  obtain ⟨r, rfl⟩ := gaugeState_surjective G q
  exact (energy_gaugeState C e F χ A v c hc G p).trans_le
    ((hp r).trans_eq (energy_gaugeState C e F χ A v c hc G r).symm)

theorem groundState_gauge_iff (G : WeakSpatialGauge) (p : State N) :
    IsGroundState C e F χ (G.gaugeVector A) v c hc (gaugeState G p) ↔
      IsGroundState C e F χ A v c hc p := by
  constructor
  · intro hp q
    exact (energy_gaugeState C e F χ A v c hc G p).symm.trans_le
      ((hp (gaugeState G q)).trans_eq (energy_gaugeState C e F χ A v c hc G q))
  · exact groundState_gauge C e F χ A v c hc G p

end PfHk.PauliWeakGauge

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
