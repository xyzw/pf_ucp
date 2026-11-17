import PfHk.PauliWeylState
import GptLean.PhysicalMeanFields

/-! The actual external covariant coordinates and scalar form multipliers
under a photon displacement. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliWeylEnergy

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalWeyl GptLean.PhysicalPolarization GptLean.PhysicalPairDuality
  GptLean.SymmetricLift GptLean.Representability PfHk.PauliSpin PfHk.PauliGroundState
  PfHk.PhysicalLocalEnergy PfHk.PhysicalCommonFormDomain PfHk.CenteredPhysicalReference

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 70000

variable {N : ℕ}
local instance coordinateReferenceAddCommGroup :
    AddCommGroup (Reference (Fin N × Fin 3) (fun _ => 0)) :=
  PauliGroundState.referenceAddCommGroup (N := N)
local instance coordinateReferenceModule : Module ℂ (Reference (Fin N × Fin 3) (fun _ => 0)) :=
  PauliGroundState.referenceModule (N := N)
local instance coordinateReferenceSMul : SMul ℂ (Reference (Fin N × Fin 3) (fun _ => 0)) :=
  PauliGroundState.referenceSMul (N := N)
attribute [local irreducible] referenceSubspace inclusion roughMultiply covariant

variable (W : ConcreteWeylLaw photonMeasure) {f : Lp ℂ 2 photonMeasure}
  (K : WeightedPhotonKernel)
  (hK : ∀ᵐ p ∂photonMeasure, K.val.2 p = (Real.sqrt ‖p.1‖ : ℂ) * f p)

theorem value_displaced_ae (u : PauliGroundState.Ref N) (s : SpinIndex N) :
    (fun X => inclusion (Fin N × Fin 3) (fun _ => 0) (PauliWeyl.displaced W K hK u s) X) =ᵐ[volume]
      fun X => W.weyl f (inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X) :=
  inclusion_weylRef_ae (fun _ => 0) W K hK (u s)

attribute [local irreducible] PauliWeyl.displaced

theorem rough_norm_displaced (g : Configuration N → ℝ) (u : PauliGroundState.Ref N)
    (s : SpinIndex N)
    (hu : HasMultiplier g (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)))
    (hw : HasMultiplier g (inclusion (Fin N × Fin 3) (fun _ => 0)
      (PauliWeyl.displaced W K hK u s))) :
    ‖roughMultiply g (inclusion (Fin N × Fin 3) (fun _ => 0)
      (PauliWeyl.displaced W K hK u s)) hw‖ =
      ‖roughMultiply g (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) hu‖ := by
  apply norm_eq_of_ae
  filter_upwards [roughMultiply_ae g _ hw, roughMultiply_ae g _ hu,
    value_displaced_ae W K hK u s] with X h₁ h₂ h₃
  exact (congrArg (fun z : PhotonFock => ‖z‖) h₁).trans
    ((norm_smul (g X) _).trans
      ((congrArg (fun r : ℝ => ‖g X‖ * r)
        ((congrArg (fun z : PhotonFock => ‖z‖) h₃).trans ((W.weyl f).norm_map _))).trans
        ((norm_smul (g X) _).symm.trans (congrArg (fun z : PhotonFock => ‖z‖) h₂.symm))))

private theorem external_weyl_algebra {H : Type*} [AddCommGroup H] [Module ℂ H]
    (L : H →ₗ[ℂ] H) (d u : H) (a b : ℂ) :
    L (d - b • u) + a • L u = L (d + a • u + (-b) • u) := by
  simp only [map_add, map_sub, map_smul, neg_smul, map_neg]
  abel

variable (F : Frame) (χ : ArticleCutoff) (C : CanonicalSectorCCR photonMeasure)
  (e : ℝ) (A : VectorPotential) (v : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)

set_option hygiene false in
local notation "κ" => profile (N := N) F χ 0
set_option hygiene false in
local notation "hκ" => profile_measurable (N := N) F χ 0
set_option hygiene false in
local notation "M" => profileBound F χ
set_option hygiene false in
local notation "hb" => profile_bound (N := N) F χ 0
set_option hygiene false in
local notation "D" => physicalDomain (N := N) A v c hc

def derivatives (u : PauliGroundState.Ref N) :
    (Fin N × Fin 3) → SpinIndex N → WaveSpace (Fin N × Fin 3) :=
  rawCovariant C κ hκ M hb e (vector A) (positive v c) (negative v c) u (D u)

theorem orbital_displaced_ae (u : PauliGroundState.Ref N) (q : Fin N × Fin 3)
    (s : SpinIndex N) :
    (fun X => covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hb e q
      (PauliWeyl.displaced W K hK u s) X) =ᵐ[volume]
      fun X => W.weyl f (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hb e q (u s) X -
        ((e * classicalField κ f q X : ℝ) : ℂ) • inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X) := by
  unfold PauliWeyl.displaced
  exact covariant_weylRef_ae (fun _ => 0) W K hK C κ hκ M hb e q (u s)

theorem derivatives_ae (u : PauliGroundState.Ref N) (q : Fin N × Fin 3) (s : SpinIndex N) :
    (fun X => derivatives F χ C e A v c hc u q s X) =ᵐ[volume]
      fun X => covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hb e q (u s) X +
        ((vector A q X : ℝ) : ℂ) • inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X := by
  filter_upwards [Lp.coeFn_add
    (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hb e q (u s))
    (roughMultiply (vector A q) (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))
      (((D u) s).vector q)),
    roughMultiply_ae (vector A q) (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))
      (((D u) s).vector q)] with X h₁ h₂
  exact h₁.trans (congrArg (fun y : PhotonFock =>
    covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hb e q (u s) X + y)
      (h₂.trans (Complex.coe_smul (vector A q X) _).symm))

attribute [local irreducible] derivatives

theorem derivatives_displaced_ae (u : PauliGroundState.Ref N)
    (q : Fin N × Fin 3) (s : SpinIndex N) :
    (fun X => derivatives F χ C e A v c hc (PauliWeyl.displaced W K hK u) q s X) =ᵐ[volume]
      fun X => W.weyl f (derivatives F χ C e A v c hc u q s X +
        ((-(e * classicalField κ f q X) : ℝ) : ℂ) •
          inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X) := by
  filter_upwards [derivatives_ae F χ C e A v c hc (PauliWeyl.displaced W K hK u) q s,
    derivatives_ae F χ C e A v c hc u q s,
    orbital_displaced_ae W K hK F χ C e u q s,
    value_displaced_ae W K hK u s] with X h₁ h₂ h₃ h₄
  have ha := external_weyl_algebra (W.weyl f).toLinearEquiv.toLinearMap
    (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hb e q (u s) X)
    (inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X)
    (vector A q X : ℂ) ((e * classicalField κ f q X : ℝ) : ℂ)
  have heq := h₁.trans ((congrArg₂ (fun z y : PhotonFock => z + (vector A q X : ℂ) • y)
    h₃ h₄).trans ha)
  have ht := congrArg (fun z : PhotonFock => W.weyl f
    (z + (-((e * classicalField κ f q X : ℝ) : ℂ)) •
      inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X)) h₂.symm
  simpa only [Complex.ofReal_neg] using heq.trans ht

end PfHk.PauliWeylEnergy

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
