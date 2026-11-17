import GptLean.TransformationsPotentials

set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false

/-!
Orthogonal changes of variables on the article pair space `X × Y` and on the
potentials `(L∞ + L^{3/2}) × (L∞ + L³)`, and invariance of the Lieb
functional under them.

Let `R` be a linear isometry of `ℝ³`, so `R⁻¹ = Rᵀ`. It acts on pairs by
`(ρ, j) ↦ (ρ ∘ R⁻¹, R ∘ j ∘ R⁻¹)` and on potentials by
`(v, A) ↦ (v ∘ R⁻¹, R ∘ A ∘ R⁻¹)`. Both actions are one construction,
`f ↦ L ∘ f ∘ R⁻¹`, where `L` is the identity on scalars and `R` on vectors.
The pairing is unchanged by the joint action because `R⁻¹` preserves
Lebesgue measure and `⟨R a, R b⟩ = ⟨a, b⟩`. Then
`TransformationsPotentials.lieb_invariance` transfers invariance of the
constrained search to the Lieb functional.

The invariance of the constrained search itself is a hypothesis here.
-/

noncomputable section

namespace GptLean.TransformationsPotentials

open MeasureTheory PhysicalPairSpace PhysicalPairDuality
open scoped ENNReal

set_option maxHeartbeats 400000

/-! ### Orthogonal change of variables -/

section Rotation

variable (R : Position ≃ₗᵢ[ℝ] Position)

/-- The inverse of a linear isometry of `ℝ³` preserves Lebesgue measure. -/
theorem measurePreserving_rotate : MeasurePreserving R.symm volume volume :=
  R.symm.measurePreserving

theorem ae_comp_rotate {β : Type*} {f f' : Position → β} (h : f =ᵐ[volume] f') :
    (fun x => f (R.symm x)) =ᵐ[volume] fun x => f' (R.symm x) :=
  (measurePreserving_rotate R).quasiMeasurePreserving.ae_eq_comp h

/-- Change of variables `x ↦ R⁻¹ x` in a Lebesgue integral. -/
theorem integral_comp_rotate {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (g : Position → G) : ∫ x, g (R.symm x) = ∫ x, g x :=
  MeasurePreserving.integral_comp' (f := R.symm.toMeasurableEquiv)
    (measurePreserving_rotate R) g

section Values

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : F ≃ₗᵢ[ℝ] F)

/-- `f ↦ L ∘ f ∘ R⁻¹` preserves membership in `Lr`. -/
theorem memLp_rotate {r : ℝ≥0∞} {f : Position → F} (hf : MemLp f r volume) :
    MemLp (fun x => L (f (R.symm x))) r volume :=
  L.lipschitz.comp_memLp (map_zero L) (hf.comp_measurePreserving (measurePreserving_rotate R))

/-- The change of variables `f ↦ L ∘ f ∘ R⁻¹` of one `Lp` class. -/
def rotateLp {r : ℝ≥0∞} (f : Lp F r (volume : Measure Position)) :
    Lp F r (volume : Measure Position) :=
  (memLp_rotate R L (Lp.memLp f)).toLp fun x => L (f (R.symm x))

theorem coeFn_rotateLp {r : ℝ≥0∞} (f : Lp F r (volume : Measure Position)) :
    (rotateLp R L f : Position → F) =ᵐ[volume] fun x => L (f (R.symm x)) :=
  MemLp.coeFn_toLp _

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- The change of variables `f ↦ L ∘ f ∘ R⁻¹` of a compatible pair of `Lp`
classes. -/
def rotateIntersection (u : LpIntersection F p q (volume : Measure Position)) :
    LpIntersection F p q (volume : Measure Position) :=
  ofMemLp (fun x => L (PhysicalPairSpace.fst u (R.symm x)))
    (memLp_rotate R L (Lp.memLp (PhysicalPairSpace.fst u)))
    ((memLp_rotate R L (Lp.memLp (PhysicalPairSpace.snd u))).ae_eq (by
      filter_upwards [ae_comp_rotate R (PhysicalPairSpace.compatible u)] with x h
      exact congrArg L h.symm))

theorem fst_rotateIntersection (u : LpIntersection F p q (volume : Measure Position)) :
    (PhysicalPairSpace.fst (rotateIntersection R L u) : Position → F) =ᵐ[volume]
      fun x => L (PhysicalPairSpace.fst u (R.symm x)) :=
  fst_ofMemLp_ae _ _ _

/-- Two changes of variables that undo each other pointwise cancel. -/
theorem rotateIntersection_cancel (R' : Position ≃ₗᵢ[ℝ] Position) (L' : F ≃ₗᵢ[ℝ] F)
    (hR : ∀ x, R.symm (R'.symm x) = x) (hL : ∀ y, L' (L y) = y)
    (u : LpIntersection F p q (volume : Measure Position)) :
    rotateIntersection R' L' (rotateIntersection R L u) = u := by
  apply PhysicalPairSpace.ext_ae
  filter_upwards [fst_rotateIntersection R' L' (rotateIntersection R L u),
    ae_comp_rotate R' (fst_rotateIntersection R L u)] with x h₁ h₂
  rw [h₁, h₂, hL, hR]

end Values

section Sum

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] (L : F ≃ₗᵢ[ℝ] F)
  {q : ℝ≥0∞}

/-- The change of variables `u ↦ L ∘ u ∘ R⁻¹` of an `L∞ + Lq` class, acting on
both parts of its chosen decomposition. -/
def rotateSum (u : LpSum F q (volume : Measure Position)) :
    LpSum F q (volume : Measure Position) :=
  ofParts (rotateLp R L (parts u).1) (rotateLp R L (parts u).2)

theorem coeFn_rotateSum (u : LpSum F q (volume : Measure Position)) :
    ((rotateSum R L u).val : Position → F) =ᵐ[volume] fun x => L (u.val (R.symm x)) := by
  have h : ((rotateSum R L u).val : Position → F) =ᵐ[volume]
      fun x => rotateLp R L (parts u).1 x + rotateLp R L (parts u).2 x :=
    coeFn_ofParts _ _
  filter_upwards [h, coeFn_rotateLp R L (parts u).1, coeFn_rotateLp R L (parts u).2,
    ae_comp_rotate R (coeFn_parts u)] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄]
  exact (map_add L _ _).symm

/-- Two changes of variables that undo each other pointwise cancel. -/
theorem rotateSum_cancel (R' : Position ≃ₗᵢ[ℝ] Position) (L' : F ≃ₗᵢ[ℝ] F)
    (hR : ∀ x, R.symm (R'.symm x) = x) (hL : ∀ y, L' (L y) = y)
    (u : LpSum F q (volume : Measure Position)) :
    rotateSum R' L' (rotateSum R L u) = u := by
  apply sum_ext_ae
  filter_upwards [coeFn_rotateSum R' L' (rotateSum R L u),
    ae_comp_rotate R' (coeFn_rotateSum R L u)] with x h₁ h₂
  rw [h₁, h₂, hL, hR]

/-- Changing variables in the potential and the paired function together
leaves the pairing unchanged. -/
theorem pairing_rotate {p : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate q p] (u : LpSum F q (volume : Measure Position))
    (f : LpIntersection F 1 p (volume : Measure Position)) :
    pairing (rotateSum R L u) (rotateIntersection R L f) = pairing u f := by
  rw [pairing_eq_integral, pairing_eq_integral]
  refine (integral_congr_ae ?_).trans
    (integral_comp_rotate R fun x => inner ℝ (u.val x) (PhysicalPairSpace.fst f x))
  filter_upwards [coeFn_rotateSum R L u, fst_rotateIntersection R L f] with x h₁ h₂
  rw [h₁, h₂]
  exact L.inner_map_map _ _

end Sum

/-- Orthogonal change of variables of pairs,
`(ρ, j) ↦ (ρ ∘ R⁻¹, R ∘ j ∘ R⁻¹)`. -/
def rotatePair : Pair ≃ Pair where
  toFun d := (rotateIntersection R (LinearIsometryEquiv.refl ℝ ℝ) d.1,
    rotateIntersection R R d.2)
  invFun d := (rotateIntersection R.symm (LinearIsometryEquiv.refl ℝ ℝ) d.1,
    rotateIntersection R.symm R.symm d.2)
  left_inv d := Prod.ext
    (rotateIntersection_cancel R (LinearIsometryEquiv.refl ℝ ℝ) R.symm
      (LinearIsometryEquiv.refl ℝ ℝ) R.symm.apply_symm_apply (fun _ => rfl) d.1)
    (rotateIntersection_cancel R R R.symm R.symm R.symm.apply_symm_apply R.symm_apply_apply d.2)
  right_inv d := Prod.ext
    (rotateIntersection_cancel R.symm (LinearIsometryEquiv.refl ℝ ℝ) R
      (LinearIsometryEquiv.refl ℝ ℝ) R.symm.symm_apply_apply (fun _ => rfl) d.1)
    (rotateIntersection_cancel R.symm R.symm R R R.symm.symm_apply_apply R.apply_symm_apply d.2)

theorem rotatePair_apply (d : Pair) :
    rotatePair R d = (rotateIntersection R (LinearIsometryEquiv.refl ℝ ℝ) d.1,
      rotateIntersection R R d.2) := rfl

theorem densityL1_rotatePair (d : Pair) :
    (densityL1 (rotatePair R d) : Position → ℝ) =ᵐ[volume]
      fun x => densityL1 d (R.symm x) :=
  fst_rotateIntersection R (LinearIsometryEquiv.refl ℝ ℝ) d.1

theorem currentL1_rotatePair (d : Pair) :
    (currentL1 (rotatePair R d) : Position → Vector) =ᵐ[volume]
      fun x => R (currentL1 d (R.symm x)) :=
  fst_rotateIntersection R R d.2

/-- Orthogonal change of variables of potentials,
`(v, A) ↦ (v ∘ R⁻¹, R ∘ A ∘ R⁻¹)`. -/
def rotatePotential : Potential ≃ Potential where
  toFun u := (rotateSum R (LinearIsometryEquiv.refl ℝ ℝ) u.1, rotateSum R R u.2)
  invFun u := (rotateSum R.symm (LinearIsometryEquiv.refl ℝ ℝ) u.1,
    rotateSum R.symm R.symm u.2)
  left_inv u := Prod.ext
    (rotateSum_cancel R (LinearIsometryEquiv.refl ℝ ℝ) R.symm
      (LinearIsometryEquiv.refl ℝ ℝ) R.symm.apply_symm_apply (fun _ => rfl) u.1)
    (rotateSum_cancel R R R.symm R.symm R.symm.apply_symm_apply R.symm_apply_apply u.2)
  right_inv u := Prod.ext
    (rotateSum_cancel R.symm (LinearIsometryEquiv.refl ℝ ℝ) R
      (LinearIsometryEquiv.refl ℝ ℝ) R.symm.symm_apply_apply (fun _ => rfl) u.1)
    (rotateSum_cancel R.symm R.symm R R R.symm.symm_apply_apply R.apply_symm_apply u.2)

theorem rotatePotential_apply (u : Potential) :
    rotatePotential R u = (rotateSum R (LinearIsometryEquiv.refl ℝ ℝ) u.1,
      rotateSum R R u.2) := rfl

theorem coeFn_rotatePotential_fst (u : Potential) :
    ((rotatePotential R u).1.val : Position → ℝ) =ᵐ[volume]
      fun x => u.1.val (R.symm x) :=
  coeFn_rotateSum R (LinearIsometryEquiv.refl ℝ ℝ) u.1

theorem coeFn_rotatePotential_snd (u : Potential) :
    ((rotatePotential R u).2.val : Position → Vector) =ᵐ[volume]
      fun x => R (u.2.val (R.symm x)) :=
  coeFn_rotateSum R R u.2

/-- Change of variables: the pairing is invariant under the joint
orthogonal change of variables of potentials and pairs. -/
theorem pairPotential_rotate (u : Potential) (d : Pair) :
    pairPotential (rotatePotential R u) (rotatePair R d) = pairPotential u d := by
  change pairing (rotateSum R (LinearIsometryEquiv.refl ℝ ℝ) u.1)
        (rotateIntersection R (LinearIsometryEquiv.refl ℝ ℝ) d.1) +
      pairing (rotateSum R R u.2) (rotateIntersection R R d.2) =
    pairing u.1 d.1 + pairing u.2 d.2
  rw [pairing_rotate, pairing_rotate]

end Rotation

/-- Invariance under an orthogonal change of variables passes from the
constrained search to the Lieb functional. -/
theorem lieb_rotate {S : Type*} (A : DFT.StateModel S Pair) (R : Position ≃ₗᵢ[ℝ] Position)
    (hsym : ∀ d, DFT.search A (rotatePair R d) = DFT.search A d) (d : Pair) :
    DFT.lieb A (fun u p => pairPotential u p) (rotatePair R d) =
      DFT.lieb A (fun u p => pairPotential u p) d :=
  lieb_invariance A (rotatePair R) (rotatePotential R).symm
    (fun u e => by
      rw [← pairPotential_rotate R ((rotatePotential R).symm u) e,
        Equiv.apply_symm_apply])
    hsym d

end GptLean.TransformationsPotentials
