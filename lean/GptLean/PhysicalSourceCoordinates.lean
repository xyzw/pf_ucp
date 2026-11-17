import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The actual measure-preserving split of one particle from configuration space. -/

noncomputable section

namespace GptLean.PhysicalSourceCoordinates

open MeasureTheory

variable {N : ℕ}

abbrev Configuration (N : ℕ) := EuclideanSpace ℝ (Fin N × Fin 3)
abbrev Position := EuclideanSpace ℝ (Fin 3)
abbrev Remaining (i : Fin N) := {j : Fin N // j ≠ i} × Fin 3
abbrev Spectator (i : Fin N) := EuclideanSpace ℝ (Remaining i)

/-- Reindex the selected particle's three coordinates separately from all others. -/
def coordinateEquiv (i : Fin N) : (Fin 3 ⊕ Remaining i) ≃ (Fin N × Fin 3) where
  toFun s := match s with
    | Sum.inl a => (i, a)
    | Sum.inr p => (p.1.val, p.2)
  invFun p := if h : p.1 = i then Sum.inl p.2 else Sum.inr (⟨p.1, h⟩, p.2)
  left_inv := by
    intro s
    cases s with
    | inl a => simp
    | inr p => simp [p.1.property]
  right_inv := by
    intro p
    by_cases h : p.1 = i
    · simp only [dite_eq_left h]
      exact Prod.ext h.symm rfl
    · simp [h]

@[simp] theorem coordinateEquiv_inl (i : Fin N) (a : Fin 3) :
    coordinateEquiv i (.inl a) = (i, a) := rfl

@[simp] theorem coordinateEquiv_symm_selected (i : Fin N) (a : Fin 3) :
    (coordinateEquiv i).symm (i, a) = .inl a := by
  simp [coordinateEquiv]

def reindex (i : Fin N) :
    Configuration N ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3 ⊕ Remaining i) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (coordinateEquiv i).symm

/-- The first factor is exactly the chosen particle position. -/
def split (i : Fin N) : Configuration N ≃L[ℝ] Position × Spectator i :=
  (reindex i).toContinuousLinearEquiv.trans EuclideanSpace.sumEquivProd

@[simp] theorem split_fst_apply (i : Fin N) (x : Configuration N) (a : Fin 3) :
    (split i x).1 a = x (i, a) := rfl

@[simp] theorem split_snd_apply (i : Fin N) (x : Configuration N) (j : Remaining i) :
    (split i x).2 j = x (j.1.val, j.2) := rfl

/-- The selected coordinate directions have no spectator component. -/
theorem split_single_selected (i : Fin N) (a : Fin 3) :
    split i (EuclideanSpace.single (i, a) 1) = (EuclideanSpace.single a 1, 0) := by
  apply Prod.ext
  · ext b
    simp only [split_fst_apply, PiLp.single_apply]
    simp
  · ext j
    simp only [split_snd_apply, PiLp.single_apply, PiLp.zero_apply]
    simp [j.1.property]

/-- No Jacobian factor is introduced by separating the particle coordinates. -/
theorem split_measurePreserving (i : Fin N) :
    MeasurePreserving (split i) volume
      ((volume : Measure Position).prod (volume : Measure (Spectator i))) := by
  let S := PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℝ) 2
    (fun _ : Fin 3 ⊕ Remaining i => ℝ)
  change MeasurePreserving (fun x => WithLp.ofLp (S (reindex i x))) volume volume
  exact (WithLp.volume_preserving_ofLp Position (Spectator i)).comp
    (S.measurePreserving.comp (reindex i).measurePreserving)

theorem split_symm_measurePreserving (i : Fin N) :
    MeasurePreserving (split i).symm
      ((volume : Measure Position).prod (volume : Measure (Spectator i))) volume := by
  exact (show MeasurePreserving (split i).toHomeomorph.toMeasurableEquiv volume
    ((volume : Measure Position).prod (volume : Measure (Spectator i))) from
      split_measurePreserving i).symm

end GptLean.PhysicalSourceCoordinates
