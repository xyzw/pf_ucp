import GptLean.PhysicalSectorMeasures

/-!
The exact head/tail split of photon configuration coordinates. The head
is the one-photon position and the tail is the n-photon configuration.
The Hilbert product map has no Jacobian or normalization factor.
-/

noncomputable section

namespace GptLean.PhysicalSectorHeadCoordinates

open MeasureTheory PhysicalSectorMeasures Gaussian

/-- Reindex the head photon separately from the remaining photons. -/
def headIndex (n : ℕ) : (Fin 3 ⊕ (Fin n × Fin 3)) ≃ (Fin (n + 1) × Fin 3) where
  toFun s := match s with
    | Sum.inl a => (0, a)
    | Sum.inr p => (p.1.succ, p.2)
  invFun p := Fin.cases (.inl p.2) (fun j => .inr (j, p.2)) p.1
  left_inv := by
    intro s
    cases s with
    | inl a => rfl
    | inr p => rfl
  right_inv := by
    rintro ⟨i, a⟩
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

def split (n : ℕ) : Configuration (n + 1) ≃ₗᵢ[ℝ]
    WithLp 2 (FieldSpace × Configuration n) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (headIndex n).symm).trans
    (PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℝ) 2
      (fun _ : Fin 3 ⊕ (Fin n × Fin 3) => ℝ))

@[simp] theorem split_fst (n : ℕ) (x : Configuration (n + 1)) (a : Fin 3) :
    (split n x).fst a = x (0, a) := rfl

@[simp] theorem split_snd (n : ℕ) (x : Configuration (n + 1)) (p : Fin n × Fin 3) :
    (split n x).snd p = x (p.1.succ, p.2) := rfl

theorem split_measurePreserving (n : ℕ) :
    MeasurePreserving (fun x => WithLp.ofLp (split n x)) volume
      ((volume : Measure FieldSpace).prod (volume : Measure (Configuration n))) :=
  (WithLp.volume_preserving_ofLp FieldSpace (Configuration n)).comp (split n).measurePreserving

end GptLean.PhysicalSectorHeadCoordinates
