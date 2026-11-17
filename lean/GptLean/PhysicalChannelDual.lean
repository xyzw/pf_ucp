import GptLean.PhysicalNormalTrace
import Mathlib.Analysis.Normed.Lp.lpHolder

/-!
The bounded Heisenberg action of an actual Hilbert-sum dilation. Its
normal trace pairing is proved from the Kraus series and Parseval.
This helper is independent of any photon cutoff or Hamiltonian.
-/

noncomputable section
namespace GptLean.PhysicalChannelDual

open PhotonLocalizationChannel
open scoped InnerProductSpace

variable {H T : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]

def diagonal (A : H →L[ℂ] H) :
    lp (fun _ : ℕ => H) 2 →L[ℂ] lp (fun _ : ℕ => H) 2 :=
  lp.mapCLM 2 (fun _ => A) (norm_nonneg A) (fun _ => le_rfl)

omit [CompleteSpace H] in
@[simp] theorem diagonal_apply (A : H →L[ℂ] H)
    (v : lp (fun _ : ℕ => H) 2) (n : ℕ) : diagonal A v n = A (v n) := rfl

def pullback (U : KrausIsometry H) (A : H →L[ℂ] H) : H →L[ℂ] H :=
  U.toContinuousLinearMap.adjoint.comp ((diagonal A).comp U.toContinuousLinearMap)

theorem pullback_inner (U : KrausIsometry H) (A : H →L[ℂ] H) (u v : H) :
    ⟪u, pullback U A v⟫_ℂ = ⟪U u, diagonal A (U v)⟫_ℂ :=
  U.toContinuousLinearMap.adjoint_inner_right u (diagonal A (U v))

theorem pullback_hasSum (U : KrausIsometry H) (A : H →L[ℂ] H) (u v : H) :
    HasSum (fun n => ⟪U u n, A (U v n)⟫_ℂ) ⟪u, pullback U A v⟫_ℂ := by
  rw [pullback_inner]
  exact lp.hasSum_inner (𝕜 := ℂ) (U u) (diagonal A (U v))

theorem observable {R : Gaussian.RankOneData H T} (N : NormalTraceData R)
    (F : NormalFunctionalData R) (U : KrausIsometry H) (A : H →L[ℂ] H)
    {x : T} (hx : x ∈ R.positive) :
    F.repr (N.extend U x) A = F.repr x (pullback U A) := by
  let B := ((ContinuousLinearMap.apply ℂ ℂ A).restrictScalars ℝ).comp F.repr
  let C := ((ContinuousLinearMap.apply ℂ ℂ (pullback U A)).restrictScalars ℝ).comp F.repr
  apply N.observable U B C _ hx
  intro v
  change F.repr (pure R U v) A = F.repr (R.rankOne v) (pullback U A)
  rw [F.rankOne]
  exact (F.observable_hasSum (pure_hasSum R U v) A).unique (pullback_hasSum U A v v)

/-- Exact bounded-operator composition implies the same actual normal
channel identity on all positive traces. -/
theorem compose {R : Gaussian.RankOneData H T} (N : NormalTraceData R)
    (F : NormalFunctionalData R) (U V W : KrausIsometry H)
    (h : ∀ A, pullback V (pullback U A) = pullback W A)
    {x : T} (hx : x ∈ R.positive) :
    N.extend U (N.extend V x) = N.extend W x := by
  apply F.isometry.injective
  ext A
  rw [observable N F U A (N.positive V hx), observable N F V _ hx,
    observable N F W A hx, h]

theorem equal {R : Gaussian.RankOneData H T} (N : NormalTraceData R)
    (F : NormalFunctionalData R) (U V : KrausIsometry H)
    (h : ∀ A, pullback U A = pullback V A)
    {x : T} (hx : x ∈ R.positive) : N.extend U x = N.extend V x := by
  apply F.isometry.injective
  ext A
  rw [observable N F U A hx, observable N F V A hx, h]

end GptLean.PhysicalChannelDual
