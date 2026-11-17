import GptLean.PhysicalFockExponential
import GptLean.PhysicalFockKrausL2
import GptLean.PhysicalNormalTrace

/-!
The normal photon channel on the concrete coupled electronic/Fock model.

A fixed one-photon unitary (in particular the physical Fourier transform)
conjugates a splitting to momentum space. The exponential law is matched
to the actual creation operators, the environmental coordinates are
constructed, and the electronic lift is pointwise. Normal trace calculus
then gives positivity, trace preservation, and fermionic state stability.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory PhotonLocalizationChannel PhotonLocalizationFockChannel
  PhysicalNormalTrace PhysicalNormalTrace.StandardNormalTraceBackground
open scoped ENNReal

section Transport
variable {h k H : Type*} [NormedAddCommGroup h] [InnerProductSpace ℂ h]
  [NormedAddCommGroup k] [InnerProductSpace ℂ k]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- One-photon unitary conjugation, including both retained and discarded outputs. -/
def transportSplit (e : h ≃ₗᵢ[ℂ] k) (j : h →ₗᵢ[ℂ] WithLp 2 (h × h)) :
    k →ₗᵢ[ℂ] WithLp 2 (k × k) :=
  (LinearIsometryEquiv.withLpProdCongr 2 e e).toLinearIsometry.comp
    (j.comp e.symm.toLinearIsometry)

@[simp] theorem transportSplit_retained (e : h ≃ₗᵢ[ℂ] k)
    (j : h →ₗᵢ[ℂ] WithLp 2 (h × h)) (u : k) :
    retainedMap (transportSplit e j) u = e (retainedMap j (e.symm u)) := rfl

def transportFactorization (e : h ≃ₗᵢ[ℂ] k) (F : FockFactorization k H) :
    FockFactorization h H where
  factor j := F.factor (transportSplit e j)
end Transport

variable (BF : StandardSymmetricFockExponential) (BT : StandardNormalTraceBackground)
  {h : Type} [NormedAddCommGroup h] [InnerProductSpace ℂ h]
  (e : h ≃ₗᵢ[ℂ] Lp ℂ 2 photonMeasure) (N : ℕ)

/-- The same actual photon factorization with the electronic factor included. -/
def fullFactorization : FockFactorization h (FullHilbert N) :=
  electronicFactorization (volume : Measure (SymmetricLift.Configuration N))
    (transportFactorization e (photonFactorization BF))

/-- The concrete normal channel for an arbitrary one-photon split. -/
def fullChannel (j : h →ₗᵢ[ℂ] WithLp 2 (h × h)) : BT.FullTrace N →L[ℝ] BT.FullTrace N :=
  (BT.normal (H := FullHilbert N)).extend ((fullFactorization BF e N).factor j)

theorem fullChannel_positive (j : h →ₗᵢ[ℂ] WithLp 2 (h × h)) {x : BT.FullTrace N}
    (hx : x ∈ (BT.realization (FullHilbert N)).rank.positive) :
    fullChannel BF BT e N j x ∈ (BT.realization (FullHilbert N)).rank.positive :=
  BT.normal.positive _ hx

theorem fullChannel_trace (j : h →ₗᵢ[ℂ] WithLp 2 (h × h)) {x : BT.FullTrace N}
    (hx : x ∈ (BT.realization (FullHilbert N)).rank.positive) :
    (BT.realization (FullHilbert N)).rank.trace (fullChannel BF BT e N j x) =
      (BT.realization (FullHilbert N)).rank.trace x :=
  BT.normal.trace _ hx

/-- Fermionic stability follows from the constructed fiber action of every Kraus coordinate. -/
theorem fullChannel_fermionic (j : h →ₗᵢ[ℂ] WithLp 2 (h × h)) {x : BT.FullTrace N}
    (hx : x ∈ BT.fermionicStates N) :
    fullChannel BF BT e N j x ∈ BT.fermionicStates N := by
  apply BT.fermionicStates_channel N ((fullFactorization BF e N).factor j)
    (fun n => (lp.evalCLM ℂ (fun _ : ℕ => PhotonFock) 2 n).comp
      ((photonFactorization BF).factor (transportSplit e j)).toContinuousLinearMap)
    (fun _ _ => rfl) hx

end GptLean.PhysicalFock
