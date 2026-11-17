import GptLean.PhysicalFockChannelComposition
import GptLean.PhysicalFockElectronicWords

/-!
Electronic matrix elements intertwine the full pointwise Kraus channel
with its photon channel. This proves composition for arbitrary bounded
coupled observables, not just observables acting on the photon factor.
-/

noncomputable section
namespace GptLean.PhysicalFock.ElectronicComposition

open MeasureTheory PhotonLocalizationChannel PhotonLocalizationFockChannel
open PhysicalNormalTrace PhysicalL2HilbertSum
open scoped ENNReal InnerProductSpace

variable {X : Type} [MeasurableSpace X] {μ : Measure X}

section General
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def matrixElement (f g : Lp ℂ 2 μ)
    (A : Lp H 2 μ →L[ℂ] Lp H 2 μ) : H →L[ℂ] H :=
  (tensor f).adjoint.comp (A.comp (tensor g))

theorem matrixElement_inner (f g : Lp ℂ 2 μ)
    (A : Lp H 2 μ →L[ℂ] Lp H 2 μ) (u v : H) :
    ⟪u, matrixElement f g A v⟫_ℂ = ⟪tensor f u, A (tensor g v)⟫_ℂ :=
  (tensor f).adjoint_inner_right u (A (tensor g v))

theorem matrixElement_ext
    (A B : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (h : ∀ f g, matrixElement f g A = matrixElement f g B) : A = B := by
  apply ext_spatial_tensors
  intro g v
  have he : innerSL ℂ (A (tensor g v)) = innerSL ℂ (B (tensor g v)) := by
    apply ext_spatial_tensors
    intro f u
    have hm := congrArg (fun M : H →L[ℂ] H => ⟪u, M v⟫_ℂ) (h f g)
    simp only [matrixElement_inner] at hm
    simpa only [innerSL_apply_apply, inner_conj_symm] using congrArg (starRingEnd ℂ) hm
  apply ext_inner_right ℂ
  intro x
  exact congrArg (fun L : Lp H 2 μ →L[ℂ] ℂ => L x) he

theorem matrixElement_lift_pullback (U : KrausIsometry H)
    (f g : Lp ℂ 2 μ) (A : Lp H 2 μ →L[ℂ] Lp H 2 μ) :
    matrixElement f g (PhysicalChannelDual.pullback (KrausL2.lift μ U) A) =
      PhysicalChannelDual.pullback U (matrixElement f g A) := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℂ
  intro u
  rw [matrixElement_inner]
  have hf := PhysicalChannelDual.pullback_hasSum (KrausL2.lift μ U) A (tensor f u) (tensor g v)
  have hp := PhysicalChannelDual.pullback_hasSum U (matrixElement f g A) u v
  apply hf.unique
  apply hp.congr_fun
  intro n
  rw [matrixElement_inner, lift_tensor, lift_tensor]

theorem lift_pullback_eq (U V : KrausIsometry H)
    (h : ∀ A, PhysicalChannelDual.pullback U A = PhysicalChannelDual.pullback V A)
    (A : Lp H 2 μ →L[ℂ] Lp H 2 μ) :
    PhysicalChannelDual.pullback (KrausL2.lift μ U) A =
      PhysicalChannelDual.pullback (KrausL2.lift μ V) A := by
  apply matrixElement_ext
  intro f g
  simp only [matrixElement_lift_pullback, h]

end General

variable (BF : StandardSymmetricFockExponential)

theorem matrixElement_pullback
    (j : Lp ℂ 2 photonMeasure →ₗᵢ[ℂ]
      WithLp 2 (Lp ℂ 2 photonMeasure × Lp ℂ 2 photonMeasure))
    (f g : Lp ℂ 2 μ) (A : Lp PhotonFock 2 μ →L[ℂ] Lp PhotonFock 2 μ) :
    matrixElement f g
      (PhysicalChannelDual.pullback
        ((electronicFactorization μ (photonFactorization BF)).factor j) A) =
      PhysicalChannelDual.pullback ((photonFactorization BF).factor j)
        (matrixElement f g A) := by
  exact matrixElement_lift_pullback ((photonFactorization BF).factor j) f g A

theorem pullback_comp
    (j k : Lp ℂ 2 photonMeasure →ₗᵢ[ℂ]
      WithLp 2 (Lp ℂ 2 photonMeasure × Lp ℂ 2 photonMeasure))
    (h₁ : ∀ f, retainedMap j (retainedMap k f) = retainedMap j f)
    (h₂ : ∀ f, discardedMap photonMeasure j (retainedMap k f) =
      retainedMap k (discardedMap photonMeasure j f))
    (h₃ : ∀ f, discardedMap photonMeasure k f =
      discardedMap photonMeasure k (discardedMap photonMeasure j f))
    (A : Lp PhotonFock 2 μ →L[ℂ] Lp PhotonFock 2 μ) :
    PhysicalChannelDual.pullback ((electronicFactorization μ (photonFactorization BF)).factor k)
      (PhysicalChannelDual.pullback
        ((electronicFactorization μ (photonFactorization BF)).factor j) A) =
      PhysicalChannelDual.pullback ((electronicFactorization μ (photonFactorization BF)).factor j) A := by
  apply matrixElement_ext
  intro f g
  simp only [matrixElement_pullback]
  exact ChannelComposition.pullback_comp BF j k h₁ h₂ h₃ (matrixElement f g A)

theorem channel_comp (BT : StandardNormalTraceBackground)
    (j k : Lp ℂ 2 photonMeasure →ₗᵢ[ℂ]
      WithLp 2 (Lp ℂ 2 photonMeasure × Lp ℂ 2 photonMeasure))
    (h₁ : ∀ f, retainedMap j (retainedMap k f) = retainedMap j f)
    (h₂ : ∀ f, discardedMap photonMeasure j (retainedMap k f) =
      retainedMap k (discardedMap photonMeasure j f))
    (h₃ : ∀ f, discardedMap photonMeasure k f =
      discardedMap photonMeasure k (discardedMap photonMeasure j f))
    {x : BT.Trace (Lp PhotonFock 2 μ)}
    (hx : x ∈ (BT.realization (Lp PhotonFock 2 μ)).rank.positive) :
    BT.normal.extend ((electronicFactorization μ (photonFactorization BF)).factor j)
      (BT.normal.extend ((electronicFactorization μ (photonFactorization BF)).factor k) x) =
      BT.normal.extend ((electronicFactorization μ (photonFactorization BF)).factor j) x :=
  PhysicalChannelDual.compose BT.normal (BT.realization (Lp PhotonFock 2 μ)).functional _ _ _
    (pullback_comp BF j k h₁ h₂ h₃) hx

end GptLean.PhysicalFock.ElectronicComposition
