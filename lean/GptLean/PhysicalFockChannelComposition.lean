import GptLean.PhysicalChannelDual
import GptLean.PhysicalFockWordComposition
import GptLean.PhysicalFockChannel

/-!
Actual photon-channel composition from creation-word coassociation.
The environmental basis is arbitrary. Equality is first proved for
bounded Heisenberg operators and then transported to positive traces.
-/

noncomputable section
namespace GptLean.PhysicalFock.ChannelComposition

open MeasureTheory PhotonLocalizationFockChannel PhotonLocalizationChannel
open TensorCoordinates SplitCoassociation PhysicalNormalTrace
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true

private theorem pullback_inner_of_coordinates {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (U : KrausIsometry H) (V : H →ₗᵢ[ℂ] K)
    (J : K →ₗᵢ[ℂ] lp (fun _ : ℕ => H) 2)
    (A : H →L[ℂ] H) (B : K →L[ℂ] K)
    (hfactor : ∀ u, U u = J (V u))
    (hcoord : ∀ z n, J (B z) n = A (J z n)) (u v : H) :
    ⟪u, PhysicalChannelDual.pullback U A v⟫_ℂ = ⟪V u, B (V v)⟫_ℂ := by
  have h := lp.hasSum_inner (𝕜 := ℂ) (J (V u)) (J (B (V v)))
  rw [J.inner_map_map] at h
  simp only [hcoord] at h
  have hp := PhysicalChannelDual.pullback_hasSum U A u v
  simp only [hfactor] at hp
  exact hp.unique h

variable (BF : StandardSymmetricFockExponential)

private theorem factor_apply
    (j : Lp ℂ 2 photonMeasure →ₗᵢ[ℂ]
      WithLp 2 (Lp ℂ 2 photonMeasure × Lp ℂ 2 photonMeasure)) (u : PhotonFock) :
    (photonFactorization BF).factor j u =
      environmentalCoordinates PhotonFock ((photonExponential BF).split photonMeasure j u) := rfl

theorem pullback_inner
    (j : Lp ℂ 2 photonMeasure →ₗᵢ[ℂ]
      WithLp 2 (Lp ℂ 2 photonMeasure × Lp ℂ 2 photonMeasure))
    (A : PhotonFock →L[ℂ] PhotonFock) (u v : PhotonFock) :
    ⟪u, PhysicalChannelDual.pullback ((photonFactorization BF).factor j) A v⟫_ℂ =
      ⟪(photonExponential BF).split photonMeasure j u,
        retainedOperator A ((photonExponential BF).split photonMeasure j v)⟫_ℂ := by
  apply pullback_inner_of_coordinates ((photonFactorization BF).factor j)
    ((photonExponential BF).split photonMeasure j) (environmentalCoordinates PhotonFock)
    A (retainedOperator A)
  · exact factor_apply BF j
  · exact environmentalCoordinates_retainedOperator A

theorem pullback_word
    (j : Lp ℂ 2 photonMeasure →ₗᵢ[ℂ]
      WithLp 2 (Lp ℂ 2 photonMeasure × Lp ℂ 2 photonMeasure))
    (A : PhotonFock →L[ℂ] PhotonFock) (w z : List (Lp ℂ 2 photonMeasure)) :
    ⟪creationWord photonMeasure w,
      PhysicalChannelDual.pullback ((photonFactorization BF).factor j) A
        (creationWord photonMeasure z)⟫_ℂ =
      couple photonMeasure j
        (fun a b => ⟪creationWord photonMeasure a, A (creationWord photonMeasure b)⟫_ℂ) w z := by
  exact (pullback_inner BF j A (creationWord photonMeasure w) (creationWord photonMeasure z)).trans
    (couple_observable photonMeasure (photonExponential BF) j A w z).symm

include BF in
private theorem eq_of_word_inner (u v : PhotonFock)
    (h : ∀ w, ⟪creationWord photonMeasure w, u⟫_ℂ =
      ⟪creationWord photonMeasure w, v⟫_ℂ) : u = v := by
  have he : innerSL ℂ u = innerSL ℂ v := by
    apply (photonExponential BF).ext_words photonMeasure
    intro w
    change ⟪u, creationWord photonMeasure w⟫_ℂ = ⟪v, creationWord photonMeasure w⟫_ℂ
    simpa only [inner_conj_symm] using (congrArg (starRingEnd ℂ) (h w))
  apply ext_inner_right ℂ
  intro x
  exact congrArg (fun L : PhotonFock →L[ℂ] ℂ => L x) he

/-- Three actual one-photon component identities suffice, with no
composition premise on the Fock channel itself. -/
theorem pullback_comp
    (j k : Lp ℂ 2 photonMeasure →ₗᵢ[ℂ]
      WithLp 2 (Lp ℂ 2 photonMeasure × Lp ℂ 2 photonMeasure))
    (h₁ : ∀ f, retainedMap j (retainedMap k f) = retainedMap j f)
    (h₂ : ∀ f, discardedMap photonMeasure j (retainedMap k f) =
      retainedMap k (discardedMap photonMeasure j f))
    (h₃ : ∀ f, discardedMap photonMeasure k f =
      discardedMap photonMeasure k (discardedMap photonMeasure j f))
    (A : PhotonFock →L[ℂ] PhotonFock) :
    PhysicalChannelDual.pullback ((photonFactorization BF).factor k)
      (PhysicalChannelDual.pullback ((photonFactorization BF).factor j) A) =
        PhysicalChannelDual.pullback ((photonFactorization BF).factor j) A := by
  apply (photonExponential BF).ext_words photonMeasure
  intro z
  apply eq_of_word_inner BF
  intro w
  simp_rw [pullback_word]
  exact couple_comp photonMeasure (photonExponential BF) j k h₁ h₂ h₃ _ w z

theorem channel_comp (BT : StandardNormalTraceBackground)
    (j k : Lp ℂ 2 photonMeasure →ₗᵢ[ℂ]
      WithLp 2 (Lp ℂ 2 photonMeasure × Lp ℂ 2 photonMeasure))
    (h₁ : ∀ f, retainedMap j (retainedMap k f) = retainedMap j f)
    (h₂ : ∀ f, discardedMap photonMeasure j (retainedMap k f) =
      retainedMap k (discardedMap photonMeasure j f))
    (h₃ : ∀ f, discardedMap photonMeasure k f =
      discardedMap photonMeasure k (discardedMap photonMeasure j f))
    {x : BT.Trace PhotonFock} (hx : x ∈ (BT.realization PhotonFock).rank.positive) :
    BT.normal.extend ((photonFactorization BF).factor j)
      (BT.normal.extend ((photonFactorization BF).factor k) x) =
        BT.normal.extend ((photonFactorization BF).factor j) x :=
  PhysicalChannelDual.compose BT.normal (BT.realization PhotonFock).functional _ _ _
    (pullback_comp BF j k h₁ h₂ h₃) hx

end GptLean.PhysicalFock.ChannelComposition
