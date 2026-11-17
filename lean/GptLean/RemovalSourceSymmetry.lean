import GptLean.RemovalLatticeSymmetry

/-! WIS acts on the photon factor, so its universal commutation with
electronic permutations transfers the original fermionic character to
the conditional source. Localization then preserves it. -/

namespace GptLean.RemovalSource

open MeasureTheory MeasureTheory.Measure Filter Repair SymmetricLift

variable {Q H K Hr Kr Hs : Type*} [MeasurableSpace Q] {μ : Measure Q}
  [SFinite μ] {N : ℕ}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup Hr] [InnerProductSpace ℂ Hr]
  [NormedAddCommGroup Kr] [InnerProductSpace ℂ Kr]
  [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]

/-- Universal photon-factor commutation, independent of the source and
the removal construction. -/
def SpatialPermutationIntertwining
    (U : Lp H 2 (volume : Measure (Configuration N)) ≃ₗᵢ[ℂ]
      Lp K 2 (μ.prod (volume : Measure (Configuration N)))) : Prop :=
  ∀ (π : Equiv.Perm (Fin N)) (u v : Lp H 2 (volume : Measure (Configuration N))),
    (u : Configuration N → H) =ᵐ[volume] (fun x => v (permuteConfiguration π x)) →
      (U u : Q × Configuration N → K) =ᵐ[μ.prod volume]
        (fun qx => U v (qx.1, permuteConfiguration π qx.2))

theorem LatticeSourceData.original_source_character
    (D : LatticeSourceData N μ H K Hr Kr Hs)
    (hU : SpatialPermutationIntertwining D.U) (χ : Equiv.Perm (Fin N) → ℂ)
    (hχ : ∀ n, HasElectronicCharacter (fun π => permuteConfiguration π) χ (D.ψ n)) :
    ∀ n, ∀ᵐ q ∂μ, HasElectronicCharacter (fun π => permuteConfiguration π) χ
      (fun x => D.original.source n (q, x)) := by
  classical
  intro n
  have hp (π : Equiv.Perm (Fin N)) : ∀ᵐ qx ∂μ.prod volume,
      D.U (D.ψ n) (qx.1, permuteConfiguration π qx.2) = χ π • D.U (D.ψ n) qx := by
    have hs : ((χ π • D.ψ n : Lp H 2 (volume : Measure (Configuration N))) :
        Configuration N → H) =ᵐ[volume] (fun x => D.ψ n (permuteConfiguration π x)) := by
      filter_upwards [Lp.coeFn_smul (χ π) (D.ψ n), hχ n π] with x hx hπ
      rw [hx, Pi.smul_apply, hπ]
    have he := hU π (χ π • D.ψ n) (D.ψ n) hs
    rw [map_smul] at he
    filter_upwards [he, Lp.coeFn_smul (χ π) (D.U (D.ψ n))] with qx hqx hsx
    rw [hsx, Pi.smul_apply] at hqx
    exact hqx.symm
  exact ae_all_iff.mpr (fun π => ae_ae_of_ae_prod (hp π))

theorem LatticeSourceData.conditioned_character_from_original
    (D : LatticeSourceData N μ H K Hr Kr Hs) (R : ℝ) (hR : 0 < R)
    (hU : SpatialScalarIntertwining D.U) (hperm : SpatialPermutationIntertwining D.U)
    (χ : Equiv.Perm (Fin N) → ℂ)
    (hχ : ∀ n, HasElectronicCharacter (fun π => permuteConfiguration π) χ (D.ψ n)) :
    ∀ n, ∀ᵐ q ∂μ, HasElectronicCharacter (fun π => permuteConfiguration π) χ
      (fun x => (D.conditioned R hR).source n (q, x)) :=
  D.conditioned_source_character R hR hU χ (D.original_source_character hperm χ hχ)

end GptLean.RemovalSource
