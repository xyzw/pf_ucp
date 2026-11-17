import GptLean.PhysicalH1Permutation
import PfHk.PhysicalComparisonDomain

/-! Particle pullbacks on the actual free reference graph. The map acts
on the electronic H1 graph and on the L2 radiation graph, and reconstructs
the zero potential coordinate. No domain-invariance premise is used. -/

noncomputable section
namespace PfHk.PhysicalReferencePermutation

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.SymmetricLift
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

variable {N : ℕ}

abbrev Free := Reference (Fin N × Fin 3) (fun _ => 0)

section Pull
variable {Q Q' : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q]
  [NormedAddCommGroup Q'] [NormedSpace ℂ Q']

def pull (π : Equiv.Perm (Fin N)) :
    Lp Q 2 (volume : Measure (Configuration N)) →ₗᵢ[ℂ]
      Lp Q 2 (volume : Measure (Configuration N)) :=
  Lp.compMeasurePreservingₗᵢ ℂ (permuteConfiguration π)
    (permuteConfiguration π).measurePreserving

theorem pull_ae (π : Equiv.Perm (Fin N)) (u : Lp Q 2 (volume : Measure (Configuration N))) :
    pull π u =ᵐ[volume] fun x => u (permuteConfiguration π x) :=
  Lp.coeFn_compMeasurePreserving u (permuteConfiguration π).measurePreserving

theorem pull_compLpL (π : Equiv.Perm (Fin N)) (L : Q →L[ℂ] Q')
    (u : Lp Q 2 (volume : Measure (Configuration N))) :
    pull π (L.compLpL 2 volume u) = L.compLpL 2 volume (pull π u) := by
  apply Lp.ext
  filter_upwards [pull_ae π (L.compLpL 2 volume u),
    (permuteConfiguration π).measurePreserving.quasiMeasurePreserving.ae (L.coeFn_compLpL u),
    L.coeFn_compLpL (pull π u), pull_ae π u] with x h₁ h₂ h₃ h₄
  exact h₁.trans (h₂.trans (h₃.trans (congrArg L h₄)).symm)

theorem pull_one (u : Lp Q 2 (volume : Measure (Configuration N))) : pull 1 u = u := by
  apply Lp.ext
  filter_upwards [pull_ae 1 u] with x hx
  simpa only [permuteConfiguration_one] using hx

theorem pull_pull (π σ : Equiv.Perm (Fin N))
    (u : Lp Q 2 (volume : Measure (Configuration N))) :
    pull π (pull σ u) = pull (σ * π) u := by
  apply Lp.ext
  filter_upwards [pull_ae π (pull σ u),
    (permuteConfiguration π).measurePreserving.quasiMeasurePreserving.ae (pull_ae σ u),
    pull_ae (σ * π) u] with x h₁ h₂ h₃
  exact h₁.trans (h₂.trans ((congrArg u (permuteConfiguration_mul σ π x)).symm.trans h₃.symm))
end Pull

local instance radiationGraphNormedSpace : NormedSpace ℂ RadiationGraphSpace :=
  radiationRoot.graph.normedSpace

private def zeroPotential (w : WaveSpace (Fin N × Fin 3)) :
    PotentialGraph (Fin N × Fin 3) (fun _ => 0) :=
  ⟨(w, 0), by
    filter_upwards [Lp.coeFn_zero PhotonFock 2 (volume : Measure (Configuration N))] with x hx
    simp only [hx, Pi.zero_apply, Real.sqrt_zero, Complex.ofReal_zero, zero_smul]⟩

set_option maxHeartbeats 80000 in
def permuted (π : Equiv.Perm (Fin N)) (u : Free (N := N)) : Free (N := N) :=
  ⟨(PhysicalH1Permutation.permutation (H := PhotonFock) π
      (electronic (Fin N × Fin 3) (fun _ => 0) u),
    pull (Q := RadiationGraphSpace) π (radiationSource (Fin N × Fin 3) (fun _ => 0) u),
    zeroPotential (N := N) (pull (Q := PhotonFock) π
      (inclusion (Fin N × Fin 3) (fun _ => 0) u))), by
    change (pull π (inclusion (Fin N × Fin 3) (fun _ => 0) u) -
      spatialRadiationInclusion volume
        (pull π (radiationSource (Fin N × Fin 3) (fun _ => 0) u)),
      pull π (inclusion (Fin N × Fin 3) (fun _ => 0) u) -
        pull π (inclusion (Fin N × Fin 3) (fun _ => 0) u)) = (0, 0)
    apply Prod.ext
    · exact sub_eq_zero.mpr ((congrArg (pull π)
        (radiation_matches (Fin N × Fin 3) (fun _ => 0) u)).symm.trans
          (pull_compLpL π radiationGraphInclusion _))
    · exact sub_self _⟩

theorem inclusion_permuted (π : Equiv.Perm (Fin N)) (u : Free (N := N)) :
    inclusion (Fin N × Fin 3) (fun _ => 0) (permuted π u) =
      pull π (inclusion (Fin N × Fin 3) (fun _ => 0) u) := rfl

def permutation (π : Equiv.Perm (Fin N)) : Free (N := N) →ₗ[ℂ] Free (N := N) where
  toFun := permuted π
  map_add' u v := inclusion_injective (Fin N × Fin 3) (fun _ => 0) (by
    simp only [inclusion_permuted, map_add])
  map_smul' c u := inclusion_injective (Fin N × Fin 3) (fun _ => 0) (by
    simp only [inclusion_permuted, map_smul, RingHom.id_apply])

theorem inclusion_permutation (π : Equiv.Perm (Fin N)) (u : Free (N := N)) :
    inclusion (Fin N × Fin 3) (fun _ => 0) (permutation π u) =
      pull π (inclusion (Fin N × Fin 3) (fun _ => 0) u) := rfl

theorem ordinary_permutation (π : Equiv.Perm (Fin N)) (u : Free (N := N))
    (q : Fin N × Fin 3) :
    ordinary (Fin N × Fin 3) (fun _ => 0) q (permutation π u) =
      pull π (ordinary (Fin N × Fin 3) (fun _ => 0) (π q.1, q.2) u) := rfl

theorem radiationSource_permutation (π : Equiv.Perm (Fin N)) (u : Free (N := N)) :
    radiationSource (Fin N × Fin 3) (fun _ => 0) (permutation π u) =
      pull π (radiationSource (Fin N × Fin 3) (fun _ => 0) u) := rfl

theorem radiation_permutation (π : Equiv.Perm (Fin N)) (u : Free (N := N)) :
    radiation (Fin N × Fin 3) (fun _ => 0) (permutation π u) =
      pull π (radiation (Fin N × Fin 3) (fun _ => 0) u) :=
  (pull_compLpL π radiationGraphDerivative _).symm

attribute [local irreducible] permutation

theorem permutation_one (u : Free (N := N)) : permutation (N := N) 1 u = u := by
  apply inclusion_injective (Fin N × Fin 3) (fun _ => 0)
  exact (inclusion_permutation 1 u).trans (pull_one _)

theorem permutation_permutation (π σ : Equiv.Perm (Fin N)) (u : Free (N := N)) :
    permutation π (permutation σ u) = permutation (σ * π) u := by
  apply inclusion_injective (Fin N × Fin 3) (fun _ => 0)
  exact (inclusion_permutation π _).trans
    ((congrArg (pull π) (inclusion_permutation σ u)).trans
      ((pull_pull π σ _).trans (inclusion_permutation (σ * π) u).symm))

end PfHk.PhysicalReferencePermutation
