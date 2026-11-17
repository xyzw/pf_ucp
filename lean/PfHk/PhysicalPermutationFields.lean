import PfHk.PhysicalReferencePermutation
import PfHk.CenteredPhysicalReference

/-! The actual particle field at center zero transforms with the same
particle index as the weak derivative. Consequently the free physical
kinetic and radiation forms are invariant under simultaneous pullback. -/

noncomputable section
namespace PfHk.PhysicalReferencePermutation

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.SymmetricLift GptLean.PhysicalPolarization
  PfHk.CenteredPhysicalReference PfHk.PhysicalLocalEnergy
open scoped InnerProductSpace ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 40000

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff)
  (C : CanonicalSectorCCR photonMeasure) (e : ℝ)

theorem profile_permutation (π : Equiv.Perm (Fin N)) (q : Fin N × Fin 3)
    (X : Configuration N) :
    profile F χ 0 (π q.1, q.2) (permuteConfiguration π X) = profile F χ 0 q X := by
  simp only [profile, zero_add, particle_permute, π.symm_apply_apply]

theorem field_permutation (π : Equiv.Perm (Fin N)) (u : Free (N := N))
    (q : Fin N × Fin 3) :
    field (Fin N × Fin 3) (fun _ => 0) C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) q (permutation π u) =
    pull π (field (Fin N × Fin 3) (fun _ => 0) C (profile F χ 0)
      (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) (π q.1, q.2) u) := by
  apply Lp.ext
  have hs := (permuteConfiguration π).measurePreserving.quasiMeasurePreserving.ae
    (spatialField_ae volume C (profile F χ 0 (π q.1, q.2))
      (profile_measurable F χ 0 (π q.1, q.2)) (profileBound F χ)
      (profile_bound F χ 0 (π q.1, q.2))
      (radiationSource (Fin N × Fin 3) (fun _ => 0) u))
  filter_upwards [spatialField_ae volume C (profile F χ 0 q)
      (profile_measurable F χ 0 q) (profileBound F χ) (profile_bound F χ 0 q)
      (radiationSource (Fin N × Fin 3) (fun _ => 0) (permutation π u)),
    pull_ae π (field (Fin N × Fin 3) (fun _ => 0) C (profile F χ 0)
      (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) (π q.1, q.2) u),
    hs, pull_ae π (radiationSource (Fin N × Fin 3) (fun _ => 0) u)] with X hf hp hsp hr
  have hrad : radiationSource (Fin N × Fin 3) (fun _ => 0) (permutation π u) X =
      radiationSource (Fin N × Fin 3) (fun _ => 0) u (permuteConfiguration π X) :=
    (congrArg (fun z : RadiationGraph (Fin N × Fin 3) => z X)
      (radiationSource_permutation π u)).trans hr
  exact hf.trans ((congrArg (kernelField C (profile F χ 0 q X)) hrad).trans
    ((congrArg (fun k : WeightedPhotonKernel => kernelField C k
      (radiationSource (Fin N × Fin 3) (fun _ => 0) u (permuteConfiguration π X)))
        (profile_permutation F χ π q X).symm).trans (hsp.symm.trans hp.symm)))

theorem covariant_permutation (π : Equiv.Perm (Fin N)) (u : Free (N := N))
    (q : Fin N × Fin 3) :
    covariant (Fin N × Fin 3) (fun _ => 0) C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e q (permutation π u) =
    pull π (covariant (Fin N × Fin 3) (fun _ => 0) C (profile F χ 0)
      (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e (π q.1, q.2) u) := by
  have h₁ := covariant_apply (Fin N × Fin 3) (fun _ => 0) C (profile F χ 0)
    (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e q (permutation π u)
  have h₂ := covariant_apply (Fin N × Fin 3) (fun _ => 0) C (profile F χ 0)
    (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e (π q.1, q.2) u
  exact h₁.trans ((congrArg₂ (fun a b : WaveSpace (Fin N × Fin 3) =>
    (-Complex.I) • a - (e : ℂ) • b) (ordinary_permutation π u q)
      (field_permutation F χ C π u q)).trans
    ((by simp only [map_sub, map_smul] :
      (-Complex.I) • pull π (ordinary (Fin N × Fin 3) (fun _ => 0) (π q.1, q.2) u) -
        (e : ℂ) • pull π (field (Fin N × Fin 3) (fun _ => 0) C (profile F χ 0)
          (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) (π q.1, q.2) u) =
      pull π ((-Complex.I) • ordinary (Fin N × Fin 3) (fun _ => 0) (π q.1, q.2) u -
        (e : ℂ) • field (Fin N × Fin 3) (fun _ => 0) C (profile F χ 0)
          (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) (π q.1, q.2) u)).trans
      (congrArg (pull π) h₂.symm)))

theorem radiation_inner_permutation (π : Equiv.Perm (Fin N)) (u v : Free (N := N)) :
    ⟪radiation (Fin N × Fin 3) (fun _ => 0) (permutation π u),
      radiation (Fin N × Fin 3) (fun _ => 0) (permutation π v)⟫_ℂ =
    ⟪radiation (Fin N × Fin 3) (fun _ => 0) u,
      radiation (Fin N × Fin 3) (fun _ => 0) v⟫_ℂ :=
  (congrArg₂ (fun a b : WaveSpace (Fin N × Fin 3) => ⟪a, b⟫_ℂ)
    (radiation_permutation π u) (radiation_permutation π v)).trans
      ((pull (Q := PhotonFock) π).inner_map_map _ _)

theorem kinetic_inner_permutation (π : Equiv.Perm (Fin N)) (u v : Free (N := N)) :
    (∑ q : Fin N × Fin 3, ⟪covariant (Fin N × Fin 3) (fun _ => 0) C (profile F χ 0)
        (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e q (permutation π u),
      covariant (Fin N × Fin 3) (fun _ => 0) C (profile F χ 0)
        (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e q (permutation π v)⟫_ℂ) =
    ∑ q : Fin N × Fin 3, ⟪covariant (Fin N × Fin 3) (fun _ => 0) C (profile F χ 0)
        (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e q u,
      covariant (Fin N × Fin 3) (fun _ => 0) C (profile F χ 0)
        (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e q v⟫_ℂ := by
  calc
    _ = ∑ q : Fin N × Fin 3, ⟪covariant (Fin N × Fin 3) (fun _ => 0) C (profile F χ 0)
        (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e (π q.1, q.2) u,
      covariant (Fin N × Fin 3) (fun _ => 0) C (profile F χ 0)
        (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e (π q.1, q.2) v⟫_ℂ := by
      apply Finset.sum_congr rfl
      intro q _
      exact (congrArg₂ (fun a b : WaveSpace (Fin N × Fin 3) => ⟪a, b⟫_ℂ)
        (covariant_permutation F χ C e π u q) (covariant_permutation F χ C e π v q)).trans
          ((pull (Q := PhotonFock) π).inner_map_map _ _)
    _ = _ := (Equiv.prodCongr π (Equiv.refl (Fin 3))).sum_comp
      (fun q : Fin N × Fin 3 =>
        ⟪covariant (Fin N × Fin 3) (fun _ => 0) C (profile F χ 0)
          (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e q u,
          covariant (Fin N × Fin 3) (fun _ => 0) C (profile F χ 0)
          (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e q v⟫_ℂ)

theorem potential_zero (u : Free (N := N)) :
    potential (Fin N × Fin 3) (fun _ => 0) u = 0 := by
  apply Lp.ext
  filter_upwards [(potentialSource (Fin N × Fin 3) (fun _ => 0) u).property,
    Lp.coeFn_zero PhotonFock 2 (volume : Measure (Configuration N))] with X hp hz
  change potential (Fin N × Fin 3) (fun _ => 0) u X = _
  have hs : (Real.sqrt (0 : ℝ) : ℂ) •
      (potentialSource (Fin N × Fin 3) (fun _ => 0) u).val.1 X = 0 := by
    simp only [Real.sqrt_zero, Complex.ofReal_zero, zero_smul]
  exact hp.trans (hs.trans hz.symm)

theorem form_permutation (π : Equiv.Perm (Fin N)) (u v : Free (N := N)) :
    form (fun _ => 0) C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e (permutation π u) (permutation π v) =
    form (fun _ => 0) C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e u v := by
  simp only [form, potential_zero, inner_zero_left, add_zero]
  exact congrArg₂ (· + ·)
    (congrArg (fun z : ℂ => (1 / 2 : ℂ) * z) (kinetic_inner_permutation F χ C e π u v))
    (radiation_inner_permutation π u v)

end PfHk.PhysicalReferencePermutation
