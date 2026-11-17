import PfHk.PhysicalPermutationFields
import PfHk.PhysicalCoefficientPermutation
import PfHk.PhysicalCommonFormDomain

/-! Permutation covariance of the actual rough external multipliers and
the full identical-particle Pauli--Fierz form. The common-domain premise
of the intermediate lemmas is discharged in the public theorem. -/

noncomputable section
namespace PfHk.PhysicalReferencePermutation

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.SymmetricLift GptLean.PhysicalPolarization GptLean.PhysicalPairDuality
  PfHk.CenteredPhysicalReference PfHk.PhysicalLocalEnergy
  PfHk.PhysicalCommonFormDomain PfHk.PhysicalCoefficientPermutation
open scoped InnerProductSpace ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 60000

local instance permutationPhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _

variable {N : ℕ}

theorem roughMultiply_permutation (π : Equiv.Perm (Fin N))
    (b b' : Configuration N → ℝ)
    (hb : ∀ X, b' (permuteConfiguration π X) = b X)
    (u : Free (N := N))
    (hu : HasMultiplier b' (inclusion (Fin N × Fin 3) (fun _ => 0) u))
    (hp : HasMultiplier b (inclusion (Fin N × Fin 3) (fun _ => 0) (permutation π u))) :
    roughMultiply b (inclusion (Fin N × Fin 3) (fun _ => 0) (permutation π u)) hp =
      pull π (roughMultiply b' (inclusion (Fin N × Fin 3) (fun _ => 0) u) hu) := by
  apply Lp.ext
  have hr := (permuteConfiguration π).measurePreserving.quasiMeasurePreserving.ae
    (roughMultiply_ae b' (inclusion (Fin N × Fin 3) (fun _ => 0) u) hu)
  filter_upwards [roughMultiply_ae b (inclusion (Fin N × Fin 3) (fun _ => 0)
      (permutation π u)) hp,
    pull_ae π (roughMultiply b' (inclusion (Fin N × Fin 3) (fun _ => 0) u) hu), hr,
    pull_ae π (inclusion (Fin N × Fin 3) (fun _ => 0) u)] with X h₁ h₂ h₃ h₄
  have hvalue := (congrArg (fun z : WaveSpace (Fin N × Fin 3) => z X)
    (inclusion_permutation π u)).trans h₄
  exact h₁.trans ((congrArg (fun z : PhotonFock => b X • z) hvalue).trans
    ((congrArg (fun r : ℝ => r • inclusion (Fin N × Fin 3) (fun _ => 0) u
      (permuteConfiguration π X)) (hb X).symm).trans (h₃.symm.trans h₂.symm)))

variable (F : Frame) (χ : ArticleCutoff) (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
  (A : VectorPotential) (v : ScalarPotential) (c : ℝ)
  (D : ∀ u : Free (N := N),
    ExternalDomain (fun _ => 0) (vector A) (positive v c) (negative v c) u)

theorem vector_multiplier_permutation (π : Equiv.Perm (Fin N)) (u : Free (N := N))
    (q : Fin N × Fin 3) :
    roughMultiply (vector A q) (inclusion (Fin N × Fin 3) (fun _ => 0) (permutation π u))
      ((D (permutation π u)).vector q) =
      pull π (roughMultiply (vector A (π q.1, q.2))
        (inclusion (Fin N × Fin 3) (fun _ => 0) u) ((D u).vector (π q.1, q.2))) :=
  roughMultiply_permutation π (vector A q) (vector A (π q.1, q.2))
    (fun X => by simpa only [π.symm_apply_apply, Prod.mk.eta] using
      vector_permutation A π (π q.1, q.2) X) u _ _

theorem positive_multiplier_permutation (π : Equiv.Perm (Fin N)) (u : Free (N := N)) :
    roughMultiply (positive v c) (inclusion (Fin N × Fin 3) (fun _ => 0) (permutation π u))
      (D (permutation π u)).positive =
      pull π (roughMultiply (positive v c) (inclusion (Fin N × Fin 3) (fun _ => 0) u)
        (D u).positive) :=
  roughMultiply_permutation π (positive v c) (positive v c)
    (positive_permutation v c π) u _ _

theorem negative_multiplier_permutation (π : Equiv.Perm (Fin N)) (u : Free (N := N)) :
    roughMultiply (negative v c) (inclusion (Fin N × Fin 3) (fun _ => 0) (permutation π u))
      (D (permutation π u)).negative =
      pull π (roughMultiply (negative v c) (inclusion (Fin N × Fin 3) (fun _ => 0) u)
        (D u).negative) :=
  roughMultiply_permutation π (negative v c) (negative v c)
    (negative_permutation v c π) u _ _

theorem externalCovariant_permutation (π : Equiv.Perm (Fin N)) (u : Free (N := N))
    (q : Fin N × Fin 3) :
    externalCovariant (fun _ => 0) C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c) (negative v c)
      (permutation π u) (D (permutation π u)) q =
      pull π (externalCovariant (fun _ => 0) C (profile F χ 0) (profile_measurable F χ 0)
        (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c) (negative v c)
        u (D u) (π q.1, q.2)) :=
  (congrArg₂ (fun a b : WaveSpace (Fin N × Fin 3) => a + b)
    (covariant_permutation F χ C e π u q)
    (vector_multiplier_permutation A v c D π u q)).trans ((pull π).map_add _ _).symm

theorem external_kinetic_inner_permutation (π : Equiv.Perm (Fin N))
    (u w : Free (N := N)) :
    (∑ q : Fin N × Fin 3,
      ⟪externalCovariant (fun _ => 0) C (profile F χ 0) (profile_measurable F χ 0)
        (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c) (negative v c)
        (permutation π u) (D (permutation π u)) q,
      externalCovariant (fun _ => 0) C (profile F χ 0) (profile_measurable F χ 0)
        (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c) (negative v c)
        (permutation π w) (D (permutation π w)) q⟫_ℂ) =
    ∑ q : Fin N × Fin 3,
      ⟪externalCovariant (fun _ => 0) C (profile F χ 0) (profile_measurable F χ 0)
        (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c) (negative v c) u (D u) q,
      externalCovariant (fun _ => 0) C (profile F χ 0) (profile_measurable F χ 0)
        (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c) (negative v c) w (D w) q⟫_ℂ := by
  let f : (Fin N × Fin 3) → ℂ := fun q =>
    ⟪externalCovariant (fun _ => 0) C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c) (negative v c) u (D u) q,
    externalCovariant (fun _ => 0) C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c) (negative v c) w (D w) q⟫_ℂ
  calc
    _ = ∑ q : Fin N × Fin 3, f (π q.1, q.2) := by
      apply Finset.sum_congr rfl
      intro q _
      exact (congrArg₂ (fun a b : WaveSpace (Fin N × Fin 3) => ⟪a, b⟫_ℂ)
        (externalCovariant_permutation F χ C e A v c D π u q)
        (externalCovariant_permutation F χ C e A v c D π w q)).trans
          ((pull (Q := PhotonFock) π).inner_map_map _ _)
    _ = _ := (Equiv.prodCongr π (Equiv.refl (Fin 3))).sum_comp f

theorem externalForm_permutation_of_domain (π : Equiv.Perm (Fin N))
    (u w : Free (N := N)) :
    externalForm (fun _ => 0) C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c) (negative v c)
      (permutation π u) (permutation π w) (D (permutation π u)) (D (permutation π w)) =
    externalForm (fun _ => 0) C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c) (negative v c)
      u w (D u) (D w) := by
  have hpositive := (congrArg₂ (fun a b : WaveSpace (Fin N × Fin 3) => ⟪a, b⟫_ℂ)
    (positive_multiplier_permutation A v c D π u)
    (positive_multiplier_permutation A v c D π w)).trans
      ((pull (Q := PhotonFock) π).inner_map_map _ _)
  have hnegative := (congrArg₂ (fun a b : WaveSpace (Fin N × Fin 3) => ⟪a, b⟫_ℂ)
    (negative_multiplier_permutation A v c D π u)
    (negative_multiplier_permutation A v c D π w)).trans
      ((pull (Q := PhotonFock) π).inner_map_map _ _)
  simp only [externalForm, potential_zero, inner_zero_left, add_zero]
  exact congrArg₂ (· - ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·)
    (congrArg (fun z : ℂ => (1 / 2 : ℂ) * z)
      (external_kinetic_inner_permutation F χ C e A v c D π u w))
    (radiation_inner_permutation π u w)) hpositive) hnegative

omit D in
theorem externalForm_permutation (hc : 0 ≤ c) (π : Equiv.Perm (Fin N))
    (u w : Free (N := N)) :
    externalForm (fun _ => 0) C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c) (negative v c)
      (permutation π u) (permutation π w)
      (externalDomain A v c hc (permutation π u)) (externalDomain A v c hc (permutation π w)) =
    externalForm (fun _ => 0) C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c) (negative v c)
      u w (externalDomain A v c hc u) (externalDomain A v c hc w) :=
  externalForm_permutation_of_domain F χ C e A v c (externalDomain A v c hc) π u w

end PfHk.PhysicalReferencePermutation
