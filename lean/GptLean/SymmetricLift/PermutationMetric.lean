import GptLean.SymmetricLift.PermutationGeometry
import GptLean.SymmetricLift.MetricGeometry

/-! Particle permutations preserve both the pair energy and coordinate metric. -/
noncomputable section
namespace GptLean.SymmetricLift
open scoped BigOperators

theorem particle_permute {N : ℕ} (π : Equiv.Perm (Fin N)) (x : Configuration N)
    (i : Fin N) : particle (permuteConfiguration π x) i = particle x (π.symm i) := by
  ext μ
  rfl

theorem pairEnergy_permute {N : ℕ} (π : Equiv.Perm (Fin N)) (x : Configuration N) :
    pairEnergy (permuteConfiguration π x) = pairEnergy x := by
  apply le_antisymm
  · exact pairEnergy_embedding _ _ π.symm.toEmbedding (particle_permute π x)
  · apply pairEnergy_embedding _ _ π.toEmbedding
    intro i
    change particle x i = particle (permuteConfiguration π x) (π i)
    rw [particle_permute, π.symm_apply_apply]

theorem permuteConfiguration_single {N : ℕ} (π : Equiv.Perm (Fin N))
    (q : Fin N × Fin 3) :
    permuteConfiguration π (EuclideanSpace.single q 1) =
      EuclideanSpace.single (π q.1, q.2) 1 := by
  exact LinearIsometryEquiv.piLpCongrLeft_single (p := 2) (𝕜 := ℝ) (E := ℝ)
    (Equiv.prodCongr π (Equiv.refl (Fin 3))) q 1

/-- This sum identity applies to the actual derivative of every orbit branch. -/
theorem permuteConfiguration_coordinate_metric {N : ℕ}
    (π : Equiv.Perm (Fin N)) {K : Type*} [NormedAddCommGroup K]
    (L : Configuration N → K) :
    (∑ q : Fin N × Fin 3, ‖L (permuteConfiguration π (EuclideanSpace.single q 1))‖ ^ 2) =
      ∑ q : Fin N × Fin 3, ‖L (EuclideanSpace.single q 1)‖ ^ 2 := by
  simp only [permuteConfiguration_single]
  exact Fintype.sum_equiv (Equiv.prodCongr π (Equiv.refl (Fin 3))) _ _ (fun _ => rfl)

end GptLean.SymmetricLift
