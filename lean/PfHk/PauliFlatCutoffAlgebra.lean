import PfHk.PauliLocalEnergy

/-! A scalar cutoff that fixes a Pauli contraction and annihilates the
cutoff error can be moved out of the first argument of its kinetic form. -/

noncomputable section
namespace PfHk.PauliFlatCutoffAlgebra

open PfHk.PauliSpin PfHk.PauliCurrentAlgebra
open scoped InnerProductSpace

set_option Elab.async false
set_option maxHeartbeats 30000

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem sigma_pair_zero (n : Fin N) (k : Fin 3) (B : H →L[ℂ] H)
    (hB : ∀ x y, inner ℂ x (B y) = inner ℂ (B x) y)
    (v d : SpinIndex N → H) (hd : ∀ s, B (d s) = 0) :
    (∑ s, inner ℂ (sigmaFamily n k (fun t => B (v t)) s) (d s)) = 0 := by
  have hm (s : SpinIndex N) : B (sigmaFamily n k d s) = 0 := by
    have h := congrFun (sigmaFamily_map n k B.toLinearMap d) s
    change sigmaFamily n k (fun t => B (d t)) s = B (sigmaFamily n k d s) at h
    have hz : (fun t => B (d t)) = 0 := funext hd
    rw [hz] at h
    simpa only [sigmaFamily, Pi.zero_apply, smul_zero, ite_self] using h.symm
  rw [sigmaFamily_selfadjoint]
  calc
    _ = ∑ s, inner ℂ (v s) (B (sigmaFamily n k d s)) :=
      Finset.sum_congr rfl (fun s _ => (hB _ _).symm)
    _ = 0 := by simp only [hm, inner_zero_right, Finset.sum_const_zero]

theorem error_pair_zero (n : Fin N) (B : Fin 3 → H →L[ℂ] H)
    (hB : ∀ k x y, inner ℂ x (B k y) = inner ℂ (B k x) y)
    (v d : SpinIndex N → H) (hd : ∀ k s, B k (d s) = 0) :
    (∑ s, inner ℂ (contraction n (fun k t => (-Complex.I) • B k (v t)) s) (d s)) = 0 := by
  have hk (k : Fin 3) := sigma_pair_zero n k (B k) (hB k)
    (fun s => (-Complex.I) • v s) d (hd k)
  simp only [map_smul] at hk
  simp only [contraction, Finset.sum_apply, sum_inner]
  exact Finset.sum_comm.trans (by simp only [hk, Finset.sum_const_zero])

theorem kinetic_fixed {S : Type*} [Fintype S] (L : H →L[ℂ] H)
    (hL : ∀ x y, inner ℂ x (L y) = inner ℂ (L x) y)
    (d v err : S → H) (hfix : ∀ s, L (d s) = d s)
    (herr : (∑ s, inner ℂ (err s) (d s)) = 0) :
    (∑ s, inner ℂ (L (v s) + err s) (d s)) = ∑ s, inner ℂ (v s) (d s) := by
  simp only [inner_add_left, Finset.sum_add_distrib, herr, add_zero]
  exact Finset.sum_congr rfl (fun s _ =>
    (hL (v s) (d s)).symm.trans (congrArg (fun w : H => inner ℂ (v s) w) (hfix s)))

theorem form_fixed {K₁ K₂ R₁ R₂ P₁ P₂ M₁ M₂ : ℂ}
    (hK : K₁ = K₂) (hR : R₁ = R₂) (hP : P₁ = P₂) (hM : M₁ = M₂) :
    (1 / 2 : ℂ) * K₁ + R₁ + P₁ - M₁ = (1 / 2 : ℂ) * K₂ + R₂ + P₂ - M₂ := by
  rw [hK, hR, hP, hM]

end PfHk.PauliFlatCutoffAlgebra
