import PfHk.PauliCurrent

/-! Marginal density and current covariance from identities on the actual
configuration-space spinor. This passage is shared by phase and photon
displacements. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliPairCovariance

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPairSpace
  GptLean.PhysicalSourceCoordinates GptLean.PhysicalSourcePair GptLean.SymmetricLift
  PfHk.PauliSpin PfHk.PauliCurrent

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 60000

variable {N : ℕ}
attribute [local irreducible] wave pauliVelocity particlePair pair densityL1 currentL1
  ElectronicH1Complex.complexWeakGraph ElectronicH1Complex.value

private theorem vector_sum_apply {ι : Type*} [Fintype ι] (f : ι → Vector) (a : Fin 3) :
    (∑ i, f i) a = ∑ i, f i a :=
  map_sum (EuclideanSpace.proj a : Vector →L[ℝ] ℝ) f Finset.univ

private theorem current_scaling {r b j' j ρ f g : ℝ}
    (h₁ : j' = r * (f + b * g)) (h₂ : j = r * f) (h₃ : ρ = r * g) :
    j' = j + b * ρ := by
  rw [h₁, h₂, h₃]
  ring

private theorem cancel_average (hN : 0 < N) (j f : Fin N → ℝ)
    (h : ∀ n, j n = (N : ℝ) * f n) :
    (N : ℝ)⁻¹ * ∑ n, j n = ∑ n, f n := by
  calc
    (N : ℝ)⁻¹ * ∑ n, j n = (N : ℝ)⁻¹ * ∑ n, (N : ℝ) * f n :=
      congrArg ((N : ℝ)⁻¹ * ·) (Finset.sum_congr rfl (fun n _ => h n))
    _ = _ := by
      rw [← Finset.mul_sum, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN.ne'), one_mul]

private theorem sum_current_shift (j' j ρ : Fin N → ℝ) (b : ℝ)
    (h : ∀ n, j' n = j n + b * ρ n) :
    (∑ n, j' n) = (∑ n, j n) + b * ∑ n, ρ n :=
  (Finset.sum_congr rfl (fun n _ => h n)).trans (by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum])

theorem particle_density_eq (i : Fin N) (u u' : Components (N := N))
    (d d' : Derivatives (N := N))
    (hρ : (fun X => ‖wave u' X‖ ^ 2) =ᵐ[volume] fun X => ‖wave u X‖ ^ 2) :
    densityL1 (particlePair i u' d') = densityL1 (particlePair i u d) := by
  apply Lp.ext
  have hp := Measure.ae_ae_of_ae_prod
    ((split_symm_measurePreserving i).quasiMeasurePreserving.ae hρ)
  filter_upwards [particle_density_ae i u' d', particle_density_ae i u d, hp]
    with x h₁ h₂ hx
  rw [h₁, h₂]
  exact congrArg (fun r : ℝ => (N : ℝ) * r) (integral_congr_ae hx)

private theorem real_inner_marginal {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (i : Fin N)
    (w z : Lp H 2 (volume : Measure (PhysicalSourceCoordinates.Configuration N))) :
    (fun x => (∫ y, inner ℂ (w ((split i).symm (x,y)))
      (z ((split i).symm (x,y)))).re) =ᵐ[volume]
      fun x => ∫ y, (inner ℂ (w ((split i).symm (x,y)))
        (z ((split i).symm (x,y)))).re := by
  have hi := (split_symm_measurePreserving i).integrable_comp_of_integrable
    (L2.integrable_inner (𝕜 := ℂ) w z)
  filter_upwards [hi.prod_right_ae] with x hx
  exact (integral_re hx).symm

private theorem marginal_add_mul (i : Fin N)
    (f f' g : PhysicalSourceCoordinates.Configuration N → ℝ) (b : PhysicalPairSpace.Position → ℝ)
    (hf : Integrable f volume)
    (hbg : Integrable (fun X => b (particle X i) * g X) volume)
    (he : f' =ᵐ[volume] fun X => f X + b (particle X i) * g X) :
    (fun x => ∫ y, f' ((split i).symm (x,y))) =ᵐ[volume]
      fun x => (∫ y, f ((split i).symm (x,y))) + b x * ∫ y, g ((split i).symm (x,y)) := by
  have hp := Measure.ae_ae_of_ae_prod
    ((split_symm_measurePreserving i).quasiMeasurePreserving.ae he)
  have hi := (split_symm_measurePreserving i).integrable_comp_of_integrable hf
  have hb := (split_symm_measurePreserving i).integrable_comp_of_integrable hbg
  filter_upwards [hp, hi.prod_right_ae, hb.prod_right_ae] with x hx hix hbx
  have hsplit (y : Spectator i) : particle ((split i).symm (x,y)) i = x := by
    rw [← split_fst_eq_particle, (split i).apply_symm_apply]
  exact (integral_congr_ae hx).trans ((integral_add hix hbx).trans
    (congrArg (fun r : ℝ => (∫ y, f ((split i).symm (x,y))) + r)
      ((integral_congr_ae (ae_of_all _ fun y => congrArg
        (fun z => b z * g ((split i).symm (x,y))) (hsplit y))).trans (integral_const_mul _ _))))

theorem particle_current_shift (i : Fin N) (u u' : Components (N := N))
    (d d' : Derivatives (N := N)) (a : Fin 3) (b : PhysicalPairSpace.Position → ℝ)
    (hcurrent : (fun X => (inner ℂ (wave (N := N) u' X) (pauliVelocity (N := N) d' i a X)).re) =ᵐ[volume]
      fun X => (inner ℂ (wave (N := N) u X) (pauliVelocity (N := N) d i a X)).re +
        b (particle X i) * ‖wave (N := N) u X‖ ^ 2)
    (hbi : Integrable (fun X => b (particle X i) * ‖wave (N := N) u X‖ ^ 2) volume) :
    (fun x => currentL1 (particlePair (N := N) i u' d') x a) =ᵐ[volume]
      fun x => currentL1 (particlePair (N := N) i u d) x a +
        b x * densityL1 (particlePair (N := N) i u d) x := by
  have hm := marginal_add_mul i
    (fun X => (inner ℂ (wave (N := N) u X) (pauliVelocity (N := N) d i a X)).re)
    (fun X => (inner ℂ (wave (N := N) u' X) (pauliVelocity (N := N) d' i a X)).re)
    (fun X => ‖wave (N := N) u X‖ ^ 2) b
    (L2.integrable_inner (𝕜 := ℂ) (wave (N := N) u) (pauliVelocity (N := N) d i a)).re hbi hcurrent
  filter_upwards [particle_current_ae (N := N) i u' d' a,
    particle_current_ae (N := N) i u d a, particle_density_ae (N := N) i u d,
    real_inner_marginal (H := Fiber N PhotonFock) i (wave (N := N) u) (pauliVelocity (N := N) d i a),
    real_inner_marginal (H := Fiber N PhotonFock) i (wave (N := N) u') (pauliVelocity (N := N) d' i a), hm]
    with x hj' hj hρ hr hr' hmarg
  have h1 := hj'.trans (congrArg (fun r : ℝ => (N : ℝ) * r) (hr'.trans hmarg))
  have h2 := hj.trans (congrArg (fun r : ℝ => (N : ℝ) * r) hr)
  exact current_scaling h1 h2 hρ

private theorem map_pair {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : Pair →L[ℝ] E) (u : Components (N := N)) (d : Derivatives (N := N)) :
    L (pair (N := N) u d) = (N : ℝ)⁻¹ • ∑ n : Fin N, L (particlePair (N := N) n u d) :=
  (congrArg L (pair_def (N := N) u d)).trans
    ((map_smul L (N : ℝ)⁻¹ (∑ n : Fin N, particlePair (N := N) n u d)).trans
      (congrArg (fun z : E => (N : ℝ)⁻¹ • z)
        (map_sum L (fun n : Fin N => particlePair (N := N) n u d) Finset.univ)))

private theorem average_current_ae (P : Fin N → Pair) (a : Fin 3) :
    (fun x => ((N : ℝ)⁻¹ • ∑ n : Fin N, currentL1 (P n) : Lp Vector 1 volume) x a) =ᵐ[volume]
      fun x => (N : ℝ)⁻¹ * ∑ n : Fin N, currentL1 (P n) x a := by
  filter_upwards [Lp.coeFn_smul (N : ℝ)⁻¹ (∑ n : Fin N, currentL1 (P n)),
    Lp.coeFn_finsetSum Finset.univ (fun n : Fin N => currentL1 (P n))] with x hsm hsum
  simp only [hsm, hsum, Pi.smul_apply, PiLp.smul_apply, vector_sum_apply,
    Finset.sum_apply, smul_eq_mul]

private theorem average_density_ae (P : Fin N → Pair) :
    ((N : ℝ)⁻¹ • ∑ n : Fin N, densityL1 (P n) : Lp ℝ 1 volume) =ᵐ[volume]
      fun x => (N : ℝ)⁻¹ * ∑ n : Fin N, densityL1 (P n) x := by
  filter_upwards [Lp.coeFn_smul (N : ℝ)⁻¹ (∑ n : Fin N, densityL1 (P n)),
    Lp.coeFn_finsetSum Finset.univ (fun n : Fin N => densityL1 (P n))] with x hsm hsum
  simp only [hsm, hsum, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]


theorem pair_density_eq (u u' : Components (N := N)) (d d' : Derivatives (N := N))
    (hρ : (fun X => ‖wave (N := N) u' X‖ ^ 2) =ᵐ[volume] fun X => ‖wave (N := N) u X‖ ^ 2) :
    densityL1 (pair (N := N) u' d') = densityL1 (pair (N := N) u d) :=
  (map_pair densityL1 u' d').trans
    ((congrArg (fun r : Lp ℝ 1 (volume : Measure PhysicalPairSpace.Position) => (N : ℝ)⁻¹ • r)
      (Finset.sum_congr rfl (fun i _ => particle_density_eq (N := N) i u u' d d' hρ))).trans
      (map_pair densityL1 u d).symm)

private theorem pair_current_average (u : Components (N := N)) (d : Derivatives (N := N))
    (a : Fin 3) :
    (fun x => currentL1 (pair (N := N) u d) x a) =ᵐ[volume]
      fun x => (N : ℝ)⁻¹ * ∑ n : Fin N, currentL1 (particlePair (N := N) n u d) x a :=
  (Filter.EventuallyEq.of_eq (congrArg
    (fun j : Lp Vector 1 (volume : Measure PhysicalPairSpace.Position) => fun x => j x a)
    (map_pair currentL1 u d))).trans
      (average_current_ae (fun n : Fin N => particlePair (N := N) n u d) a)

private theorem pair_density_average (u : Components (N := N)) (d : Derivatives (N := N)) :
    (densityL1 (pair (N := N) u d) : PhysicalPairSpace.Position → ℝ) =ᵐ[volume]
      fun x => (N : ℝ)⁻¹ * ∑ n : Fin N, densityL1 (particlePair (N := N) n u d) x :=
  (Filter.EventuallyEq.of_eq (congrArg
    (fun j : Lp ℝ 1 (volume : Measure PhysicalPairSpace.Position) => (j : PhysicalPairSpace.Position → ℝ))
    (map_pair densityL1 u d))).trans
      (average_density_ae (fun n : Fin N => particlePair (N := N) n u d))

theorem pair_current_ae (hN : 0 < N) (u : Components (N := N))
    (d : Derivatives (N := N)) (a : Fin 3) :
    (fun x => currentL1 (pair (N := N) u d) x a) =ᵐ[volume]
      fun x => ∑ n : Fin N, (∫ y, inner ℂ (wave (N := N) u ((split n).symm (x,y)))
        (pauliVelocity (N := N) d n a ((split n).symm (x,y)))).re := by
  filter_upwards [pair_current_average u d a,
    ae_all_iff.mpr (fun n : Fin N => particle_current_ae (N := N) n u d a)] with x hx hp
  exact hx.trans (cancel_average hN
    (fun n : Fin N => currentL1 (particlePair (N := N) n u d) x a)
    (fun n : Fin N => (∫ y, inner ℂ (wave (N := N) u ((split n).symm (x,y)))
      (pauliVelocity (N := N) d n a ((split n).symm (x,y)))).re) hp)

theorem pair_current_shift (u u' : Components (N := N)) (d d' : Derivatives (N := N))
    (a : Fin 3) (b : PhysicalPairSpace.Position → ℝ)
    (hcurrent : ∀ i : Fin N, (fun X => (inner ℂ (wave (N := N) u' X) (pauliVelocity (N := N) d' i a X)).re) =ᵐ[volume]
      fun X => (inner ℂ (wave (N := N) u X) (pauliVelocity (N := N) d i a X)).re +
        b (particle X i) * ‖wave (N := N) u X‖ ^ 2)
    (hbi : ∀ i : Fin N, Integrable (fun X => b (particle X i) * ‖wave (N := N) u X‖ ^ 2) volume) :
    (fun x => currentL1 (pair (N := N) u' d') x a) =ᵐ[volume]
      fun x => currentL1 (pair (N := N) u d) x a + b x * densityL1 (pair (N := N) u d) x := by
  filter_upwards [pair_current_average u' d' a, pair_current_average u d a,
    pair_density_average u d,
    ae_all_iff.mpr (fun i : Fin N => particle_current_shift (N := N) i u u' d d' a b
      (hcurrent i) (hbi i))] with x hj' hj hρ hx
  have he := sum_current_shift
    (fun n : Fin N => currentL1 (particlePair (N := N) n u' d') x a)
    (fun n : Fin N => currentL1 (particlePair (N := N) n u d) x a)
    (fun n : Fin N => densityL1 (particlePair (N := N) n u d) x) (b x) hx
  exact current_scaling (hj'.trans (congrArg (fun r : ℝ => (N : ℝ)⁻¹ * r) he)) hj hρ

end PfHk.PauliPairCovariance

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
