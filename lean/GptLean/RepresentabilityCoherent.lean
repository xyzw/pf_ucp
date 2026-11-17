import GptLean.RepresentabilityCoherentBackground
import GptLean.PhysicalFockCCR

/-!
Coherent vectors and their ordinary differential and field identities on
the concrete Fock model. The Weyl law is an explicit universal premise.
Norm, connection, metric and field expectations are proved from that law
and the existing sector operators, rather than included in its fields.
-/

noncomputable section
set_option Elab.async false

namespace GptLean.Representability

open MeasureTheory GptLean.PhysicalFock
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]

theorem finiteNumberSupport_vacuum :
    FiniteNumberSupport μ 0 (creationWord μ []) := by
  intro n hn
  exact lp.single_apply_ne 2 0 (vacuumSector μ) (by omega)

theorem vacuum_creationWord_inner (h : Lp ℂ 2 μ) :
    ⟪creationWord μ [], creationWord μ [h]⟫_ℂ = 0 := by
  change ⟪lp.single 2 0 (vacuumSector μ),
    lp.single 2 1 (creationSector μ 0 h (vacuumSector μ))⟫_ℂ = 0
  rw [lp.inner_single_left, lp.single_apply_ne _ _ _ (by decide : (0 : ℕ) ≠ 1)]
  exact inner_zero_right _

theorem creationWord_vacuum_inner (h : Lp ℂ 2 μ) :
    ⟪creationWord μ [h], creationWord μ []⟫_ℂ = 0 := by
  rw [inner_eq_zero_symm]
  exact vacuum_creationWord_inner μ h

/-- Every one-coordinate wavefunction is symmetric. -/
theorem oneSector_symmetric (u : FullSector μ 1) : u ∈ symmetricSubspace μ 1 := by
  intro π
  apply Lp.ext
  filter_upwards [permutation_ae μ 1 π u] with k hk
  apply hk.trans
  change u ((MeasurableEquiv.piCongrLeft (fun _ : Fin 1 => Ω) π) k) = u k
  congr 1
  funext i
  have hi : π i = i := Subsingleton.elim _ _
  simpa only [hi] using
    MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin 1 => Ω) π k i

/-- Vacuum creation is an isometry directly from the concrete insertion.
No CCR background is needed in the zero-particle sector. -/
theorem creationWord_single_norm (h : Lp ℂ 2 μ) :
    ‖creationWord μ [h]‖ = ‖h‖ := by
  rw [creationWord_norm]
  simp only [creationWordSector, List.length_nil, creationSector, Nat.cast_zero,
    zero_add, Real.sqrt_one, Complex.ofReal_one, one_smul,
    ContinuousLinearMap.comp_apply]
  rw [(symmetricSubspace μ 1).norm_orthogonalProjectionOnto_apply
    (oneSector_symmetric μ _), tensorInsertion_norm]
  change ‖h‖ * ‖vacuumSector μ‖ = ‖h‖
  rw [vacuumSector_norm, mul_one]

theorem creationWord_single_norm_sq (h : Lp ℂ 2 μ) :
    ‖creationWord μ [h]‖ ^ 2 = ‖h‖ ^ 2 := by
  rw [creationWord_single_norm]

theorem annihilationGraph_vacuum (g : Lp ℂ 2 μ) :
    AnnihilationGraph μ g (creationWord μ []) 0 := by
  intro n
  change 0 = annihilationSector μ n g ((lp.single 2 0 (vacuumSector μ)) (n + 1))
  rw [lp.single_apply_ne _ _ _ (by omega : n + 1 ≠ 0), map_zero]

theorem segalGraph_vacuum (g : Lp ℂ 2 μ) :
    SegalGraph μ g (creationWord μ []) (creationWord μ [g]) := by
  intro n
  rcases n with _ | _ | n
  · simp [creationWord, creationWordSector, segalCoordinate, lp.evalCLM]
  · simp [creationWord, creationWordSector, segalCoordinate, lp.evalCLM]
  · simp [creationWord, creationWordSector, segalCoordinate, lp.evalCLM]

namespace AnnihilationGraph

theorem unique {g : Lp ℂ 2 μ} {u v w : Fock μ}
    (hv : AnnihilationGraph μ g u v) (hw : AnnihilationGraph μ g u w) : v = w := by
  apply lp.ext
  funext n
  exact (hv n).trans (hw n).symm

theorem form_eq {g : Lp ℂ 2 μ} {u v : Fock μ} (h : AnnihilationGraph μ g u v) :
    annihilationForm μ g u = ENNReal.ofReal (‖v‖ ^ 2) := by
  unfold annihilationForm
  have hn : ∀ n, annihilationSector μ n g (u (n + 1)) = v n := fun n => (h n).symm
  simp_rw [hn]
  simpa only [weightedForm, one_mul] using massForm_eq (Sector μ) v

end AnnihilationGraph

theorem norm_add_pow_two_of_inner_eq_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (x y : H) (h : ⟪x, y⟫_ℂ = 0) :
    ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  simpa only [pow_two] using
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero x y h

namespace ConcreteWeylLaw

variable (W : ConcreteWeylLaw μ)

/-- The normalized coherent vector in the actual Fock space. -/
def coherent (f : Lp ℂ 2 μ) : Fock μ := W.weyl f (creationWord μ [])

theorem coherent_norm (f : Lp ℂ 2 μ) : ‖W.coherent μ f‖ = 1 := by
  rw [coherent, (W.weyl f).norm_map, vacuum_norm]

theorem coherent_continuous : Continuous (W.coherent μ) :=
  W.continuous.comp (continuous_id.prodMk continuous_const)

/-- Its derivative is constructed from the finite vacuum generator. -/
def coherentDerivative (f : Lp ℂ 2 μ) : Lp ℂ 2 μ →L[ℝ] Fock μ :=
  finiteWeylDerivative μ W.weyl 0 f (creationWord μ [])

theorem coherent_hasFDerivAt (f : Lp ℂ 2 μ) :
    HasFDerivAt (W.coherent μ) (W.coherentDerivative μ f) f :=
  W.finite_derivative 0 _ (finiteNumberSupport_vacuum μ) f

theorem coherentDerivative_apply (f h : Lp ℂ 2 μ) :
    W.coherentDerivative μ f h = W.weyl f
      (creationWord μ [h] + (Complex.I * ((⟪f, h⟫_ℂ).im : ℂ)) • creationWord μ []) := by
  rw [coherentDerivative, finiteWeylDerivative_apply,
    annihilationFinite_vacuum, sub_zero, creationFinite_word μ 0 h [] (by simp)]

theorem coherent_connection (f h : Lp ℂ 2 μ) :
    ⟪W.coherent μ f, W.coherentDerivative μ f h⟫_ℂ =
      Complex.I * ((⟪f, h⟫_ℂ).im : ℂ) := by
  rw [coherent, coherentDerivative_apply, (W.weyl f).inner_map_map,
    inner_add_right, vacuum_creationWord_inner, inner_smul_right,
    inner_self_eq_norm_sq_to_K, vacuum_norm]
  simp

theorem coherent_metric (f h : Lp ℂ 2 μ) :
    ‖W.coherentDerivative μ f h‖ ^ 2 = ‖h‖ ^ 2 + (⟪f, h⟫_ℂ).im ^ 2 := by
  rw [coherentDerivative_apply, (W.weyl f).norm_map,
    norm_add_pow_two_of_inner_eq_zero _ _
      (by rw [inner_smul_right, creationWord_vacuum_inner, mul_zero]),
    creationWord_single_norm_sq μ, norm_smul, vacuum_norm, mul_one,
    norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem coherent_connection_zero (f h : Lp ℂ 2 μ) (hreal : (⟪f, h⟫_ℂ).im = 0) :
    ⟪W.coherent μ f, W.coherentDerivative μ f h⟫_ℂ = 0 := by
  rw [coherent_connection, hreal, Complex.ofReal_zero, mul_zero]

theorem coherent_real_metric (f h : Lp ℂ 2 μ) (hreal : (⟪f, h⟫_ℂ).im = 0) :
    ‖W.coherentDerivative μ f h‖ ^ 2 = ‖h‖ ^ 2 := by
  rw [coherent_metric μ W, hreal, zero_pow (by decide : 2 ≠ 0), add_zero]

theorem coherent_annihilationGraph (f g : Lp ℂ 2 μ) :
    AnnihilationGraph μ g (W.coherent μ f) (⟪g, f⟫_ℂ • W.coherent μ f) := by
  simpa only [coherent, zero_add, map_smul] using
    W.annihilation_shift f g _ _ (annihilationGraph_vacuum μ g)

theorem coherent_annihilationForm (f g : Lp ℂ 2 μ) :
    annihilationForm μ g (W.coherent μ f) = ENNReal.ofReal (‖⟪g, f⟫_ℂ‖ ^ 2) := by
  rw [(W.coherent_annihilationGraph μ f g).form_eq μ, norm_smul,
    coherent_norm, mul_one]

/-- The actual field output after the vacuum field graph is shifted. -/
def coherentField (f g : Lp ℂ 2 μ) : Fock μ :=
  W.weyl f (creationWord μ [g] + ((2 * (⟪g, f⟫_ℂ).re : ℝ) : ℂ) • creationWord μ [])

theorem coherentField_graph (f g : Lp ℂ 2 μ) :
    SegalGraph μ g (W.coherent μ f) (W.coherentField μ f g) :=
  W.field_shift f g _ _ (segalGraph_vacuum μ g)

theorem coherentField_expectation (f g : Lp ℂ 2 μ) :
    ⟪W.coherent μ f, W.coherentField μ f g⟫_ℂ = ((2 * (⟪g, f⟫_ℂ).re : ℝ) : ℂ) := by
  rw [coherent, coherentField, (W.weyl f).inner_map_map, inner_add_right,
    vacuum_creationWord_inner, inner_smul_right, inner_self_eq_norm_sq_to_K,
    vacuum_norm]
  simp

end ConcreteWeylLaw
end GptLean.Representability
