import GptLean.RepresentabilityCoherent
import GptLean.RepresentabilityOnePhotonTag

/-!
The actual Weyl-displaced one-photon auxiliary vector. The derivative
identities are consequences of the finite-number differential law and
sector orthogonality. Orthogonality of its kernel to the auxiliary modes
is expressed by ordinary annihilation and is later obtained from support.
-/

noncomputable section
set_option Elab.async false

namespace GptLean.Representability

open MeasureTheory GptLean.PhysicalFock
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]

theorem finiteNumberSupport_onePhoton (z : Sector μ 1) :
    FiniteNumberSupport μ 1 (lp.single 2 1 z) := by
  intro n hn
  exact lp.single_apply_ne 2 1 z (by omega)

theorem onePhoton_annihilationGraph (g : Lp ℂ 2 μ) (z : Sector μ 1) :
    AnnihilationGraph μ g (lp.single 2 1 z)
      (lp.single 2 0 (annihilationSector μ 0 g z)) := by
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [lp.single_apply_self]
  · rw [lp.single_apply_ne _ _ _ hn,
      lp.single_apply_ne _ _ _ (by omega : n + 1 ≠ 1), map_zero]

theorem onePhoton_annihilation_inner (g : Lp ℂ 2 μ) (z : Sector μ 1) :
    ⟪lp.single 2 0 (annihilationSector μ 0 g z), lp.single 2 1 z⟫_ℂ = 0 := by
  rw [lp.inner_single_left, lp.single_apply_ne _ _ _ (by decide : (0 : ℕ) ≠ 1)]
  exact inner_zero_right _

namespace ConcreteWeylLaw

variable (W : ConcreteWeylLaw μ)

/-- The trial photon factor in the full physical Fock space. -/
def displacedOnePhoton (f : Lp ℂ 2 μ) (z : Sector μ 1) : Fock μ :=
  W.weyl f (lp.single 2 1 z)

theorem displacedOnePhoton_norm (f : Lp ℂ 2 μ) (z : Sector μ 1) :
    ‖W.displacedOnePhoton μ f z‖ = ‖z‖ := by
  rw [displacedOnePhoton, (W.weyl f).norm_map, lp.norm_single (by norm_num)]

theorem displacedOnePhoton_continuous :
    Continuous (fun p : Lp ℂ 2 μ × Sector μ 1 => W.displacedOnePhoton μ p.1 p.2) :=
  W.continuous.comp (continuous_fst.prodMk
    ((lp.singleContinuousLinearMap ℂ (Sector μ) 2 1).continuous.comp continuous_snd))

/-- Both the displacement and the auxiliary photon may vary. -/
def displacedOnePhotonDerivative (f : Lp ℂ 2 μ) (z : Sector μ 1)
    (h : Lp ℂ 2 μ) (dz : Sector μ 1) : Fock μ :=
  finiteWeylDerivative μ W.weyl 1 f (lp.single 2 1 z) h +
    W.weyl f (lp.single 2 1 dz)

theorem displacedOnePhoton_hasDerivAt {f : ℝ → Lp ℂ 2 μ} {z : ℝ → Sector μ 1}
    {df : Lp ℂ 2 μ} {dz : Sector μ 1} {t : ℝ}
    (hf : HasDerivAt f df t) (hz : HasDerivAt z dz t) :
    HasDerivAt (fun s => W.displacedOnePhoton μ (f s) (z s))
      (W.displacedOnePhotonDerivative μ (f t) (z t) df dz) t :=
  W.hasDerivAt_apply μ hf
    (((lp.singleContinuousLinearMap ℂ (Sector μ) 2 1).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hz)
    1 (finiteNumberSupport_onePhoton μ (z t))

theorem displacedOnePhotonDerivative_eq (f h : Lp ℂ 2 μ) (z dz : Sector μ 1)
    (hreal : (⟪f, h⟫_ℂ).im = 0) (horth : annihilationSector μ 0 h z = 0) :
    W.displacedOnePhotonDerivative μ f z h dz = W.weyl f
      (lp.single 2 2 (creationSector μ 1 h z) + lp.single 2 1 dz) := by
  rw [displacedOnePhotonDerivative, finiteWeylDerivative_apply,
    creationFinite_single μ 1 1 le_rfl,
    annihilationFinite_single μ 1 0 (by decide), horth, lp.single_zero,
    sub_zero, hreal, Complex.ofReal_zero, mul_zero, zero_smul, add_zero,
    ← map_add]

theorem displacedOnePhoton_connection (f h : Lp ℂ 2 μ) (z dz : Sector μ 1)
    (hreal : (⟪f, h⟫_ℂ).im = 0) (horth : annihilationSector μ 0 h z = 0) :
    ⟪W.displacedOnePhoton μ f z, W.displacedOnePhotonDerivative μ f z h dz⟫_ℂ =
      ⟪z, dz⟫_ℂ := by
  rw [displacedOnePhoton, displacedOnePhotonDerivative_eq μ W f h z dz hreal horth,
    (W.weyl f).inner_map_map, inner_add_right, lp.inner_single_left,
    lp.single_apply_ne _ _ _ (by decide : (1 : ℕ) ≠ 2), inner_zero_right,
    zero_add, lp.inner_single_left, lp.single_apply_self]

theorem displacedOnePhoton_metric (C : CanonicalSectorCCR μ)
    (f h : Lp ℂ 2 μ) (z dz : Sector μ 1)
    (hreal : (⟪f, h⟫_ℂ).im = 0) (horth : annihilationSector μ 0 h z = 0) :
    ‖W.displacedOnePhotonDerivative μ f z h dz‖ ^ 2 =
      ‖h‖ ^ 2 * ‖z‖ ^ 2 + ‖dz‖ ^ 2 := by
  rw [displacedOnePhotonDerivative_eq μ W f h z dz hreal horth,
    (W.weyl f).norm_map,
    norm_add_pow_two_of_inner_eq_zero _ _ (by
      rw [lp.inner_single_left,
        lp.single_apply_ne _ _ _ (by decide : (2 : ℕ) ≠ 1), inner_zero_right]),
    lp.norm_single (by norm_num), lp.norm_single (by norm_num), C.successor h 0 z,
    horth, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add]

/-- Radiation calculations use the exact shifted annihilation form. -/
theorem displacedOnePhoton_annihilationForm (f g : Lp ℂ 2 μ) (z : Sector μ 1) :
    annihilationForm μ g (W.displacedOnePhoton μ f z) =
      annihilationForm μ g (lp.single 2 1 z) +
        ENNReal.ofReal (‖⟪g, f⟫_ℂ‖ ^ 2) * ENNReal.ofReal (‖z‖ ^ 2) := by
  have hg := W.annihilation_shift f g _ _ (onePhoton_annihilationGraph μ g z)
  change AnnihilationGraph μ g (W.displacedOnePhoton μ f z)
    (W.weyl f (lp.single 2 0 (annihilationSector μ 0 g z) +
      ⟪g, f⟫_ℂ • lp.single 2 1 z)) at hg
  rw [hg.form_eq μ, (W.weyl f).norm_map,
    norm_add_pow_two_of_inner_eq_zero _ _ (by
      rw [inner_smul_right, onePhoton_annihilation_inner, mul_zero]),
    ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
    ← (onePhoton_annihilationGraph μ g z).form_eq μ,
    norm_smul, mul_pow, lp.norm_single (by norm_num),
    ENNReal.ofReal_mul (sq_nonneg _)]

end ConcreteWeylLaw

section PhysicalField

variable (W : ConcreteWeylLaw photonMeasure)

/-- A concrete field graph on the displaced one-photon vector. -/
theorem displacedOnePhoton_field_graph (f g : Lp ℂ 2 photonMeasure)
    (z : Sector photonMeasure 1) :
    SegalGraph photonMeasure g (W.displacedOnePhoton photonMeasure f z)
      (W.weyl f (OnePhotonTag.fieldValue g z +
        ((2 * (⟪g, f⟫_ℂ).re : ℝ) : ℂ) • lp.single 2 1 z)) :=
  W.field_shift f g _ _ (OnePhotonTag.fieldValue_graph g z)

theorem displacedOnePhoton_field_expectation (f g : Lp ℂ 2 photonMeasure)
    (z : Sector photonMeasure 1) :
    ⟪W.displacedOnePhoton photonMeasure f z,
      W.weyl f (OnePhotonTag.fieldValue g z +
        ((2 * (⟪g, f⟫_ℂ).re : ℝ) : ℂ) • lp.single 2 1 z)⟫_ℂ =
      ((2 * (⟪g, f⟫_ℂ).re * ‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [ConcreteWeylLaw.displacedOnePhoton, (W.weyl f).inner_map_map,
    inner_add_right, OnePhotonTag.single_field_expectation_zero z g _
      (OnePhotonTag.fieldValue_graph g z), zero_add, inner_smul_right,
    inner_self_eq_norm_sq_to_K, lp.norm_single (by norm_num)]
  push_cast
  rfl

end PhysicalField
end GptLean.Representability
