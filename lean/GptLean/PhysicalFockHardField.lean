import GptLean.PhysicalFockSupportedSubspaces
import GptLean.PhysicalFockWordGram
import GptLean.PhysicalFockKernelField

/-!
Fields orthogonal to a one-photon subspace on its generated Fock space.
Finite-word contraction and closed kernels prove that annihilation vanishes.
The actual radiation-graph creation operator is orthogonal to that entire
Fock subspace and has exactly its vacuum fluctuation norm.
-/

noncomputable section

namespace GptLean.PhysicalFock

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

section Generated

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]
  (C : CanonicalSectorCCR μ) (V : Submodule ℂ (Lp ℂ 2 μ))

instance generatedCompleteSpace : CompleteSpace (generatedSubspace μ V) := by
  unfold generatedSubspace
  infer_instance

include C

omit C in
theorem generated_map_mem (L : Fock μ →L[ℂ] Fock μ)
    (hL : ∀ w : List (Lp ℂ 2 μ), (∀ g ∈ w, g ∈ V) →
      L (creationWord μ w) ∈ generatedSubspace μ V)
    (u : Fock μ) (hu : u ∈ generatedSubspace μ V) :
    L u ∈ generatedSubspace μ V := by
  have hs : Submodule.span ℂ {z | ∃ w : List (Lp ℂ 2 μ),
      (∀ g ∈ w, g ∈ V) ∧ z = creationWord μ w} ≤
      (generatedSubspace μ V).comap L.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w, hw, rfl⟩
    exact hL w hw
  exact (closure_minimal hs
    ((Submodule.isClosed_topologicalClosure _).preimage L.continuous)) hu

omit C in
theorem creationBlock_mem_generated (n : ℕ) (f : Lp ℂ 2 μ) (hf : f ∈ V)
    (u : Fock μ) (hu : u ∈ generatedSubspace μ V) :
    creationBlock μ n f u ∈ generatedSubspace μ V := by
  apply generated_map_mem μ V (creationBlock μ n f) _ u hu
  intro w hw
  by_cases hn : n = w.length
  · subst n
    change lp.single 2 (w.length + 1)
      (creationSector μ w.length f ((creationWord μ w) w.length)) ∈ _
    change lp.single 2 (w.length + 1)
      (creationSector μ w.length f ((lp.single 2 w.length (creationWordSector μ w)) w.length)) ∈ _
    rw [lp.single_apply_self]
    exact creationWord_mem_generated μ V (f :: w) (by
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact hf
      · exact hw g hg)
  · rw [show creationBlock μ n f (creationWord μ w) = 0 from
      creationBlock_single_ne μ n w.length hn f (creationWordSector μ w)]
    exact (generatedSubspace μ V).zero_mem

omit C in
theorem creationFinite_mem_generated (M : ℕ) (f : Lp ℂ 2 μ) (hf : f ∈ V)
    (u : Fock μ) (hu : u ∈ generatedSubspace μ V) :
    creationFinite μ M f u ∈ generatedSubspace μ V := by
  classical
  simp only [creationFinite, sum_apply]
  exact (generatedSubspace μ V).sum_mem fun n _ => creationBlock_mem_generated μ V n f hf u hu

omit C in
theorem wordContraction_mem_generated (f : Lp ℂ 2 μ)
    (w : List (Lp ℂ 2 μ)) (hw : ∀ g ∈ w, g ∈ V) :
    wordContraction μ f w ∈ generatedSubspace μ V := by
  induction w with
  | nil => exact (generatedSubspace μ V).zero_mem
  | cons g w ih =>
    rw [wordContraction_cons]
    have htail : ∀ h ∈ w, h ∈ V := fun h hh => hw h (List.mem_cons_of_mem g hh)
    exact (generatedSubspace μ V).add_mem
      ((generatedSubspace μ V).smul_mem _ (creationWord_mem_generated μ V w htail))
      (creationFinite_mem_generated μ V w.length g (hw g List.mem_cons_self) _ (ih htail))

theorem annihilationBlock_mem_generated (n : ℕ) (f : Lp ℂ 2 μ)
    (u : Fock μ) (hu : u ∈ generatedSubspace μ V) :
    annihilationBlock μ n f u ∈ generatedSubspace μ V := by
  apply generated_map_mem μ V (annihilationBlock μ n f) _ u hu
  intro w hw
  cases w with
  | nil =>
    rw [show annihilationBlock μ n f (creationWord μ []) = 0 from
      annihilationBlock_single_ne μ n 0 (by omega) f (vacuumSector μ)]
    exact (generatedSubspace μ V).zero_mem
  | cons g w =>
    by_cases hn : n = w.length
    · subst n
      have h := annihilationFinite_word μ C (w.length + 1) f (g :: w) le_rfl
      change annihilationFinite μ (w.length + 1) f
        (lp.single 2 (w.length + 1) (creationWordSector μ (g :: w))) = _ at h
      rw [annihilationFinite_single μ (w.length + 1) w.length (by omega)] at h
      have he := (annihilationBlock_single μ w.length f
        (creationWordSector μ (g :: w))).trans h
      exact he.symm ▸ wordContraction_mem_generated μ V f (g :: w) hw
    · rw [show annihilationBlock μ n f (creationWord μ (g :: w)) = 0 from
        annihilationBlock_single_ne μ n (w.length + 1) (by omega) f
          (creationWordSector μ (g :: w))]
      exact (generatedSubspace μ V).zero_mem

omit C in
theorem mem_generated_of_photonSector (u : Fock μ)
    (hu : ∀ n, photonSector μ n u ∈ generatedSubspace μ V) :
    u ∈ generatedSubspace μ V := by
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto (photonSector_hasSum μ u)
  exact Eventually.of_forall fun s => (generatedSubspace μ V).sum_mem fun n _ => hu n

omit C in
theorem wordContraction_eq_zero_of_orthogonal (f : Lp ℂ 2 μ) (hf : f ∈ Vᗮ)
    (w : List (Lp ℂ 2 μ)) (hw : ∀ g ∈ w, g ∈ V) : wordContraction μ f w = 0 := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    rw [wordContraction_cons, V.inner_left_of_mem_orthogonal
      (hw g (List.mem_cons_self)) hf,
      ih (fun h hh => hw h (List.mem_cons_of_mem g hh)), zero_smul, map_zero, add_zero]

theorem annihilationBlock_word_eq_zero (n : ℕ) (f : Lp ℂ 2 μ) (hf : f ∈ Vᗮ)
    (w : List (Lp ℂ 2 μ)) (hw : ∀ g ∈ w, g ∈ V) :
    annihilationBlock μ n f (creationWord μ w) = 0 := by
  classical
  cases w with
  | nil => exact annihilationBlock_single_ne μ n 0 (by omega) f (vacuumSector μ)
  | cons g w =>
    by_cases hn : n = w.length
    · subst n
      have h := (annihilationFinite_word μ C (w.length + 1) f (g :: w) le_rfl).trans
        (wordContraction_eq_zero_of_orthogonal μ V f hf (g :: w) hw)
      change annihilationFinite μ (w.length + 1) f
        (lp.single 2 (w.length + 1) (creationWordSector μ (g :: w))) = 0 at h
      rw [annihilationFinite_single μ (w.length + 1) w.length (by omega)] at h
      exact (annihilationBlock_single μ w.length f (creationWordSector μ (g :: w))).trans h
    · exact annihilationBlock_single_ne μ n (w.length + 1) (by omega) f
        (creationWordSector μ (g :: w))

/-- Each bounded annihilation block vanishes on the completed generated space. -/
theorem annihilationBlock_eq_zero_of_orthogonal (n : ℕ) (f : Lp ℂ 2 μ)
    (hf : f ∈ Vᗮ) (u : Fock μ) (hu : u ∈ generatedSubspace μ V) :
    annihilationBlock μ n f u = 0 := by
  have hs : Submodule.span ℂ {z | ∃ w : List (Lp ℂ 2 μ),
      (∀ g ∈ w, g ∈ V) ∧ z = creationWord μ w} ≤ (annihilationBlock μ n f).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w, hw, rfl⟩
    exact annihilationBlock_word_eq_zero μ C V n f hf w hw
  exact (closure_minimal hs (annihilationBlock μ n f).isClosed_ker) hu

theorem annihilationSector_eq_zero_of_orthogonal (n : ℕ) (f : Lp ℂ 2 μ)
    (hf : f ∈ Vᗮ) (u : Fock μ) (hu : u ∈ generatedSubspace μ V) :
    annihilationSector μ n f (u (n + 1)) = 0 := by
  have h := annihilationBlock_eq_zero_of_orthogonal μ C V n f hf u hu
  have hc := congrArg (fun v : Fock μ => v n) h
  change (lp.single 2 n (annihilationSector μ n f (u (n + 1)))) n = (0 : Fock μ) n at hc
  rw [lp.single_apply_self] at hc
  exact hc

end Generated

section Radiation

variable (C : CanonicalSectorCCR photonMeasure)
  (V : Submodule ℂ (Lp ℂ 2 photonMeasure))
  (k : WeightedPhotonKernel)

include C

theorem kernelAnnihilation_mem_generated (q : RadiationGraphSpace)
    (hq : radiationGraphInclusion q ∈ generatedFockSubspace V) :
    kernelAnnihilation k q ∈ generatedFockSubspace V := by
  apply mem_generated_of_photonSector photonMeasure V
  intro n
  exact annihilationBlock_mem_generated photonMeasure C V n k.val.1
    (radiationGraphInclusion q) hq

theorem kernelCreation_mem_generated (hk : k.val.1 ∈ V) (q : RadiationGraphSpace)
    (hq : radiationGraphInclusion q ∈ generatedFockSubspace V) :
    kernelCreation C k q ∈ generatedFockSubspace V := by
  apply mem_generated_of_photonSector photonMeasure V
  intro n
  cases n with
  | zero =>
    change lp.single 2 0 (0 : Sector photonMeasure 0) ∈ _
    rw [lp.single_zero]
    exact (generatedFockSubspace V).zero_mem
  | succ n =>
    exact creationBlock_mem_generated photonMeasure V n k.val.1 hk
      (radiationGraphInclusion q) hq

/-- The hard field acts on the same hard-generated fiber space. -/
theorem kernelField_mem_generated (hk : k.val.1 ∈ V) (q : RadiationGraphSpace)
    (hq : radiationGraphInclusion q ∈ generatedFockSubspace V) :
    kernelField C k q ∈ generatedFockSubspace V :=
  (generatedFockSubspace V).add_mem (kernelAnnihilation_mem_generated C V k q hq)
    (kernelCreation_mem_generated C V k hk q hq)

variable (hk : k.val.1 ∈ Vᗮ)

include hk

/-- The actual radiation-graph annihilation operator vanishes on hard vectors. -/
theorem kernelAnnihilation_eq_zero_of_orthogonal (q : RadiationGraphSpace)
    (hq : radiationGraphInclusion q ∈ generatedFockSubspace V) :
    kernelAnnihilation k q = 0 := by
  apply lp.ext
  funext n
  exact annihilationSector_eq_zero_of_orthogonal photonMeasure C V n k.val.1 hk
    (radiationGraphInclusion q) hq

/-- Soft creation is orthogonal to every vector in the hard generated space. -/
theorem kernelCreation_inner_eq_zero_of_orthogonal (q : RadiationGraphSpace)
    (v : PhotonFock) (hv : v ∈ generatedFockSubspace V) :
    ⟪v, kernelCreation C k q⟫_ℂ = 0 := by
  rw [lp.inner_eq_tsum]
  suffices hzero : ∀ n, ⟪v n, kernelCreation C k q n⟫_ℂ = 0 by
    simp only [hzero, tsum_zero]
  intro n
  cases n with
  | zero => exact inner_zero_right _
  | succ n =>
    change ⟪v (n + 1), creationSector photonMeasure n k.val.1
      (radiationGraphInclusion q n)⟫_ℂ = 0
    rw [← (creationSector photonMeasure n k.val.1).adjoint_inner_left]
    change ⟪annihilationSector photonMeasure n k.val.1 (v (n + 1)),
      radiationGraphInclusion q n⟫_ℂ = 0
    rw [annihilationSector_eq_zero_of_orthogonal photonMeasure C V n k.val.1 hk v hv,
      inner_zero_left]

theorem kernelField_eq_creation_of_orthogonal (q : RadiationGraphSpace)
    (hq : radiationGraphInclusion q ∈ generatedFockSubspace V) :
    kernelField C k q = kernelCreation C k q := by
  change kernelAnnihilation k q + kernelCreation C k q = _
  rw [kernelAnnihilation_eq_zero_of_orthogonal C V k hk q hq, zero_add]

omit C hk in
private theorem norm_sq_add_of_zero {H : Type*} [NormedAddCommGroup H]
    (v : H) (hv : v = 0) (a : ℝ) : ‖v‖ ^ 2 + a = a := by
  rw [hv, norm_zero]
  ring

/-- The added soft field has the exact vacuum variance on every hard vector. -/
theorem kernelField_norm_sq_of_orthogonal (q : RadiationGraphSpace)
    (hq : radiationGraphInclusion q ∈ generatedFockSubspace V) :
    ‖kernelField C k q‖ ^ 2 = ‖k.val.1‖ ^ 2 * ‖radiationGraphInclusion q‖ ^ 2 := by
  rw [kernelField_eq_creation_of_orthogonal C V k hk q hq]
  have h := creationRadiation_norm_sq C k.val.1 k.val.2 k.property q
  change ‖kernelCreation C k q‖ ^ 2 =
    ‖kernelAnnihilation k q‖ ^ 2 + ‖k.val.1‖ ^ 2 * ‖radiationGraphInclusion q‖ ^ 2 at h
  exact h.trans (norm_sq_add_of_zero (kernelAnnihilation k q)
    (kernelAnnihilation_eq_zero_of_orthogonal C V k hk q hq) _)

theorem kernelField_inner_eq_zero_of_orthogonal (q : RadiationGraphSpace)
    (hq : radiationGraphInclusion q ∈ generatedFockSubspace V)
    (v : PhotonFock) (hv : v ∈ generatedFockSubspace V) :
    ⟪v, kernelField C k q⟫_ℂ = 0 := by
  rw [kernelField_eq_creation_of_orthogonal C V k hk q hq]
  exact kernelCreation_inner_eq_zero_of_orthogonal C V k hk q v hv

end Radiation

end GptLean.PhysicalFock
