import GptLean.PhysicalFreeReferenceCore
import GptLean.PhysicalCoulombBound
import GptLean.PhysicalFockSeparable
import GptLean.PhysicalPFReference

/-!
The physical Coulomb multiplication graph adds no further domain
restriction to the common electronic H1 and radiation reference.
The proved bounded Coulomb graph map gives a continuous linear
equivalence, transporting its smooth core and ambient L2 density.
-/

noncomputable section

namespace GptLean.PhysicalCoulombReferenceCore

open MeasureTheory PhysicalFock ElectronicH1Complex

set_option backward.isDefEq.respectTransparency.types false

private def tripleMapWithThird {Q E F G : Type*}
    [TopologicalSpace Q] [AddCommGroup Q] [Module ℂ Q]
    [TopologicalSpace E] [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℂ F]
    [TopologicalSpace G] [AddCommGroup G] [Module ℂ G]
    (a : Q →L[ℂ] E) (b : Q →L[ℂ] F) (p : E →L[ℂ] G) :
    Q →L[ℂ] E × F × G := a.prod (b.prod (p.comp a))

private theorem dense_image_of_surjective {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (f : X → Y) (hf : Continuous f) (hsurj : Function.Surjective f)
    {s : Set X} (hs : Dense s) : Dense (f '' s) := by
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  exact image_closure_subset_closure_image hf ⟨x, hs x, rfl⟩

abbrev Index (N : ℕ) := Fin N × Fin 3
abbrev Free (N : ℕ) := PhysicalFreeReferenceCore.FreeReference (Index N)
abbrev Reference (N : ℕ) (c : ℝ) :=
  PhysicalPFReference.Reference (Index N) (fun x => c * PhysicalCoulombH1.potential N x)

variable (N : ℕ) (c : ℝ) (hc : 0 ≤ c)

local instance radiationNormedSpace : NormedSpace ℂ RadiationGraphSpace :=
  radiationRoot.graph.normedSpace

local instance electronicNormedSpace : NormedSpace ℂ (ComplexH1 PhotonFock (Index N)) :=
  (complexWeakGraph PhotonFock (Index N)).normedSpace

local instance freeNormedSpace : NormedSpace ℂ (Free N) :=
  (PhysicalFreeReferenceCore.freeSubspace (Index N)).normedSpace

local instance potentialNormedSpace :
    NormedSpace ℂ (PhysicalPFReference.PotentialGraph (Index N)
      (fun x => c * PhysicalCoulombH1.potential N x)) :=
  (PhysicalMultiplicationGraph.graph volume (H := PhotonFock)
    (fun x => (Real.sqrt (c * PhysicalCoulombH1.potential N x) : ℂ))).normedSpace

theorem potentialGraphOperator_value (u : ComplexH1 PhotonFock (Index N)) :
    PhysicalMultiplicationGraph.inclusion volume _
      (PhysicalCoulombH1.potentialGraphOperator c hc u) = value u := rfl

set_option backward.isDefEq.respectTransparency.types true in
private def coulombOperator : PhysicalPFReference.ElectronicGraph (Index N) →L[ℂ]
    PhysicalPFReference.PotentialGraph (Index N) (fun x => c * PhysicalCoulombH1.potential N x) where
  toFun u := PhysicalCoulombH1.potentialGraphOperator c hc u
  map_add' u v := by
    apply PhysicalMultiplicationGraph.inclusion_injective volume _
    change value (u + v) = value u + value v
    exact map_add value u v
  map_smul' a u := by
    apply PhysicalMultiplicationGraph.inclusion_injective volume _
    change value (a • u) = a • value u
    exact map_smul value a u
  cont := (PhysicalCoulombH1.potentialGraphOperator (N := N) (H := PhotonFock) c hc).continuous

set_option backward.isDefEq.respectTransparency.types true in
private def attachAmbient :=
  tripleMapWithThird
    (Q := Free N) (E := PhysicalPFReference.ElectronicGraph (Index N))
    (F := PhysicalPFReference.RadiationGraph (Index N))
    (G := PhysicalPFReference.PotentialGraph (Index N)
      (fun x => c * PhysicalCoulombH1.potential N x))
    (PhysicalFreeReferenceCore.electronic (Index N))
    (PhysicalFreeReferenceCore.radiationSource (Index N))
    (coulombOperator N c hc)

set_option backward.isDefEq.respectTransparency.types true in
def attach : Free N →L[ℂ] Reference N c :=
  (attachAmbient N c hc).codRestrict
    (PhysicalPFReference.referenceSubspace (Index N)
      (fun x => c * PhysicalCoulombH1.potential N x)) (by
        intro q
        change (value (PhysicalFreeReferenceCore.electronic (Index N) q) -
            radiationGraphInclusion.compLpL 2 volume
              (PhysicalFreeReferenceCore.radiationSource (Index N) q),
          value (PhysicalFreeReferenceCore.electronic (Index N) q) -
            PhysicalMultiplicationGraph.inclusion volume _
              (PhysicalCoulombH1.potentialGraphOperator c hc
                (PhysicalFreeReferenceCore.electronic (Index N) q))) = (0, 0)
        exact Prod.ext
          (sub_eq_zero.mpr (PhysicalFreeReferenceCore.value_matching (Index N) q))
          (sub_eq_zero.mpr (potentialGraphOperator_value N c hc
            (PhysicalFreeReferenceCore.electronic (Index N) q)).symm))

def forget : Reference N c →L[ℂ] Free N :=
  ((PhysicalPFReference.electronic (Index N)
    (fun x => c * PhysicalCoulombH1.potential N x)).prod
    (PhysicalPFReference.radiationSource (Index N)
      (fun x => c * PhysicalCoulombH1.potential N x))).codRestrict
    (PhysicalFreeReferenceCore.freeSubspace (Index N)) (by
      intro q
      change PhysicalPFReference.inclusion (Index N)
          (fun x => c * PhysicalCoulombH1.potential N x) q -
        spatialRadiationInclusion volume (PhysicalPFReference.radiationSource (Index N)
          (fun x => c * PhysicalCoulombH1.potential N x) q) = 0
      exact sub_eq_zero.mpr (PhysicalPFReference.radiation_matches _ _ q).symm)

theorem forget_attach (q : Free N) : forget N c (attach N c hc q) = q := by
  apply Subtype.ext
  rfl

theorem attach_forget (q : Reference N c) : attach N c hc (forget N c q) = q := by
  apply PhysicalPFReference.inclusion_injective (Index N)
    (fun x => c * PhysicalCoulombH1.potential N x)
  rfl

/-- The full Coulomb reference and the free common graph have equivalent norms. -/
def referenceEquiv : Free N ≃L[ℂ] Reference N c where
  toFun := attach N c hc
  invFun := forget N c
  left_inv := forget_attach N c hc
  right_inv := attach_forget N c hc
  map_add' := map_add (attach N c hc)
  map_smul' a q := (attach N c hc).map_smul' a q
  continuous_toFun := (attach N c hc).continuous
  continuous_invFun := (forget N c).continuous

@[simp] theorem inclusion_referenceEquiv (q : Free N) :
    PhysicalPFReference.inclusion (Index N) (fun x => c * PhysicalCoulombH1.potential N x)
      (referenceEquiv N c hc q) = PhysicalFreeReferenceCore.inclusion (Index N) q := rfl

def smoothCore : Set (Reference N c) :=
  (referenceEquiv N c hc) '' PhysicalFreeReferenceCore.smoothCore (Index N)

set_option backward.isDefEq.respectTransparency.types true in
theorem dense_smoothCore : Dense (smoothCore N c hc) := by
  apply dense_image_of_surjective (X := Free N) (Y := Reference N c)
    (referenceEquiv N c hc) (referenceEquiv N c hc).continuous (referenceEquiv N c hc).surjective
  exact PhysicalFreeReferenceCore.dense_smoothCore (Index N)

include hc in
/-- The concrete Coulomb form reference is dense in the spatial Fock Hilbert space. -/
theorem inclusion_denseRange :
    DenseRange (PhysicalPFReference.inclusion (Index N)
      (fun x => c * PhysicalCoulombH1.potential N x)) := by
  apply (PhysicalFreeReferenceCore.inclusion_denseRange (Index N)).mono
  rintro u ⟨q, rfl⟩
  exact ⟨referenceEquiv N c hc q, rfl⟩

end GptLean.PhysicalCoulombReferenceCore
