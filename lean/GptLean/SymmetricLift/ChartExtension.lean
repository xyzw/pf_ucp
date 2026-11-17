import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Algebra.Group.Subgroup.Basic
import GptLean.SymmetricLift.Geometry

/-!
The orbit-chart extension in Step 2 of the symmetric-tensor appendix.

The extension below is constructed by choosing an orbit translate containing
the point. Stabilizer covariance proves that this choice is immaterial. The
resulting map is genuinely smooth as a continuous-linear-map-valued function
on the open orbit union. No global equivariant extension is assumed.
-/

noncomputable section

namespace GptLean.SymmetricLift

open scoped ContDiff Topology

open Set

variable {G X H K : Type*} [Group G]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- Linear actions on the configuration space and unitary actions on tensors. -/
structure ChartRepresentation (G X H : Type*) [Group G]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  base : G →* (X ≃L[ℝ] X)
  fiber : G →* (H ≃ₗᵢ[ℂ] H)

namespace ChartRepresentation

variable (A : ChartRepresentation G X H)

@[simp] theorem base_mul_apply (g h : G) (x : X) :
    A.base (g * h) x = A.base g (A.base h x) := by rw [map_mul]; rfl

@[simp] theorem base_one_apply (x : X) : A.base 1 x = x := by rw [map_one]; rfl

@[simp] theorem fiber_mul_apply (g h : G) (u : H) :
    A.fiber (g * h) u = A.fiber g (A.fiber h u) := by rw [map_mul]; rfl

@[simp] theorem fiber_one_apply (u : H) : A.fiber 1 u = u := by rw [map_one]; rfl

theorem base_comp_cancel (g h : G) (x : X) :
    A.base (g⁻¹ * h) (A.base h⁻¹ x) = A.base g⁻¹ x := by
  rw [← base_mul_apply, mul_assoc, mul_inv_cancel, mul_one]

theorem fiber_comp_cancel (g h : G) (u : H) :
    A.fiber (g⁻¹ * h) (A.fiber h⁻¹ u) = A.fiber g⁻¹ u := by
  rw [← fiber_mul_apply, mul_assoc, mul_inv_cancel, mul_one]

/-- The configuration stabilizer is a subgroup, with no chosen block labels. -/
def baseStabilizer (c : X) : Subgroup G where
  carrier := {g | A.base g c = c}
  one_mem' := A.base_one_apply c
  mul_mem' := by
    intro g h hg hh
    change A.base (g * h) c = c
    rw [A.base_mul_apply, hh, hg]
  inv_mem' := by
    intro g hg
    change A.base g⁻¹ c = c
    have he := congrArg (A.base g⁻¹) hg
    rw [← A.base_mul_apply, inv_mul_cancel, A.base_one_apply] at he
    exact he.symm

/-- The chart-separation hypothesis used below follows from the finite orbit
geometry for any finite isometric action. -/
theorem exists_stabilizer_separated_ball [Fintype G] (c : X)
    (hiso : ∀ g, Isometry (A.base g)) :
    ∃ r : ℝ, 0 < r ∧ ∀ g h x,
      A.base g⁻¹ x ∈ Metric.ball c r → A.base h⁻¹ x ∈ Metric.ball c r →
      g⁻¹ * h ∈ A.baseStabilizer c := by
  obtain ⟨r, hr, hsep⟩ := finite_orbit_balls (fun g : G => A.base g c)
  refine ⟨r, hr, ?_⟩
  intro g h x hg hh
  have hg' : x ∈ Metric.ball (A.base g c) r := by
    have he := (hiso g).dist_eq (A.base g⁻¹ x) c
    rw [← A.base_mul_apply, mul_inv_cancel, A.base_one_apply] at he
    change dist x (A.base g c) < r
    rw [he]
    exact hg
  have hh' : x ∈ Metric.ball (A.base h c) r := by
    have he := (hiso h).dist_eq (A.base h⁻¹ x) c
    rw [← A.base_mul_apply, mul_inv_cancel, A.base_one_apply] at he
    change dist x (A.base h c) < r
    rw [he]
    exact hh
  rcases hsep g h with he | hd
  · change A.base (g⁻¹ * h) c = c
    rw [A.base_mul_apply, ← he, ← A.base_mul_apply, inv_mul_cancel, A.base_one_apply]
  · exact False.elim (Set.disjoint_left.mp hd hg' hh')

/-- The union of all translates of one chart. -/
def orbitDomain (O : Set X) : Set X := {x | ∃ g : G, A.base g⁻¹ x ∈ O}

theorem orbitDomain_isOpen {O : Set X} (hO : IsOpen O) : IsOpen (A.orbitDomain O) := by
  have hset : A.orbitDomain O = ⋃ g : G, (A.base g⁻¹) ⁻¹' O := by
    ext x
    simp [orbitDomain]
  rw [hset]
  exact isOpen_iUnion fun g => hO.preimage (A.base g⁻¹).continuous

/-- The local formula on a specified translate. -/
def chartBranch (V : X → H →L[ℂ] K) (g : G) (x : X) : H →L[ℂ] K :=
  (V (A.base g⁻¹ x)).comp (A.fiber g⁻¹).toLinearIsometry.toContinuousLinearMap

/-- Stabilizer covariance resolves the permutation ambiguity on overlapping translates. -/
theorem chartBranch_eq (O : Set X) (S : Subgroup G) (V : X → H →L[ℂ] K)
    (hseparate : ∀ g h x, A.base g⁻¹ x ∈ O → A.base h⁻¹ x ∈ O → g⁻¹ * h ∈ S)
    (hlocal : ∀ s ∈ S, ∀ y ∈ O, ∀ u, V (A.base s y) (A.fiber s u) = V y u)
    {g h : G} {x : X} (hg : A.base g⁻¹ x ∈ O) (hh : A.base h⁻¹ x ∈ O) :
    A.chartBranch V g x = A.chartBranch V h x := by
  ext u
  have he := hlocal (g⁻¹ * h) (hseparate g h x hg hh) (A.base h⁻¹ x) hh
    (A.fiber h⁻¹ u)
  simpa only [chartBranch, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry, A.base_comp_cancel,
    A.fiber_comp_cancel] using he

/-- An actual globally defined extension, zero off the orbit domain. -/
def chartExtension (O : Set X) (V : X → H →L[ℂ] K) (x : X) : H →L[ℂ] K :=
  by
    classical
    exact if hx : x ∈ A.orbitDomain O then A.chartBranch V (Classical.choose hx) x else 0

theorem chartExtension_eq_branch (O : Set X) (S : Subgroup G) (V : X → H →L[ℂ] K)
    (hseparate : ∀ g h x, A.base g⁻¹ x ∈ O → A.base h⁻¹ x ∈ O → g⁻¹ * h ∈ S)
    (hlocal : ∀ s ∈ S, ∀ y ∈ O, ∀ u, V (A.base s y) (A.fiber s u) = V y u)
    {g : G} {x : X} (hx : A.base g⁻¹ x ∈ O) :
    A.chartExtension O V x = A.chartBranch V g x := by
  have hmem : x ∈ A.orbitDomain O := ⟨g, hx⟩
  rw [chartExtension, dite_eq_left hmem]
  exact A.chartBranch_eq O S V hseparate hlocal (Classical.choose_spec hmem) hx

theorem chartExtension_eq_local (O : Set X) (S : Subgroup G) (V : X → H →L[ℂ] K)
    (hseparate : ∀ g h x, A.base g⁻¹ x ∈ O → A.base h⁻¹ x ∈ O → g⁻¹ * h ∈ S)
    (hlocal : ∀ s ∈ S, ∀ y ∈ O, ∀ u, V (A.base s y) (A.fiber s u) = V y u)
    {x : X} (hx : x ∈ O) : A.chartExtension O V x = V x := by
  have hx' : A.base (1 : G)⁻¹ x ∈ O := by simpa only [inv_one, A.base_one_apply] using hx
  rw [A.chartExtension_eq_branch O S V hseparate hlocal hx']
  ext u
  simp only [chartBranch, ContinuousLinearMap.comp_apply, inv_one, A.base_one_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    A.fiber_one_apply]

theorem chartExtension_norm (O : Set X) (S : Subgroup G) (V : X → H →L[ℂ] K)
    (hseparate : ∀ g h x, A.base g⁻¹ x ∈ O → A.base h⁻¹ x ∈ O → g⁻¹ * h ∈ S)
    (hlocal : ∀ s ∈ S, ∀ y ∈ O, ∀ u, V (A.base s y) (A.fiber s u) = V y u)
    (hiso : ∀ y ∈ O, ∀ u, ‖V y u‖ = ‖u‖)
    {x : X} (hx : x ∈ A.orbitDomain O) (u : H) :
    ‖A.chartExtension O V x u‖ = ‖u‖ := by
  obtain ⟨g, hg⟩ := hx
  rw [A.chartExtension_eq_branch O S V hseparate hlocal hg]
  simp only [chartBranch, ContinuousLinearMap.comp_apply]
  rw [hiso _ hg]
  exact (A.fiber g⁻¹).norm_map u

theorem chartExtension_equivariant (O : Set X) (S : Subgroup G) (V : X → H →L[ℂ] K)
    (hseparate : ∀ g h x, A.base g⁻¹ x ∈ O → A.base h⁻¹ x ∈ O → g⁻¹ * h ∈ S)
    (hlocal : ∀ s ∈ S, ∀ y ∈ O, ∀ u, V (A.base s y) (A.fiber s u) = V y u)
    {x : X} (hx : x ∈ A.orbitDomain O) (h : G) (u : H) :
    A.chartExtension O V (A.base h x) (A.fiber h u) = A.chartExtension O V x u := by
  obtain ⟨g, hg⟩ := hx
  have hb : A.base (h * g)⁻¹ (A.base h x) = A.base g⁻¹ x := by
    rw [← A.base_mul_apply, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
  have hf : A.fiber (h * g)⁻¹ (A.fiber h u) = A.fiber g⁻¹ u := by
    rw [← A.fiber_mul_apply, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
  have hgh : A.base (h * g)⁻¹ (A.base h x) ∈ O := by rw [hb]; exact hg
  rw [A.chartExtension_eq_branch O S V hseparate hlocal hgh,
    A.chartExtension_eq_branch O S V hseparate hlocal hg]
  simp only [chartBranch, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry, hb, hf]

theorem chartExtension_fixed (O : Set X) (S : Subgroup G) (V : X → H →L[ℂ] K)
    (hseparate : ∀ g h x, A.base g⁻¹ x ∈ O → A.base h⁻¹ x ∈ O → g⁻¹ * h ∈ S)
    (hlocal : ∀ s ∈ S, ∀ y ∈ O, ∀ u, V (A.base s y) (A.fiber s u) = V y u)
    (P : H →L[ℂ] H) (C : H →L[ℂ] K)
    (hP : ∀ g u, A.fiber g (P u) = P u)
    (hfixed : ∀ y ∈ O, ∀ u, V y (P u) = C u)
    {x : X} (hx : x ∈ A.orbitDomain O) (u : H) :
    A.chartExtension O V x (P u) = C u := by
  obtain ⟨g, hg⟩ := hx
  rw [A.chartExtension_eq_branch O S V hseparate hlocal hg]
  simp only [chartBranch, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry, hP]
  exact hfixed _ hg u

section Smooth

variable [NormedSpace ℝ K] [IsScalarTower ℝ ℂ K]

/-- Composition with a fixed tensor permutation is a bounded real-linear operation. -/
def branchPostcompose (g : G) : (H →L[ℂ] K) →L[ℝ] (H →L[ℂ] K) :=
  ((ContinuousLinearMap.compL ℂ H H K).flip
    (A.fiber g⁻¹).toLinearIsometry.toContinuousLinearMap).restrictScalars ℝ

theorem chartBranch_contDiffOn (O : Set X) (V : X → H →L[ℂ] K)
    (hV : ContDiffOn ℝ ∞ V O) (g : G) :
    ContDiffOn ℝ ∞ (A.chartBranch V g) ((A.base g⁻¹) ⁻¹' O) := by
  exact (A.branchPostcompose (K := K) g).contDiff.comp_contDiffOn
    (hV.comp_continuousLinearMap (A.base g⁻¹).toContinuousLinearMap)

/-- Smoothness is proved locally from the selected chart formula, including
points where the selected representative changes. -/
theorem chartExtension_contDiffOn (O : Set X) (S : Subgroup G) (V : X → H →L[ℂ] K)
    (hO : IsOpen O)
    (hseparate : ∀ g h x, A.base g⁻¹ x ∈ O → A.base h⁻¹ x ∈ O → g⁻¹ * h ∈ S)
    (hlocal : ∀ s ∈ S, ∀ y ∈ O, ∀ u, V (A.base s y) (A.fiber s u) = V y u)
    (hV : ContDiffOn ℝ ∞ V O) :
    ContDiffOn ℝ ∞ (A.chartExtension O V) (A.orbitDomain O) := by
  apply contDiffOn_of_locally_contDiffOn
  intro x hx
  obtain ⟨g, hg⟩ := hx
  refine ⟨(A.base g⁻¹) ⁻¹' O, hO.preimage (A.base g⁻¹).continuous, hg, ?_⟩
  apply (A.chartBranch_contDiffOn O V hV g).congr_mono
  · intro y hy
    exact A.chartExtension_eq_branch O S V hseparate hlocal hy.2
  · exact Set.inter_subset_right

/-- The branch derivative is computed using the two fixed linear actions. -/
def chartBranchDerivative (V : X → H →L[ℂ] K) (g : G) (x : X) :
    X →L[ℝ] (H →L[ℂ] K) :=
  (A.branchPostcompose g).comp
    ((fderiv ℝ V (A.base g⁻¹ x)).comp (A.base g⁻¹).toContinuousLinearMap)

theorem chartBranch_hasFDerivAt (V : X → H →L[ℂ] K) (g : G) (x : X)
    (hV : DifferentiableAt ℝ V (A.base g⁻¹ x)) :
    HasFDerivAt (A.chartBranch V g) (A.chartBranchDerivative V g x) x := by
  exact (A.branchPostcompose g).hasFDerivAt.comp x
    (hV.hasFDerivAt.comp x (A.base g⁻¹).toContinuousLinearMap.hasFDerivAt)

/-- The chosen extension has the derivative of any chart containing the point. -/
theorem chartExtension_hasFDerivAt (O : Set X) (S : Subgroup G) (V : X → H →L[ℂ] K)
    (hO : IsOpen O)
    (hseparate : ∀ g h x, A.base g⁻¹ x ∈ O → A.base h⁻¹ x ∈ O → g⁻¹ * h ∈ S)
    (hlocal : ∀ s ∈ S, ∀ y ∈ O, ∀ u, V (A.base s y) (A.fiber s u) = V y u)
    {g : G} {x : X} (hx : A.base g⁻¹ x ∈ O)
    (hV : DifferentiableAt ℝ V (A.base g⁻¹ x)) :
    HasFDerivAt (A.chartExtension O V) (A.chartBranchDerivative V g x) x := by
  apply (A.chartBranch_hasFDerivAt V g x hV).congr_of_eventuallyEq
  filter_upwards [(hO.preimage (A.base g⁻¹).continuous).mem_nhds hx] with y hy
  exact A.chartExtension_eq_branch O S V hseparate hlocal hy

/-- Flatness passes to the actual derivative of the orbit-chart extension. -/
theorem chartExtension_flat (O : Set X) (S : Subgroup G) (V : X → H →L[ℂ] K)
    (hO : IsOpen O)
    (hseparate : ∀ g h x, A.base g⁻¹ x ∈ O → A.base h⁻¹ x ∈ O → g⁻¹ * h ∈ S)
    (hlocal : ∀ s ∈ S, ∀ y ∈ O, ∀ u, V (A.base s y) (A.fiber s u) = V y u)
    (hV : DifferentiableOn ℝ V O)
    (hflat : ∀ y ∈ O, ∀ d u v, inner ℂ (V y u) (fderiv ℝ V y d v) = 0)
    {x : X} (hx : x ∈ A.orbitDomain O) (d : X) (u v : H) :
    inner ℂ (A.chartExtension O V x u)
      (fderiv ℝ (A.chartExtension O V) x d v) = 0 := by
  obtain ⟨g, hg⟩ := hx
  have hv := (hV _ hg).differentiableAt (hO.mem_nhds hg)
  rw [(A.chartExtension_hasFDerivAt O S V hO hseparate hlocal hg hv).fderiv,
    A.chartExtension_eq_branch O S V hseparate hlocal hg]
  exact hflat _ hg (A.base g⁻¹ d) (A.fiber g⁻¹ u) (A.fiber g⁻¹ v)

end Smooth

end ChartRepresentation

end GptLean.SymmetricLift
