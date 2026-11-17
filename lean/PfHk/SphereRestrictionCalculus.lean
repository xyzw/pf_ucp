import PfHk.PolarCalculusAlgebra

/-! First-order ordinary sphere restriction calculus for arbitrary
Hilbert-valued C1 functions. These facts do not involve physical fields. -/

noncomputable section
namespace PfHk.PolarCalculus

open MeasureTheory
open scoped InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000

variable {I : Type*} [Fintype I] [DecidableEq I]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem radialRestriction_sphereC1 (u : Position I → H) (hu : ContDiff ℝ (1 : ℕ∞) u) (r : ℝ) :
    SphereC1 (radialRestriction u r) := by
  have hnorm : ContDiffOn ℝ (1 : ℕ∞) (fun x : Position I => ‖x‖) ({0}ᶜ : Set (Position I)) :=
    contDiffOn_id.norm ℝ (fun x hx => by simpa using hx)
  have hinv := hnorm.inv (fun x hx => norm_ne_zero_iff.mpr (by simpa using hx))
  have harg : ContDiffOn ℝ (1 : ℕ∞) (fun x : Position I => r • (‖x‖⁻¹ • x))
      ({0}ᶜ : Set (Position I)) := by
    convert! (hinv.smul (contDiffOn_id : ContDiffOn ℝ (1 : ℕ∞)
      (fun x : Position I => x) ({0}ᶜ : Set (Position I)))).const_smul r using 1
  apply (hu.comp_contDiffOn harg).congr
  intro x hx
  have hx₀ : x ≠ 0 := by simpa using hx
  simp only [homogeneousExtension, hx₀, ↓reduceDIte, radialRestriction, direction]
  rfl

theorem sphereGradient_smul_unconditional (a : ℝ) (f : UnitSphere I → H) (j : I) (θ : UnitSphere I) :
    sphereGradient (fun η => a • f η) j θ = a • sphereGradient f j θ := by
  unfold sphereGradient
  rw [homogeneousExtension_smul]
  change fderiv ℝ (a • homogeneousExtension f) θ.val (EuclideanSpace.single j 1) = _
  rw [fderiv_const_smul_field]
  rfl

theorem sphereGradient_radial_eq (P : StandardPolarCalculus I H)
    (u : Position I → H) (hu : ContDiff ℝ (1 : ℕ∞) u) {r : ℝ} (hr : 0 < r)
    (j : I) (θ : UnitSphere I) :
    sphereGradient (radialRestriction u r) j θ =
      r • fderiv ℝ u (r • θ.val) (EuclideanSpace.single j 1) -
        (r * θ.val j) • radialFirst u r θ := by
  have h := congrArg (fun v : H => r • v) (P.gradient_decomposition u hu r hr θ j)
  simp only [smul_add, smul_smul, mul_inv_cancel₀ hr.ne', one_smul] at h
  exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans h.symm)

theorem scaled_radial_sphereC1 (a : ℝ) (u : Position I → H)
    (hu : ContDiff ℝ (1 : ℕ∞) u) (r : ℝ) :
    SphereC1 (fun θ => a • u (r • θ.val)) := by
  unfold SphereC1
  rw [homogeneousExtension_smul]
  exact contDiffOn_const.smul (radialRestriction_sphereC1 u hu r)

theorem scaled_radial_gradient_continuous (P : StandardPolarCalculus I H)
    (u : Position I → H) (hu : ContDiff ℝ (1 : ℕ∞) u)
    {a r : ℝ → ℝ} (ha : Continuous a) (hr : Continuous r) (hpos : ∀ t, 0 < r t) (j : I) :
    Continuous (fun p : ℝ × UnitSphere I =>
      sphereGradient (fun θ => a p.1 • u (r p.1 • θ.val)) j p.2) := by
  have hx : Continuous (fun p : ℝ × UnitSphere I => r p.1 • p.2.val) :=
    (hr.comp continuous_fst).smul (continuous_subtype_val.comp continuous_snd)
  have hdf := (hu.continuous_fderiv (by simp)).comp hx
  have hθ : Continuous (fun p : ℝ × UnitSphere I => p.2.val) :=
    continuous_subtype_val.comp continuous_snd
  have hθj : Continuous (fun p : ℝ × UnitSphere I => p.2.val j) :=
    (PiLp.continuous_apply 2 (fun _ : I => ℝ) j).comp hθ
  have he : (fun p : ℝ × UnitSphere I =>
      sphereGradient (fun θ => a p.1 • u (r p.1 • θ.val)) j p.2) =
      fun p => a p.1 • (r p.1 • fderiv ℝ u (r p.1 • p.2.val) (EuclideanSpace.single j 1) -
        (r p.1 * p.2.val j) • fderiv ℝ u (r p.1 • p.2.val) p.2.val) := by
    funext p
    rw [sphereGradient_smul_unconditional]
    change a p.1 • sphereGradient (radialRestriction u (r p.1)) j p.2 = _
    rw [sphereGradient_radial_eq P u hu (hpos p.1)]
    rfl
  rw [he]
  exact (ha.comp continuous_fst).smul
    (((hr.comp continuous_fst).smul (hdf.clm_apply continuous_const)).sub
      (((hr.comp continuous_fst).mul hθj).smul (hdf.clm_apply hθ)))

end PfHk.PolarCalculus
