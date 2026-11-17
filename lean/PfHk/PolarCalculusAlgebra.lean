import PfHk.PolarCalculus

/-! Linearity of the actual homogeneous extension and sphere gradient. -/

noncomputable section
namespace PfHk.PolarCalculus

open MeasureTheory
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
variable {I H : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem homogeneousExtension_add (f g : UnitSphere I → H) :
    homogeneousExtension (fun θ => f θ + g θ) =
      fun x => homogeneousExtension f x + homogeneousExtension g x := by
  funext x
  unfold homogeneousExtension
  split_ifs <;> simp

theorem homogeneousExtension_smul (a : ℝ) (f : UnitSphere I → H) :
    homogeneousExtension (fun θ => a • f θ) = fun x => a • homogeneousExtension f x := by
  funext x
  unfold homogeneousExtension
  split_ifs <;> simp

theorem SphereC1.add {f g : UnitSphere I → H} (hf : SphereC1 f) (hg : SphereC1 g) :
    SphereC1 (fun θ => f θ + g θ) := by
  unfold SphereC1 at *
  rw [homogeneousExtension_add]
  exact hf.add hg

theorem SphereC1.smul {f : UnitSphere I → H} (hf : SphereC1 f) (a : ℝ) :
    SphereC1 (fun θ => a • f θ) := by
  unfold SphereC1 at *
  rw [homogeneousExtension_smul]
  exact hf.const_smul a

theorem SphereC1.differentiableAt {f : UnitSphere I → H} (hf : SphereC1 f)
    (θ : UnitSphere I) : DifferentiableAt ℝ (homogeneousExtension f) θ.val := by
  have hθ : θ.val ∈ ({0}ᶜ : Set (Position I)) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have hn := unitSphere_norm I θ
    rw [h, norm_zero] at hn
    norm_num at hn
  exact (hf.differentiableOn_one θ.val hθ).differentiableAt
    (isOpen_compl_singleton.mem_nhds hθ)

theorem sphereGradient_add {f g : UnitSphere I → H} (hf : SphereC1 f) (hg : SphereC1 g)
    (j : I) (θ : UnitSphere I) :
    sphereGradient (fun x => f x + g x) j θ = sphereGradient f j θ + sphereGradient g j θ := by
  unfold sphereGradient
  rw [homogeneousExtension_add, fderiv_fun_add (hf.differentiableAt θ) (hg.differentiableAt θ)]
  rfl

theorem sphereGradient_smul {f : UnitSphere I → H} (hf : SphereC1 f) (a : ℝ)
    (j : I) (θ : UnitSphere I) :
    sphereGradient (fun x => a • f x) j θ = a • sphereGradient f j θ := by
  unfold sphereGradient
  rw [homogeneousExtension_smul, fderiv_fun_const_smul (hf.differentiableAt θ)]
  rfl

end PfHk.PolarCalculus
