import PfHk.KatoRellichBackground
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Finite-spin amplification of the retained ordinary operator theory. -/
noncomputable section
namespace PfHk.PauliMagneticOperatorRealization
open PfHk.KatoRellichBackground
open scoped InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

section Amplification
variable {S H : Type} [Fintype S] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def finiteGraph (G : H → H → Prop)
    (u v : PiLp 2 (fun _ : S => H)) : Prop := ∀ s, G (u s) (v s)

theorem finite_shift_surjective (G : H → H → Prop) (z : ℂ)
    (h : ShiftSurjective G z) : ShiftSurjective (finiteGraph (S := S) G) z := by
  intro f
  choose u v hv he using fun s : S => h (f s)
  refine ⟨WithLp.toLp 2 u, WithLp.toLp 2 v, hv, ?_⟩
  apply PiLp.ext
  intro s
  exact he s

/-- Finite Hilbert amplification preserves the ordinary self-adjoint
resolvent graph, proved coordinate by coordinate. -/
theorem finite_selfAdjoint (G : H → H → Prop) (hG : SelfAdjointGraph G) :
    SelfAdjointGraph (finiteGraph (S := S) G) where
  symmetric := by
    intro u v u' v' hv hv'
    simp only [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun s _ => hG.symmetric _ _ _ _ (hv s) (hv' s)
  dense := by
    have hd : Dense (Set.pi Set.univ (fun _ : S => {u : H | ∃ v, G u v})) :=
      dense_pi Set.univ (fun _ _ => hG.dense)
    apply (hd.preimage (PiLp.homeomorph 2 (fun _ : S => H)).isOpenMap).mono
    intro u hu
    have hcoord (s : S) : ∃ v, G (u s) v := hu s (Set.mem_univ s)
    choose v hv using hcoord
    exact ⟨WithLp.toLp 2 v, hv⟩
  positiveShift := finite_shift_surjective G Complex.I hG.positiveShift
  negativeShift := finite_shift_surjective G (-Complex.I) hG.negativeShift

end Amplification

end PfHk.PauliMagneticOperatorRealization
