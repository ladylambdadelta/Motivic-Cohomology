import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.Owner

/-!
# Real symmetric PSD bilinear radical algebra

This file owns the generic algebraic reduction from zero self-pairing in a real
symmetric positive-semidefinite bilinear form to radical membership.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- In a real symmetric positive-semidefinite bilinear pairing, a vector with zero
self-pairing lies in the left radical.

This is the algebraic reduction that turns diagonal lower-weight nullity into cross-kernel
nullity.  The analytic work for the completed boundary pairing is to provide the bilinear,
symmetric, and positive-semidefinite laws for the concrete kernel. -/
theorem real_symmetric_bilinear_psd_left_radical_of_self_zero
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V → V → ℝ)
    (B_add_left : ∀ x y z : V, B (x + y) z = B x z + B y z)
    (B_smul_left : ∀ (a : ℝ) (x y : V), B (a • x) y = a * B x y)
    (B_add_right : ∀ x y z : V, B x (y + z) = B x y + B x z)
    (B_smul_right : ∀ (a : ℝ) (x y : V), B x (a • y) = a * B x y)
    (B_symm : ∀ x y : V, B x y = B y x)
    (B_psd : ∀ x : V, 0 ≤ B x x)
    {d t : V}
    (hdd : B d d = 0) :
    B d t = 0 := by
  by_cases htd : B t d = 0
  · exact (B_symm d t).trans htd
  · exfalso
    let b : ℝ := B t t
    let c : ℝ := B t d
    let r : ℝ := -((b + 1) / (2 * c))
    have hc : c ≠ 0 := htd
    have hpos : 0 ≤ B (t + r • d) (t + r • d) :=
      B_psd (t + r • d)
    have hcross : B d t = c := by
      exact B_symm d t
    have hexpand :
        B (t + r • d) (t + r • d) =
          b + 2 * r * c := by
      calc
        B (t + r • d) (t + r • d) =
            B t (t + r • d) + B (r • d) (t + r • d) := by
          exact B_add_left t (r • d) (t + r • d)
        _ =
            (B t t + B t (r • d)) +
              (B (r • d) t + B (r • d) (r • d)) := by
          exact congrArg₂ HAdd.hAdd
            (B_add_right t t (r • d))
            (B_add_right (r • d) t (r • d))
        _ =
            (b + r * c) + (r * c + r * (r * 0)) := by
          exact congrArg₂ HAdd.hAdd
            (congrArg₂ HAdd.hAdd rfl (B_smul_right r t d))
            ((congrArg₂ HAdd.hAdd
              (B_smul_left r d t)
              ((B_smul_left r d (r • d)).trans
                (congrArg (fun x : ℝ => r * x)
                  ((B_smul_right r d d).trans
                    (congrArg (fun x : ℝ => r * x) hdd))))).trans
              (congrArg₂ HAdd.hAdd
                (congrArg (fun x : ℝ => r * x) hcross)
                rfl))
        _ = b + 2 * r * c := by
          ring
    have hr : b + 2 * r * c = -1 := by
      unfold r
      field_simp [hc]
      ring
    rw [hexpand, hr] at hpos
    linarith

/-- In a real symmetric positive-semidefinite bilinear pairing, a vector with zero
self-pairing lies in the right radical. -/
theorem real_symmetric_bilinear_psd_right_radical_of_self_zero
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V → V → ℝ)
    (B_add_left : ∀ x y z : V, B (x + y) z = B x z + B y z)
    (B_smul_left : ∀ (a : ℝ) (x y : V), B (a • x) y = a * B x y)
    (B_add_right : ∀ x y z : V, B x (y + z) = B x y + B x z)
    (B_smul_right : ∀ (a : ℝ) (x y : V), B x (a • y) = a * B x y)
    (B_symm : ∀ x y : V, B x y = B y x)
    (B_psd : ∀ x : V, 0 ≤ B x x)
    {d t : V}
    (hdd : B d d = 0) :
    B t d = 0 := by
  have hleft :
      B d t = 0 :=
    real_symmetric_bilinear_psd_left_radical_of_self_zero
      B B_add_left B_smul_left B_add_right B_smul_right B_symm B_psd hdd
  exact (B_symm t d).trans hleft

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
