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
  match Decidable.em (B t d = 0) with
  | Or.inl htd => exact (B_symm d t).trans htd
  | Or.inr htd =>
    let b : ℝ := B t t
    let c : ℝ := B t d
    let r : ℝ := -((b + 1) / (2 * c))
    have hc : c ≠ 0 := htd
    have hpos : 0 ≤ B (t + r • d) (t + r • d) :=
      B_psd (t + r • d)
    have hcross : B d t = c := by
      exact B_symm d t
    have hquadratic_arithmetic :
        (b + r * c) + (r * c + r * (r * 0)) = b + 2 * r * c := by
      have hzero_term : r * (r * 0) = 0 := by
        calc
          r * (r * 0) = r * 0 := by
            exact congrArg (fun x : ℝ => r * x) (mul_zero r)
          _ = 0 := mul_zero r
      have hdouble :
          r * c + r * c = 2 * r * c := by
        calc
          r * c + r * c = 2 * (r * c) := (two_mul (r * c)).symm
          _ = 2 * r * c := (mul_assoc 2 r c).symm
      calc
        (b + r * c) + (r * c + r * (r * 0))
            = (b + r * c) + (r * c + 0) := by
              exact congrArg
                (fun x : ℝ => (b + r * c) + (r * c + x))
                hzero_term
        _ = (b + r * c) + r * c := by
          exact congrArg (fun x : ℝ => (b + r * c) + x) (add_zero (r * c))
        _ = b + (r * c + r * c) := by
          exact add_assoc b (r * c) (r * c)
        _ = b + 2 * r * c := by
          exact congrArg (fun x : ℝ => b + x) hdouble
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
        _ = b + 2 * r * c := hquadratic_arithmetic
    have hr : b + 2 * r * c = -1 := by
      change b + 2 * (-((b + 1) / (2 * c))) * c = -1
      have htwo_c_ne : 2 * c ≠ 0 := by
        exact mul_ne_zero two_ne_zero hc
      have htwo_c_cancel : (2 * c)⁻¹ * (2 * c) = 1 :=
        inv_mul_cancel₀ htwo_c_ne
      have hneg_cancel :
          -((b + 1) / (2 * c)) * (2 * c) = -(b + 1) := by
        calc
          -((b + 1) / (2 * c)) * (2 * c)
              = -(((b + 1) / (2 * c)) * (2 * c)) := by
                exact neg_mul ((b + 1) / (2 * c)) (2 * c)
          _ = -(((b + 1) * (2 * c)⁻¹) * (2 * c)) := by
            exact congrArg Neg.neg
              (congrArg (fun x : ℝ => x * (2 * c))
                (div_eq_mul_inv (b + 1) (2 * c)))
          _ = -((b + 1) * ((2 * c)⁻¹ * (2 * c))) := by
            exact congrArg Neg.neg (mul_assoc (b + 1) (2 * c)⁻¹ (2 * c))
          _ = -((b + 1) * 1) := by
            exact congrArg (fun x : ℝ => -((b + 1) * x)) htwo_c_cancel
          _ = -(b + 1) := by
            exact congrArg Neg.neg (mul_one (b + 1))
      have hmiddle :
          2 * (-((b + 1) / (2 * c))) * c = -(b + 1) := by
        have hcomm :
            2 * (-((b + 1) / (2 * c))) =
              -((b + 1) / (2 * c)) * 2 := by
          exact mul_comm 2 (-((b + 1) / (2 * c)))
        calc
          2 * (-((b + 1) / (2 * c))) * c =
              (-((b + 1) / (2 * c)) * 2) * c := by
                exact congrArg (fun x : ℝ => x * c) hcomm
          _ = -((b + 1) / (2 * c)) * (2 * c) := by
            exact mul_assoc (-((b + 1) / (2 * c))) 2 c
          _ = -(b + 1) := hneg_cancel
      calc
        b + 2 * (-((b + 1) / (2 * c))) * c
            = b + (-(b + 1)) := by
              exact congrArg (fun x : ℝ => b + x) hmiddle
        _ = b + (-b + -1) := by
          exact congrArg (fun x : ℝ => b + x) (neg_add b 1)
        _ = (b + -b) + -1 := (add_assoc b (-b) (-1)).symm
        _ = 0 + -1 := by
          exact congrArg (fun x : ℝ => x + -1) (add_neg_cancel b)
        _ = -1 := zero_add (-1)
    have hnegative :
        B (t + r • d) (t + r • d) = -1 :=
      Eq.trans hexpand hr
    have hnonnegative_neg_one : 0 ≤ (-1 : ℝ) :=
      Eq.subst (motive := fun x : ℝ => 0 ≤ x) hnegative hpos
    exact False.elim ((not_le_of_gt neg_one_lt_zero) hnonnegative_neg_one)

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
