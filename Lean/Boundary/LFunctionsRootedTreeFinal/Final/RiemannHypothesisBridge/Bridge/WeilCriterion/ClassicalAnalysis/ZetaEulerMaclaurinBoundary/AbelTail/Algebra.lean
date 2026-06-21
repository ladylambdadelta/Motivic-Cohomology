import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.AbelTail.Finite

/-!
# Algebra for Abel tails on the boundary line

This file owns the small algebraic transports used by the Abel tail argument.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Complex.neg_sub_mul_eq_ofReal_sub_mul_for_abelTail
    (x y : ℝ)
    (z : ℂ) :
    -(((y : ℂ) - (x : ℂ)) * z) = (((x - y : ℝ) : ℂ) * z) := by
  have hneg_sub : -((y : ℂ) - (x : ℂ)) = (x : ℂ) - (y : ℂ) :=
    neg_sub (y : ℂ) (x : ℂ)
  have hcast_sub : (((x - y : ℝ) : ℂ)) = (x : ℂ) - (y : ℂ) :=
    Complex.ofReal_sub x y
  calc
    -(((y : ℂ) - (x : ℂ)) * z) =
        (-((y : ℂ) - (x : ℂ))) * z := by
      exact (neg_mul ((y : ℂ) - (x : ℂ)) z).symm
    _ = ((x : ℂ) - (y : ℂ)) * z := by
      exact congrArg (fun c : ℂ => c * z) hneg_sub
    _ = (((x - y : ℝ) : ℂ) * z) := by
      exact congrArg (fun c : ℂ => c * z) hcast_sub.symm

theorem Real.coefficient_mass_step_arithmetic_for_abelTail
    (a b s : ℝ) :
    a + (s + (b - a)) = b + s := by
  calc
    a + (s + (b - a)) = a + ((b - a) + s) := by
      exact congrArg (fun u : ℝ => a + u) (add_comm s (b - a))
    _ = (a + (b - a)) + s := by
      exact (add_assoc a (b - a) s).symm
    _ = ((b - a) + a) + s := by
      exact congrArg (fun u : ℝ => u + s) (add_comm a (b - a))
    _ = b + s := by
      exact congrArg (fun u : ℝ => u + s) (sub_add_cancel b a)

theorem Real.one_add_sub_one_eq_for_abelTail
    (σ : ℝ) :
    1 + (σ - 1) = σ := by
  calc
    1 + (σ - 1) = (σ - 1) + 1 := by
      exact add_comm 1 (σ - 1)
    _ = σ := sub_add_cancel σ 1

theorem Complex.neg_add_add_comm_for_abelTail
    (a b c : ℂ) :
    -((a + b) + c) = -a + -c + -b := by
  calc
    -((a + b) + c) = -(a + b) + -c := by
      exact neg_add (a + b) c
    _ = (-a + -b) + -c := by
      exact congrArg (fun z : ℂ => z + -c) (neg_add a b)
    _ = -a + (-b + -c) := by
      exact add_assoc (-a) (-b) (-c)
    _ = -a + (-c + -b) := by
      exact congrArg (fun z : ℂ => -a + z) (add_comm (-b) (-c))
    _ = -a + -c + -b := by
      exact (add_assoc (-a) (-c) (-b)).symm

end

end LFunctions
end Boundary
