import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# Finite Bernstein budgets

This owner records the order-theoretic fact used by normalized oscillatory
budgets: a Bernstein combination on the unit interval is bounded by a common
upper bound for its coefficients.  The proof keeps the nonnegative basis
weights and their exact partition of unity visible.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.sum_fin_five (f : Fin 5 → ℝ) :
    (∑ k : Fin 5, f k) = f 0 + f 1 + f 2 + f 3 + f 4 := by
  have hfive := Fin.sum_univ_succ f
  have hfour := Fin.sum_univ_succ (fun k : Fin 4 => f k.succ)
  have hthree := Fin.sum_univ_succ (fun k : Fin 3 => f k.succ.succ)
  have htwo := Fin.sum_univ_succ (fun k : Fin 2 => f k.succ.succ.succ)
  have hone := Fin.sum_univ_one (fun k : Fin 1 => f k.succ.succ.succ.succ)
  exact Eq.trans hfive
    (Eq.trans
      (congrArg (fun value : ℝ => f 0 + value) hfour)
      (Eq.trans
        (congrArg (fun value : ℝ => f 0 + (f 1 + value)) hthree)
        (Eq.trans
          (congrArg (fun value : ℝ => f 0 + (f 1 + (f 2 + value))) htwo)
          (Eq.trans
            (congrArg
              (fun value : ℝ => f 0 + (f 1 + (f 2 + (f 3 + value))))
              hone)
            (Eq.trans (add_assoc (f 0) (f 1) (f 2 + (f 3 + f 4))).symm
              (Eq.trans
                (add_assoc (f 0 + f 1) (f 2) (f 3 + f 4)).symm
                (add_assoc (f 0 + f 1 + f 2) (f 3) (f 4)).symm))))))

theorem Real.reverse_three_term_sum (a b c : ℝ) :
    a + b + c = c + b + a := by
  exact Eq.trans (add_comm (a + b) c)
    (Eq.trans (congrArg (fun value : ℝ => c + value) (add_comm a b))
      (add_assoc c b a).symm)

theorem Real.reverse_four_term_sum (a b c d : ℝ) :
    a + b + c + d = d + c + b + a := by
  exact Eq.trans (add_comm (a + b + c) d)
    (Eq.trans
      (congrArg (fun value : ℝ => d + value)
        (Real.reverse_three_term_sum a b c))
      (Eq.trans (add_assoc d (c + b) a).symm
        (congrArg (fun value : ℝ => value + a) (add_assoc d c b).symm)))

theorem Real.reverse_five_term_sum (a b c d e : ℝ) :
    a + b + c + d + e = e + d + c + b + a := by
  exact Eq.trans (add_comm (a + b + c + d) e)
    (Eq.trans
      (congrArg (fun value : ℝ => e + value)
        (Real.reverse_four_term_sum a b c d))
      (Eq.trans (add_assoc e (d + c + b) a).symm
        (Eq.trans
          (congrArg (fun value : ℝ => value + a)
            (add_assoc e (d + c) b).symm)
          (congrArg (fun value : ℝ => value + b + a)
            (add_assoc e d c).symm))))

open scoped BigOperators unitInterval

/-- Multiplication preserves a coefficient bound against a nonnegative
Bernstein basis weight. -/
theorem Real.bernstein_coefficient_mul_le
    {n : ℕ} {x : I} {coefficient majorant : ℝ}
    (hcoefficient : coefficient ≤ majorant)
    (k : Fin (n + 1)) :
    coefficient * bernstein n k x ≤
      majorant * bernstein n k x := by
  exact mul_le_mul_of_nonneg_right hcoefficient bernstein_nonneg

/-- A finite Bernstein combination is at most a common coefficient
majorant. -/
theorem Real.sum_bernstein_mul_le_coefficient_majorant
    (n : ℕ)
    (x : I)
    (coefficient : Fin (n + 1) → ℝ)
    (majorant : ℝ)
    (hcoefficient : ∀ k, coefficient k ≤ majorant) :
    (∑ k : Fin (n + 1), coefficient k * bernstein n k x) ≤
      majorant := by
  have hpointwise :
      (∑ k : Fin (n + 1), coefficient k * bernstein n k x) ≤
        ∑ k : Fin (n + 1), majorant * bernstein n k x :=
    Finset.sum_le_sum
      (fun k _hk =>
        Real.bernstein_coefficient_mul_le (hcoefficient k) k)
  have hfactor :
      (∑ k : Fin (n + 1), majorant * bernstein n k x) =
        majorant * (∑ k : Fin (n + 1), bernstein n k x) :=
    (Finset.mul_sum Finset.univ
      (fun k : Fin (n + 1) => bernstein n k x) majorant).symm
  have hprobability :
      (∑ k : Fin (n + 1), bernstein n k x) = 1 :=
    bernstein.probability n x
  have hnormalize :
      (∑ k : Fin (n + 1), majorant * bernstein n k x) =
        majorant :=
    Eq.trans hfactor
      (Eq.trans
        (congrArg (fun value : ℝ => majorant * value) hprobability)
        (mul_one majorant))
  exact le_trans hpointwise (le_of_eq hnormalize)

/-- Nonnegative coefficients give a nonnegative Bernstein combination. -/
theorem Real.sum_bernstein_mul_nonneg
    (n : ℕ)
    (x : I)
    (coefficient : Fin (n + 1) → ℝ)
    (hcoefficient : ∀ k, 0 ≤ coefficient k) :
    0 ≤ ∑ k : Fin (n + 1), coefficient k * bernstein n k x := by
  exact Finset.sum_nonneg
    (fun k _hk => mul_nonneg (hcoefficient k) bernstein_nonneg)

end

end LFunctions
end Boundary
