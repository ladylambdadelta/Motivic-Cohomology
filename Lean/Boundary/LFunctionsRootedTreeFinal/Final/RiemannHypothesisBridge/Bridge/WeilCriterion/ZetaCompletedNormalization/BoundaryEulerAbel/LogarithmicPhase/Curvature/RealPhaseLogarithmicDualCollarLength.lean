import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicDualCrossingCollars

/-!
# Quantitative length of dual principal collars

On a positive interval the shifted derivative is negative and increasing.  If
its growth is at least `mu` per unit distance, then a derivative-value collar
of half-width `eta` has spatial diameter at most `2*eta/mu`.  This file proves
that conversion explicitly and specializes all sign transports to the dual
logarithmic shifted phase.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.sub_le_two_eta_of_abs_sub_le
    {a b level eta : ℝ}
    (ha : |a - level| ≤ eta)
    (hb : |b - level| ≤ eta) :
    a - b ≤ 2 * eta := by
  have haUpper : a - level ≤ eta := le_trans (le_abs_self (a - level)) ha
  have hbLower : -eta ≤ b - level := by
    have hneg := neg_le_of_abs_le hb
    exact hneg
  have hminus : level - b ≤ eta := by
    have hnegated : -(b - level) ≤ eta :=
      neg_le.mp hbLower
    exact Eq.subst (motive := fun z : ℝ => z ≤ eta)
      (neg_sub b level).symm hnegated
  have hadd := add_le_add haUpper hminus
  have hleft : (a - level) + (level - b) = a - b := by
    exact sub_add_sub_cancel a level b
  have hright : eta + eta = 2 * eta := (two_mul eta).symm
  exact Eq.subst (motive := fun z : ℝ => z ≤ 2 * eta)
    hleft.symm
    (Eq.subst (motive := fun z : ℝ => _ ≤ z) hright.symm hadd)

theorem Real.distance_le_two_eta_of_same_level_collar
    {a b level eta : ℝ}
    (ha : |a - level| ≤ eta)
    (hb : |b - level| ≤ eta) :
    |a - b| ≤ 2 * eta := by
  have hab := Real.sub_le_two_eta_of_abs_sub_le ha hb
  have hba := Real.sub_le_two_eta_of_abs_sub_le hb ha
  exact abs_le.mpr (And.intro
    (Eq.subst (motive := fun z : ℝ => -2 * eta ≤ z)
      (neg_sub b a).symm (neg_le_neg hba)) hab)

theorem Real.signed_difference_eq_abs_reverse_difference
    {a b : ℝ} (ha : a < 0) (hb : b < 0) :
    b - a = |a| - |b| := by
  have haAbs : |a| = -a := abs_of_neg ha
  have hbAbs : |b| = -b := abs_of_neg hb
  exact Eq.trans
    (congrArg₂ (fun x y : ℝ => x - y) hbAbs.symm haAbs.symm)
    (by
      exact Eq.trans
        (sub_neg_eq_add (-b) a)
        (Eq.trans (add_comm (-b) a)
          (sub_eq_add_neg b a).symm))

theorem Real.collar_diameter_of_negative_growth
    (g : ℝ → ℝ) {L U level eta mu x y : ℝ}
    (hmu : 0 < mu)
    (hxy : x ≤ y)
    (hxNeg : g x < 0)
    (hyNeg : g y < 0)
    (hgrowth : mu * (y - x) ≤ g y - g x)
    (hxCollar : ||g x| - level| ≤ eta)
    (hyCollar : ||g y| - level| ≤ eta) :
    y - x ≤ 2 * eta / mu := by
  have habsDifference : g y - g x = |g x| - |g y| :=
    Real.signed_difference_eq_abs_reverse_difference hxNeg hyNeg
  have hvalue : |g x| - |g y| ≤ 2 * eta :=
    Real.sub_le_two_eta_of_abs_sub_le hxCollar hyCollar
  have hscaled : mu * (y - x) ≤ 2 * eta :=
    le_trans hgrowth
      (Eq.subst (motive := fun z : ℝ => z ≤ 2 * eta)
        habsDifference.symm hvalue)
  exact (le_div_iff₀ hmu).mpr
    (Eq.subst (motive := fun z : ℝ => z ≤ 2 * eta)
      (mul_comm (y - x) mu) hscaled)

theorem Complex.logarithmicPhaseDualCrossingCollar_diameter_le
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    {h eta L U mu x y : ℝ} {q : ℕ}
    (hh : 0 < h)
    (hL : 0 < L)
    (hmu : 0 < mu)
    (hxy : x ≤ y)
    (hx : x ∈
      Complex.logarithmicPhaseDualCrossingCollar t h eta L U q)
    (hy : y ∈
      Complex.logarithmicPhaseDualCrossingCollar t h eta L U q)
    (hgrowth :
      mu * (y - x) ≤
        Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h y -
          Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h x) :
    y - x ≤ 2 * eta / mu := by
  have hxPos : 0 < x := lt_of_lt_of_le hL hx.1.1
  have hyPos : 0 < y := lt_of_lt_of_le hxPos hxy
  have hxNeg :=
    Complex.logarithmicPhaseDualShiftedDifferenceDerivative_neg
      t ht hh hxPos
  have hyNeg :=
    Complex.logarithmicPhaseDualShiftedDifferenceDerivative_neg
      t ht hh hyPos
  exact Real.collar_diameter_of_negative_growth
    (Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h)
    hmu hxy hxNeg hyNeg hgrowth hx.2 hy.2

theorem Real.growth_lower_of_difference_quotient
    {mu x y gx gy : ℝ}
    (hxy : x ≤ y)
    (hquotient : mu ≤ (gy - gx) / (y - x))
    (hstrict : x < y) :
    mu * (y - x) ≤ gy - gx := by
  have hdistance : 0 < y - x := sub_pos.mpr hstrict
  exact (le_div_iff₀ hdistance).mp hquotient

end

end LFunctions
end Boundary
