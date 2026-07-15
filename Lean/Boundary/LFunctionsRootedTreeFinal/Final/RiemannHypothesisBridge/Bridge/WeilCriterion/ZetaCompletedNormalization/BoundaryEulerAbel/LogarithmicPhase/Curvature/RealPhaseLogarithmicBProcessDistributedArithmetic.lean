import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicBProcessScaleArithmetic

/-!
# Distributed arithmetic for the balanced active budget

The closed active majorant is a product of a cardinality factor and a
four-term packet factor.  Estimating those factors separately would lose one
power of the square-root scale.  This owner distributes the product first and
records a reusable nonnegative four-term product inequality.  Each resulting
term is then bounded at its natural scale.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.mul_four_term_sum
    (x a b c d : ℝ) :
    x * (a + b + c + d) =
      x * a + x * b + x * c + x * d := by
  calc
    x * (a + b + c + d) = x * (a + b + c) + x * d :=
      mul_add x (a + b + c) d
    _ = (x * (a + b) + x * c) + x * d := by
      exact congrArg (fun value : ℝ => value + x * d)
        (mul_add x (a + b) c)
    _ = ((x * a + x * b) + x * c) + x * d := by
      exact congrArg (fun value : ℝ => (value + x * c) + x * d)
        (mul_add x a b)
    _ = x * a + x * b + x * c + x * d := rfl

theorem Real.add_mul_four_term_sum
    (x y a b c d : ℝ) :
    (x + y) * (a + b + c + d) =
      (x * a + x * b + x * c + x * d) +
        (y * a + y * b + y * c + y * d) := by
  exact
    (add_mul x y (a + b + c + d)).trans
      (congrArg₂ (fun left right : ℝ => left + right)
        (Real.mul_four_term_sum x a b c d)
        (Real.mul_four_term_sum y a b c d))

theorem Real.four_term_add_le
    {a b c d A B C D : ℝ}
    (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C) (hd : d ≤ D) :
    a + b + c + d ≤ A + B + C + D := by
  exact add_le_add (add_le_add (add_le_add ha hb) hc) hd

theorem Real.add_two_four_term_bounds
    {a b c d e f g h A B C D E F G H : ℝ}
    (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C) (hd : d ≤ D)
    (he : e ≤ E) (hf : f ≤ F) (hg : g ≤ G) (hh : h ≤ H) :
    (a + b + c + d) + (e + f + g + h) ≤
      (A + B + C + D) + (E + F + G + H) := by
  exact add_le_add
    (Real.four_term_add_le ha hb hc hd)
    (Real.four_term_add_le he hf hg hh)

theorem Real.longGeometry_one_third_a_le_cutoffSupportLeft
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    (a : ℝ) / 3 ≤
      Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ) := by
  unfold Real.integerBlockCutoffSupportLeftEndpoint
  have haTwo :=
    Real.logarithmicPhaseLongBranchGeometry_two_le_a hgeometry
  have haReal : (2 : ℝ) ≤ (a : ℝ) := Nat.cast_le.mpr haTwo
  have hthreePos : (0 : ℝ) < 3 :=
    Nat.cast_pos.mpr (Nat.succ_pos 2)
  have htwoThird : (2 : ℝ) / 3 ≤ 2 := by
    have honeThree : (1 : ℝ) ≤ 3 := Nat.one_le_ofNat
    have hdiv : (1 : ℝ) / 3 ≤ 1 :=
      (div_le_one hthreePos).mpr honeThree
    have hscaled := mul_le_mul_of_nonneg_left hdiv zero_le_two
    have hnormalize : (2 : ℝ) * (1 / 3) = 2 / 3 := by
      exact (congrArg (fun value : ℝ => 2 * value) (one_div 3)).trans
        (div_eq_mul_inv 2 3).symm
    exact le_trans (le_of_eq hnormalize.symm)
      (le_trans hscaled (le_of_eq (mul_one (2 : ℝ))))
  have htwoThirdA : (2 : ℝ) / 3 ≤ (a : ℝ) :=
    le_trans htwoThird haReal
  have hadd : (a : ℝ) / 3 + 2 / 3 ≤ (a : ℝ) := by
    have haNonneg : 0 ≤ (a : ℝ) := Nat.cast_nonneg a
    have hfirst : (a : ℝ) + 2 ≤ (a : ℝ) + (a : ℝ) :=
      add_le_add_left haReal (a : ℝ)
    have htwoLeThree : (2 : ℝ) ≤ 3 :=
      Nat.cast_le.mpr (show (2 : ℕ) ≤ 3 from Nat.le_succ 2)
    have hcoefficient :=
      mul_le_mul_of_nonneg_left htwoLeThree haNonneg
    have hsumToTwoMul :
        (a : ℝ) + (a : ℝ) = (a : ℝ) * 2 :=
      Eq.trans (two_mul (a : ℝ)).symm (mul_comm 2 (a : ℝ))
    have hnumerator : (a : ℝ) + 2 ≤ (a : ℝ) * 3 :=
      le_trans hfirst
        (le_trans (le_of_eq hsumToTwoMul) hcoefficient)
    have hdivided : ((a : ℝ) + 2) / 3 ≤ (a : ℝ) :=
      (div_le_iff₀ hthreePos).mpr hnumerator
    have hcombine :
        (a : ℝ) / 3 + 2 / 3 = ((a : ℝ) + 2) / 3 :=
      div_add_div_same (a : ℝ) 2 3
    exact le_trans (le_of_eq hcombine) hdivided
  exact (le_sub_iff_add_le).mpr hadd

theorem Real.longGeometry_frequencyCardTerm_le_three_norm_div_a
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    ‖t‖ /
        (2 * Real.pi *
          Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ)) ≤
      3 * (‖t‖ / (a : ℝ)) := by
  have hleft :=
    Real.longGeometry_one_third_a_le_cutoffSupportLeft hgeometry
  have htwoPi : (1 : ℝ) ≤ 2 * Real.pi := Real.one_le_two_mul_pi
  have haPos : 0 < (a : ℝ) :=
    Nat.cast_pos.mpr
      (Real.logarithmicPhaseLongBranchGeometry_zero_lt_a hgeometry)
  have hleftPos :
      0 < Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ) :=
    Complex.integerBlockCutoffSupportLeftEndpoint_pos
      (Int.ofNat_le.mpr
        (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry))
  have hdenominatorLower :
      (a : ℝ) / 3 ≤
        2 * Real.pi *
          Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ) := by
    have hscaled := mul_le_mul_of_nonneg_right htwoPi hleftPos.le
    have hleftIdentity :
        Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ) =
          1 * Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ) :=
      (one_mul _).symm
    exact le_trans hleft
      (le_trans (le_of_eq hleftIdentity) hscaled)
  have hdenominatorPos :
      0 < 2 * Real.pi *
        Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ) :=
    mul_pos Complex.two_mul_pi_pos hleftPos
  have haThirdPos : 0 < (a : ℝ) / 3 :=
    div_pos haPos (Nat.cast_pos.mpr (Nat.succ_pos 2))
  have hdivision := div_le_div_of_nonneg_left
    (norm_nonneg t) haThirdPos hdenominatorLower
  have hnormalize :
      ‖t‖ / ((a : ℝ) / 3) = 3 * (‖t‖ / (a : ℝ)) := by
    have hthreeNe : (3 : ℝ) ≠ 0 :=
      ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 2))
    have haNe : (a : ℝ) ≠ 0 := ne_of_gt haPos
    calc
      ‖t‖ / ((a : ℝ) / 3) = ‖t‖ * 3 / (a : ℝ) := by
        exact div_div_eq_mul_div ‖t‖ (a : ℝ) 3
      _ = 3 * (‖t‖ / (a : ℝ)) := by
        exact Eq.trans
          (congrArg (fun value : ℝ => value / (a : ℝ))
            (mul_comm ‖t‖ 3))
          (mul_div_assoc 3 ‖t‖ (a : ℝ))
  exact le_trans hdivision (le_of_eq hnormalize)

theorem Real.longGeometry_frequencyCardTerm_le_three_scale
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    ‖t‖ /
        (2 * Real.pi *
          Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ)) ≤
      3 * Complex.logarithmicPhaseBProcessScale t := by
  have hfrequency :=
    Real.longGeometry_frequencyCardTerm_le_three_norm_div_a hgeometry
  have hnormA := Real.longGeometry_norm_div_a_le_scale hgeometry
  have hscaled := mul_le_mul_of_nonneg_left hnormA (Nat.cast_nonneg 3)
  exact le_trans hfrequency hscaled

theorem Real.two_le_two_mul_scale
    (t : ℝ) :
    (2 : ℝ) ≤ 2 * Complex.logarithmicPhaseBProcessScale t := by
  have hone := Complex.logarithmicPhaseBProcessScale_one_le t
  have hscaled := mul_le_mul_of_nonneg_left hone zero_le_two
  exact le_trans (le_of_eq (mul_one (2 : ℝ)).symm) hscaled

end

end LFunctions
end Boundary
