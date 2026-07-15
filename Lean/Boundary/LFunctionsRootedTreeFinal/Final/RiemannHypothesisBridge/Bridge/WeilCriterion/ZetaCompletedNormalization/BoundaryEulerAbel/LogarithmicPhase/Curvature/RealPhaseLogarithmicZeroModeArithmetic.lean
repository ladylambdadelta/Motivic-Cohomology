import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicInfiniteTailClosure

/-!
# Zero-mode arithmetic in the refined scale

The transition packet contributes `2/3`, two endpoint quotients, and one block
length quotient.  Each is bounded directly by the endpoint component of the
refined scale, giving a total cost below `4` refined-scale units.
-/

namespace Boundary
namespace LFunctions

noncomputable section

private theorem zeroMode_realOfNat_add_eq_of_nat_eq
    (a b c : ℕ) (h : a + b = c) :
    (a : ℝ) + (b : ℝ) = (c : ℝ) :=
  Eq.trans (Nat.cast_add a b).symm
    (congrArg (fun n : ℕ => (n : ℝ)) h)

private theorem zeroMode_realOfNat_mul_eq_of_nat_eq
    (a b c : ℕ) (h : a * b = c) :
    (a : ℝ) * (b : ℝ) = (c : ℝ) :=
  Eq.trans (Nat.cast_mul a b).symm
    (congrArg (fun n : ℕ => (n : ℝ)) h)

private theorem zeroMode_ofNat_add_eq_of_nat_eq
    (a b c : ℕ) [Nat.AtLeastTwo a] [Nat.AtLeastTwo b] [Nat.AtLeastTwo c]
    (h : a + b = c) :
    (OfNat.ofNat a : ℝ) + OfNat.ofNat b = OfNat.ofNat c := by
  have hcast := zeroMode_realOfNat_add_eq_of_nat_eq a b c h
  exact Eq.trans
    (congrArg₂ (fun left right : ℝ => left + right)
      (Nat.cast_eq_ofNat (n := a)).symm
      (Nat.cast_eq_ofNat (n := b)).symm)
    (Eq.trans hcast (Nat.cast_eq_ofNat (n := c)))

private theorem zeroMode_ofNat_mul_eq_of_nat_eq
    (a b c : ℕ) [Nat.AtLeastTwo a] [Nat.AtLeastTwo b] [Nat.AtLeastTwo c]
    (h : a * b = c) :
    (OfNat.ofNat a : ℝ) * OfNat.ofNat b = OfNat.ofNat c := by
  have hcast := zeroMode_realOfNat_mul_eq_of_nat_eq a b c h
  exact Eq.trans
    (congrArg₂ (fun left right : ℝ => left * right)
      (Nat.cast_eq_ofNat (n := a)).symm
      (Nat.cast_eq_ofNat (n := b)).symm)
    (Eq.trans hcast (Nat.cast_eq_ofNat (n := c)))

private theorem zeroMode_eleven_add_one_eq_twelve :
    (11 : ℝ) + 1 = 12 := by
  have hcast := zeroMode_realOfNat_add_eq_of_nat_eq 11 1 12 rfl
  exact Eq.trans
    (congrArg₂ (fun left right : ℝ => left + right)
      (Nat.cast_eq_ofNat (n := 11)).symm
      (Nat.cast_one (R := ℝ)).symm)
    (Eq.trans hcast (Nat.cast_eq_ofNat (n := 12)))

private theorem zeroMode_two_thirds_add_two_add_one_eq_eleven_thirds :
    (2 / 3 : ℝ) + 2 + 1 = 11 / 3 := by
  have hthreeNe : (3 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 2))
  have htwoMulThree : (2 : ℝ) * 3 = 6 :=
    zeroMode_ofNat_mul_eq_of_nat_eq 2 3 6 rfl
  have hsix : (2 : ℝ) = 6 / 3 :=
    (eq_div_iff hthreeNe).mpr htwoMulThree
  have hthree : (1 : ℝ) = 3 / 3 :=
    (eq_div_iff hthreeNe).mpr (one_mul (3 : ℝ))
  have hfirst : (2 / 3 : ℝ) + 6 / 3 = (2 + 6) / 3 :=
    div_add_div_same 2 6 3
  have hsecond : ((2 + 6 : ℝ) / 3) + 3 / 3 = ((2 + 6) + 3) / 3 :=
    div_add_div_same (2 + 6) 3 3
  have htwoAddSix : (2 : ℝ) + 6 = 8 :=
    zeroMode_ofNat_add_eq_of_nat_eq 2 6 8 rfl
  have heightAddThree : (8 : ℝ) + 3 = 11 :=
    zeroMode_ofNat_add_eq_of_nat_eq 8 3 11 rfl
  have hnumerator : ((2 + 6 : ℝ) + 3) = 11 :=
    Eq.trans (congrArg (fun value : ℝ => value + 3) htwoAddSix)
      heightAddThree
  exact Eq.trans
    (congrArg₂ (fun left right : ℝ => 2 / 3 + left + right)
      hsix hthree)
    (Eq.trans
      (congrArg (fun value : ℝ => value + 3 / 3) hfirst)
      (Eq.trans hsecond
        (congrArg (fun numerator : ℝ => numerator / 3) hnumerator)))

theorem Real.natBlockRight_div_norm_le_refinedScale
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖) :
    (b : ℝ) / ‖t‖ ≤
      Real.logarithmicPhaseRefinedScale t (b : ℤ) := by
  unfold Real.logarithmicPhaseRefinedScale
  have hnormPos := Complex.logarithmicPhaseBProcess_norm_pos t ht
  have hnumerator : (b : ℝ) ≤ (b : ℝ) + 1 :=
    le_add_of_nonneg_right zero_le_one
  have hdivision := div_le_div_of_nonneg_right hnumerator hnormPos.le
  have hsqrt := Real.sqrt_nonneg (1 + ‖t‖)
  exact le_trans hdivision (le_add_of_nonneg_right hsqrt)

theorem Real.natBlockLength_div_norm_le_refinedScale
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖) (hab : a ≤ b) :
    ((b : ℝ) - (a : ℝ)) / ‖t‖ ≤
      Real.logarithmicPhaseRefinedScale t (b : ℤ) := by
  have haNonneg : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have hlength : (b : ℝ) - (a : ℝ) ≤ (b : ℝ) :=
    sub_le_self _ haNonneg
  have hnormPos := Complex.logarithmicPhaseBProcess_norm_pos t ht
  have hdivision := div_le_div_of_nonneg_right hlength hnormPos.le
  exact le_trans hdivision
    (Real.natBlockRight_div_norm_le_refinedScale (t := t) (a := a) (b := b) ht)

theorem Real.natBlockLength_smul_normInv_eq_div
    (t : ℝ) (a b : ℕ) :
    (((b : ℝ) - (a : ℝ)) • ‖t‖⁻¹) =
      ((b : ℝ) - (a : ℝ)) / ‖t‖ := by
  exact Eq.trans
    (@smul_eq_mul ℝ _ ((b : ℝ) - (a : ℝ)) ‖t‖⁻¹)
    (div_eq_mul_inv _ _).symm

theorem Complex.logarithmicPhaseQuantitativeZeroModeBudget_le_eleven_thirds_refined
    (t : ℝ) (a b : ℕ)
    (ht : 1 ≤ ‖t‖)
    (hab : a ≤ b) :
    Complex.logarithmicPhaseQuantitativeZeroModeBudget
        t (a : ℤ) (b : ℤ) ≤
      (11 / 3 : ℝ) * Real.logarithmicPhaseRefinedScale t (b : ℤ) := by
  let R := Real.logarithmicPhaseRefinedScale t (b : ℤ)
  have hb : (0 : ℤ) ≤ (b : ℤ) := Int.ofNat_zero_le b
  have hone := Real.one_le_logarithmicPhaseRefinedScale t (b : ℤ) ht hb
  have hconstant : (2 / 3 : ℝ) ≤ (2 / 3) * R := by
    have hscaled := mul_le_mul_of_nonneg_left hone
      (div_nonneg (Nat.cast_nonneg 2) (Nat.cast_nonneg 3))
    exact Eq.subst (motive := fun value : ℝ => value ≤ _)
      (mul_one (2 / 3 : ℝ)) hscaled
  have hright := Real.natBlockRight_div_norm_le_refinedScale
    (t := t) (a := a) (b := b) ht
  have hrightTwice := mul_le_mul_of_nonneg_left hright (Nat.cast_nonneg 2)
  have hlength := Real.natBlockLength_div_norm_le_refinedScale
    (t := t) (a := a) (b := b) ht hab
  have hlengthCast :
      ((b : ℤ) : ℝ) - ((a : ℤ) : ℝ) =
        (b : ℝ) - (a : ℝ) := by
    exact congrArg₂ (fun left right : ℝ => left - right)
      (Int.cast_natCast b) (Int.cast_natCast a)
  have hsmul :
      ((((b : ℤ) : ℝ) - ((a : ℤ) : ℝ) : ℝ) • ‖t‖⁻¹) ≤ R := by
    exact Eq.subst
      (motive := fun value : ℝ => value • ‖t‖⁻¹ ≤ R)
      hlengthCast.symm
      (Eq.subst
        (motive := fun value : ℝ => value ≤ R)
        (Real.natBlockLength_smul_normInv_eq_div t a b).symm
        hlength)
  unfold Complex.logarithmicPhaseQuantitativeZeroModeBudget
  have hcombined := add_le_add (add_le_add hconstant hrightTwice) hsmul
  have hweighted : (2 / 3) * R + 2 * R + R = (11 / 3) * R := by
    have hfactor := Real.three_weighted_terms_eq_sum_coeff_mul
      (2 / 3) 2 1 R
    exact Eq.trans
      (congrArg (fun value : ℝ => (2 / 3) * R + 2 * R + value)
        (one_mul R).symm)
      (hfactor.trans
        (congrArg (fun coefficient : ℝ => coefficient * R)
          zeroMode_two_thirds_add_two_add_one_eq_eleven_thirds))
  exact le_trans hcombined (le_of_eq hweighted)

theorem Complex.logarithmicPhaseQuantitativeZeroModeBudget_le_four_refined
    (t : ℝ) (a b : ℕ)
    (ht : 1 ≤ ‖t‖)
    (hab : a ≤ b) :
    Complex.logarithmicPhaseQuantitativeZeroModeBudget
        t (a : ℤ) (b : ℤ) ≤
      4 * Real.logarithmicPhaseRefinedScale t (b : ℤ) := by
  let R := Real.logarithmicPhaseRefinedScale t (b : ℤ)
  have hsharp :=
    Complex.logarithmicPhaseQuantitativeZeroModeBudget_le_eleven_thirds_refined
      t a b ht hab
  have hb : (0 : ℤ) ≤ (b : ℤ) := Int.ofNat_zero_le b
  have hthreePos : (0 : ℝ) < 3 :=
    Nat.cast_pos.mpr (Nat.succ_pos 2)
  have helevenAddOne : (11 : ℝ) + 1 = 12 :=
    zeroMode_eleven_add_one_eq_twelve
  have hfourMulThree : (4 : ℝ) * 3 = 12 :=
    zeroMode_ofNat_mul_eq_of_nat_eq 4 3 12 rfl
  have helevenLeTwelve : (11 : ℝ) ≤ 12 :=
    le_trans (le_add_of_nonneg_right zero_le_one)
      (le_of_eq helevenAddOne)
  have helevenLeProduct : (11 : ℝ) ≤ 4 * 3 :=
    Eq.subst (motive := fun value : ℝ => 11 ≤ value)
      hfourMulThree.symm helevenLeTwelve
  have hcoefficient : (11 / 3 : ℝ) ≤ 4 :=
    (div_le_iff₀ hthreePos).mpr helevenLeProduct
  have henlarge := mul_le_mul_of_nonneg_right hcoefficient
    (Real.logarithmicPhaseRefinedScale_nonneg t (b : ℤ) hb)
  exact le_trans hsharp henlarge

end

end LFunctions
end Boundary
