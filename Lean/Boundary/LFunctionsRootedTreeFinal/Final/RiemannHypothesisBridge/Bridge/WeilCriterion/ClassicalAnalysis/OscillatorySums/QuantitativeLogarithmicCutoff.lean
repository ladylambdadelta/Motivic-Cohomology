import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.QuantitativeCutoff

/-!
# Positive quantitative cutoff for logarithmic phases

The logarithmic phase is singular at zero.  This cutoff uses a transition of
width one third, so a block beginning at `1` is still identically zero on a
positive neighborhood of the singularity.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

def Real.quantitativeLogarithmicLeftCutoff
    (a : ℤ) (x : ℝ) : ℝ :=
  Real.smoothTransition (3 * (x - (a : ℝ)) + 1)

def Real.quantitativeLogarithmicRightCutoff
    (b : ℤ) (x : ℝ) : ℝ :=
  Real.smoothTransition (3 * ((b : ℝ) - x) + 1)

def Real.quantitativeLogarithmicBlockCutoff
    (a b : ℤ) (x : ℝ) : ℝ :=
  Real.quantitativeLogarithmicLeftCutoff a x *
    Real.quantitativeLogarithmicRightCutoff b x

theorem Real.three_mul_one_div_three_eq_one :
    (3 : ℝ) * (1 / 3) = 1 := by
  have hthree_ne : (3 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 2))
  calc
    (3 : ℝ) * (1 / 3) = (3 * 1) / 3 :=
      (mul_div_assoc 3 1 3).symm
    _ = 3 / 3 :=
      congrArg (fun value : ℝ => value / 3) (mul_one 3)
    _ = 1 := div_self hthree_ne

theorem Real.three_mul_neg_one_div_three_add_one_eq_zero :
    (3 : ℝ) * (-(1 / 3)) + 1 = 0 := by
  calc
    (3 : ℝ) * (-(1 / 3)) + 1 = -((3 : ℝ) * (1 / 3)) + 1 :=
      congrArg (fun value : ℝ => value + 1) (mul_neg 3 (1 / 3))
    _ = -1 + 1 :=
      congrArg (fun value : ℝ => -value + 1)
        Real.three_mul_one_div_three_eq_one
    _ = 0 := neg_add_cancel 1

theorem Real.one_div_three_le_one :
    (1 / 3 : ℝ) ≤ 1 := by
  have hthree_pos : (0 : ℝ) < 3 :=
    Nat.cast_pos.mpr (Nat.succ_pos 2)
  have hone_le_three : (1 : ℝ) ≤ 3 := by
    calc
      (1 : ℝ) = ((1 : ℕ) : ℝ) := Nat.cast_one.symm
      _ ≤ ((3 : ℕ) : ℝ) := Nat.cast_le.mpr (show (1 : ℕ) ≤ 3 by decide)
      _ = 3 := rfl
  have hcomparison : (1 : ℝ) ≤ 1 * 3 := by
    calc
      (1 : ℝ) = 1 * 1 := (mul_one 1).symm
      _ ≤ 1 * 3 := mul_le_mul_of_nonneg_left hone_le_three zero_le_one
  exact (div_le_iff₀ hthree_pos).mpr hcomparison

theorem Real.quantitativeLogarithmicLeftCutoff_eq_zero_of_le
    {a : ℤ} {x : ℝ}
    (hx : x ≤ (a : ℝ) - 1 / 3) :
    Real.quantitativeLogarithmicLeftCutoff a x = 0 := by
  unfold Real.quantitativeLogarithmicLeftCutoff
  have hsub : x - (a : ℝ) ≤ ((a : ℝ) - 1 / 3) - (a : ℝ) :=
    sub_le_sub_right hx (a : ℝ)
  have hendpoint : ((a : ℝ) - 1 / 3) - (a : ℝ) = -(1 / 3) :=
    sub_sub_cancel_left (a : ℝ) (1 / 3)
  have hscaled :
      3 * (x - (a : ℝ)) ≤ 3 * (-(1 / 3)) :=
    mul_le_mul_of_nonneg_left
      (Eq.subst
        (motive := fun right : ℝ => x - (a : ℝ) ≤ right)
        hendpoint
        hsub)
      zero_le_three
  have hargument : 3 * (x - (a : ℝ)) + 1 ≤ 0 := by
    calc
      3 * (x - (a : ℝ)) + 1 ≤ 3 * (-(1 / 3)) + 1 :=
        add_le_add_right hscaled 1
      _ = 0 := Real.three_mul_neg_one_div_three_add_one_eq_zero
  exact Real.smoothTransition.zero_of_nonpos hargument

theorem Real.quantitativeLogarithmicLeftCutoff_eq_one_of_le
    {a : ℤ} {x : ℝ}
    (hx : (a : ℝ) ≤ x) :
    Real.quantitativeLogarithmicLeftCutoff a x = 1 := by
  unfold Real.quantitativeLogarithmicLeftCutoff
  have hsub : 0 ≤ x - (a : ℝ) :=
    sub_nonneg.mpr hx
  have hscaled : 0 ≤ 3 * (x - (a : ℝ)) :=
    mul_nonneg zero_le_three hsub
  have hargument : (1 : ℝ) ≤ 3 * (x - (a : ℝ)) + 1 := by
    calc
      (1 : ℝ) = 0 + 1 := (zero_add 1).symm
      _ ≤ 3 * (x - (a : ℝ)) + 1 := add_le_add_right hscaled 1
  exact Real.smoothTransition.one_of_one_le hargument

theorem Real.quantitativeLogarithmicBlockCutoff_eq_zero_of_le_one_div_three
    {a b : ℤ} (ha : 1 ≤ a) {x : ℝ}
    (hx : x ≤ 1 / 3) :
    Real.quantitativeLogarithmicBlockCutoff a b x = 0 := by
  unfold Real.quantitativeLogarithmicBlockCutoff
  have ha_real : (1 : ℝ) ≤ (a : ℝ) := by
    calc
      (1 : ℝ) = ((1 : ℤ) : ℝ) := Int.cast_one.symm
      _ ≤ (a : ℝ) := Int.cast_le.mpr ha
  have hleft_margin : (1 / 3 : ℝ) ≤ (a : ℝ) - 1 / 3 := by
    have htwothirds_nonneg : (0 : ℝ) ≤ 2 / 3 :=
      div_nonneg (Nat.cast_nonneg 2) (Nat.cast_nonneg 3)
    calc
      (1 / 3 : ℝ) ≤ 1 - 1 / 3 := by
        have hsum : (1 / 3 : ℝ) + 1 / 3 ≤ 1 := by
          calc
            (1 / 3 : ℝ) + 1 / 3 = (1 + 1) / 3 := (add_div 1 1 3).symm
            _ = 2 / 3 := congrArg (fun value : ℝ => value / 3)
              one_add_one_eq_two
            _ ≤ 1 := Real.two_div_three_le_one
        exact (le_sub_iff_add_le).mpr hsum
      _ ≤ (a : ℝ) - 1 / 3 :=
        sub_le_sub_right ha_real (1 / 3)
  have hleft : x ≤ (a : ℝ) - 1 / 3 :=
    le_trans hx hleft_margin
  have hzero : Real.quantitativeLogarithmicLeftCutoff a x = 0 :=
    Real.quantitativeLogarithmicLeftCutoff_eq_zero_of_le hleft
  exact
    Eq.trans
      (congrArg
        (fun value : ℝ => value * Real.quantitativeLogarithmicRightCutoff b x)
        hzero)
      (zero_mul (Real.quantitativeLogarithmicRightCutoff b x))

theorem Real.quantitativeLogarithmicRightCutoff_eq_zero_of_le
    {b : ℤ} {x : ℝ}
    (hx : (b : ℝ) + 1 / 3 ≤ x) :
    Real.quantitativeLogarithmicRightCutoff b x = 0 := by
  unfold Real.quantitativeLogarithmicRightCutoff
  have hsub : (b : ℝ) - x ≤ (b : ℝ) - ((b : ℝ) + 1 / 3) :=
    sub_le_sub_left hx (b : ℝ)
  have hendpoint : (b : ℝ) - ((b : ℝ) + 1 / 3) = -(1 / 3) := by
    calc
      (b : ℝ) - ((b : ℝ) + 1 / 3) = (b : ℝ) - (b : ℝ) - 1 / 3 :=
        sub_add_eq_sub_sub (b : ℝ) (b : ℝ) (1 / 3)
      _ = 0 - 1 / 3 := congrArg (fun value : ℝ => value - 1 / 3) (sub_self (b : ℝ))
      _ = -(1 / 3) := zero_sub (1 / 3)
  have hscaled :
      3 * ((b : ℝ) - x) ≤ 3 * (-(1 / 3)) :=
    mul_le_mul_of_nonneg_left
      (Eq.subst
        (motive := fun right : ℝ => (b : ℝ) - x ≤ right)
        hendpoint
        hsub)
      zero_le_three
  have hargument : 3 * ((b : ℝ) - x) + 1 ≤ 0 := by
    calc
      3 * ((b : ℝ) - x) + 1 ≤ 3 * (-(1 / 3)) + 1 :=
        add_le_add_right hscaled 1
      _ = 0 := Real.three_mul_neg_one_div_three_add_one_eq_zero
  exact Real.smoothTransition.zero_of_nonpos hargument

theorem Real.quantitativeLogarithmicRightCutoff_eq_one_of_le
    {b : ℤ} {x : ℝ}
    (hx : x ≤ (b : ℝ)) :
    Real.quantitativeLogarithmicRightCutoff b x = 1 := by
  unfold Real.quantitativeLogarithmicRightCutoff
  have hsub : 0 ≤ (b : ℝ) - x := sub_nonneg.mpr hx
  have hscaled : 0 ≤ 3 * ((b : ℝ) - x) :=
    mul_nonneg zero_le_three hsub
  have hargument : (1 : ℝ) ≤ 3 * ((b : ℝ) - x) + 1 := by
    calc
      (1 : ℝ) = 0 + 1 := (zero_add 1).symm
      _ ≤ 3 * ((b : ℝ) - x) + 1 := add_le_add_right hscaled 1
  exact Real.smoothTransition.one_of_one_le hargument

theorem Real.quantitativeLogarithmicLeftCutoff_nonneg
    (a : ℤ) (x : ℝ) :
    0 ≤ Real.quantitativeLogarithmicLeftCutoff a x := by
  unfold Real.quantitativeLogarithmicLeftCutoff
  exact Real.smoothTransition.nonneg _

theorem Real.quantitativeLogarithmicRightCutoff_nonneg
    (b : ℤ) (x : ℝ) :
    0 ≤ Real.quantitativeLogarithmicRightCutoff b x := by
  unfold Real.quantitativeLogarithmicRightCutoff
  exact Real.smoothTransition.nonneg _

theorem Real.quantitativeLogarithmicLeftCutoff_le_one
    (a : ℤ) (x : ℝ) :
    Real.quantitativeLogarithmicLeftCutoff a x ≤ 1 := by
  unfold Real.quantitativeLogarithmicLeftCutoff
  exact Real.smoothTransition.le_one _

theorem Real.quantitativeLogarithmicRightCutoff_le_one
    (b : ℤ) (x : ℝ) :
    Real.quantitativeLogarithmicRightCutoff b x ≤ 1 := by
  unfold Real.quantitativeLogarithmicRightCutoff
  exact Real.smoothTransition.le_one _

theorem Real.quantitativeLogarithmicBlockCutoff_nonneg
    (a b : ℤ) (x : ℝ) :
    0 ≤ Real.quantitativeLogarithmicBlockCutoff a b x := by
  unfold Real.quantitativeLogarithmicBlockCutoff
  exact
    mul_nonneg
      (Real.quantitativeLogarithmicLeftCutoff_nonneg a x)
      (Real.quantitativeLogarithmicRightCutoff_nonneg b x)

theorem Real.quantitativeLogarithmicBlockCutoff_le_one
    (a b : ℤ) (x : ℝ) :
    Real.quantitativeLogarithmicBlockCutoff a b x ≤ 1 := by
  unfold Real.quantitativeLogarithmicBlockCutoff
  have hleft_nonneg := Real.quantitativeLogarithmicLeftCutoff_nonneg a x
  have hright_nonneg := Real.quantitativeLogarithmicRightCutoff_nonneg b x
  have hleft_one := Real.quantitativeLogarithmicLeftCutoff_le_one a x
  have hright_one := Real.quantitativeLogarithmicRightCutoff_le_one b x
  have hfirst :
      Real.quantitativeLogarithmicLeftCutoff a x *
          Real.quantitativeLogarithmicRightCutoff b x ≤
        1 * Real.quantitativeLogarithmicRightCutoff b x :=
    mul_le_mul_of_nonneg_right hleft_one hright_nonneg
  have hsecond :
      1 * Real.quantitativeLogarithmicRightCutoff b x ≤ 1 * 1 :=
    mul_le_mul_of_nonneg_left hright_one zero_le_one
  exact le_trans hfirst (le_trans hsecond (le_of_eq (one_mul (1 : ℝ))))

theorem Real.contDiff_quantitativeLogarithmicLeftCutoff
    (a : ℤ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (Real.quantitativeLogarithmicLeftCutoff a) := by
  unfold Real.quantitativeLogarithmicLeftCutoff
  have haffine :
      ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : ℝ => 3 * (x - (a : ℝ)) + 1) :=
    (contDiff_const.mul (contDiff_id.sub contDiff_const)).add contDiff_const
  exact Real.smoothTransition.contDiff.comp haffine

theorem Real.contDiff_quantitativeLogarithmicRightCutoff
    (b : ℤ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (Real.quantitativeLogarithmicRightCutoff b) := by
  unfold Real.quantitativeLogarithmicRightCutoff
  have haffine :
      ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : ℝ => 3 * ((b : ℝ) - x) + 1) :=
    (contDiff_const.mul (contDiff_const.sub contDiff_id)).add contDiff_const
  exact Real.smoothTransition.contDiff.comp haffine

theorem Real.contDiff_quantitativeLogarithmicBlockCutoff
    (a b : ℤ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (Real.quantitativeLogarithmicBlockCutoff a b) := by
  unfold Real.quantitativeLogarithmicBlockCutoff
  exact
    (Real.contDiff_quantitativeLogarithmicLeftCutoff a).mul
      (Real.contDiff_quantitativeLogarithmicRightCutoff b)

theorem Real.quantitativeLogarithmicBlockCutoff_eq_zero_of_left
    (a b : ℤ) {x : ℝ}
    (hx : x ≤ (a : ℝ) - 1 / 3) :
    Real.quantitativeLogarithmicBlockCutoff a b x = 0 := by
  unfold Real.quantitativeLogarithmicBlockCutoff
  exact
    Eq.trans
      (congrArg
        (fun value : ℝ => value * Real.quantitativeLogarithmicRightCutoff b x)
        (Real.quantitativeLogarithmicLeftCutoff_eq_zero_of_le hx))
      (zero_mul (Real.quantitativeLogarithmicRightCutoff b x))

theorem Real.quantitativeLogarithmicBlockCutoff_eq_zero_of_right
    (a b : ℤ) {x : ℝ}
    (hx : (b : ℝ) + 1 / 3 ≤ x) :
    Real.quantitativeLogarithmicBlockCutoff a b x = 0 := by
  unfold Real.quantitativeLogarithmicBlockCutoff
  exact
    Eq.trans
      (congrArg
        (fun value : ℝ => Real.quantitativeLogarithmicLeftCutoff a x * value)
        (Real.quantitativeLogarithmicRightCutoff_eq_zero_of_le hx))
      (mul_zero (Real.quantitativeLogarithmicLeftCutoff a x))

theorem Real.quantitativeLogarithmicBlockCutoff_eq_one_of_mem_Icc
    {a b : ℤ} {x : ℝ}
    (hx : x ∈ Set.Icc (a : ℝ) (b : ℝ)) :
    Real.quantitativeLogarithmicBlockCutoff a b x = 1 := by
  unfold Real.quantitativeLogarithmicBlockCutoff
  have hleft : Real.quantitativeLogarithmicLeftCutoff a x = 1 :=
    Real.quantitativeLogarithmicLeftCutoff_eq_one_of_le hx.1
  have hright : Real.quantitativeLogarithmicRightCutoff b x = 1 :=
    Real.quantitativeLogarithmicRightCutoff_eq_one_of_le hx.2
  calc
    Real.quantitativeLogarithmicLeftCutoff a x *
        Real.quantitativeLogarithmicRightCutoff b x =
        1 * Real.quantitativeLogarithmicRightCutoff b x :=
      congrArg (fun value : ℝ => value * Real.quantitativeLogarithmicRightCutoff b x) hleft
    _ = 1 * 1 := congrArg (fun value : ℝ => 1 * value) hright
    _ = 1 := one_mul 1

theorem Real.support_quantitativeLogarithmicBlockCutoff_subset_openCollar
    (a b : ℤ) :
    Function.support (Real.quantitativeLogarithmicBlockCutoff a b) ⊆
      Set.Ioo ((a : ℝ) - 1 / 3) ((b : ℝ) + 1 / 3) := by
  intro x hx
  have hleft : (a : ℝ) - 1 / 3 < x := by
    by_contra hnot
    have hzero := Real.quantitativeLogarithmicBlockCutoff_eq_zero_of_left a b (le_of_not_gt hnot)
    exact hx hzero
  have hright : x < (b : ℝ) + 1 / 3 := by
    by_contra hnot
    have hzero := Real.quantitativeLogarithmicBlockCutoff_eq_zero_of_right a b (le_of_not_gt hnot)
    exact hx hzero
  exact And.intro hleft hright

theorem Real.hasCompactSupport_quantitativeLogarithmicBlockCutoff
    (a b : ℤ) :
    HasCompactSupport (Real.quantitativeLogarithmicBlockCutoff a b) := by
  have hopen := Real.support_quantitativeLogarithmicBlockCutoff_subset_openCollar a b
  have hclosed :
      Function.support (Real.quantitativeLogarithmicBlockCutoff a b) ⊆
        Set.Icc ((a : ℝ) - 1 / 3) ((b : ℝ) + 1 / 3) :=
    Set.Subset.trans hopen (fun x hx => And.intro (le_of_lt hx.1) (le_of_lt hx.2))
  exact HasCompactSupport.of_support_subset_isCompact isCompact_Icc hclosed

theorem Real.quantitativeLogarithmicBlockCutoff_eq_one_of_mem_Icc_int
    {a b n : ℤ}
    (hn : n ∈ Finset.Icc a b) :
    Real.quantitativeLogarithmicBlockCutoff a b (n : ℝ) = 1 := by
  have hbounds := Finset.mem_Icc.mp hn
  exact
    Real.quantitativeLogarithmicBlockCutoff_eq_one_of_mem_Icc
      (And.intro (Int.cast_le.mpr hbounds.1) (Int.cast_le.mpr hbounds.2))

theorem Real.quantitativeLogarithmicBlockCutoff_eq_zero_of_lt_left
    {a b n : ℤ}
    (hna : n < a) :
    Real.quantitativeLogarithmicBlockCutoff a b (n : ℝ) = 0 := by
  have hgap : n + 1 ≤ a := Int.add_one_le_iff.mpr hna
  have hgap_real : (n : ℝ) + 1 ≤ (a : ℝ) := by
    calc
      (n : ℝ) + 1 = (n : ℝ) + ((1 : ℤ) : ℝ) :=
        congrArg (fun value : ℝ => (n : ℝ) + value) Int.cast_one.symm
      _ = ((n + 1 : ℤ) : ℝ) := (Int.cast_add n 1).symm
      _ ≤ (a : ℝ) := Int.cast_le.mpr hgap
  have hmargin : (n : ℝ) ≤ (a : ℝ) - 1 / 3 := by
    calc
      (n : ℝ) ≤ (a : ℝ) - 1 := (le_sub_iff_add_le).mpr hgap_real
      _ ≤ (a : ℝ) - 1 / 3 :=
        sub_le_sub_left Real.one_div_three_le_one (a : ℝ)
  exact Real.quantitativeLogarithmicBlockCutoff_eq_zero_of_left a b hmargin

theorem Real.quantitativeLogarithmicBlockCutoff_eq_zero_of_lt_right
    {a b n : ℤ}
    (hbn : b < n) :
    Real.quantitativeLogarithmicBlockCutoff a b (n : ℝ) = 0 := by
  have hgap : b + 1 ≤ n := Int.add_one_le_iff.mpr hbn
  have hgap_real : (b : ℝ) + 1 ≤ (n : ℝ) := by
    calc
      (b : ℝ) + 1 = (b : ℝ) + ((1 : ℤ) : ℝ) :=
        congrArg (fun value : ℝ => (b : ℝ) + value) Int.cast_one.symm
      _ = ((b + 1 : ℤ) : ℝ) := (Int.cast_add b 1).symm
      _ ≤ (n : ℝ) := Int.cast_le.mpr hgap
  have hmargin : (b : ℝ) + 1 / 3 ≤ (n : ℝ) := by
    calc
      (b : ℝ) + 1 / 3 ≤ (b : ℝ) + 1 :=
        add_le_add_left Real.one_div_three_le_one (b : ℝ)
      _ ≤ (n : ℝ) := hgap_real
  exact Real.quantitativeLogarithmicBlockCutoff_eq_zero_of_right a b hmargin

theorem Real.quantitativeLogarithmicBlockCutoff_eq_zero_of_not_mem_Icc
    {a b n : ℤ}
    (hn : n ∉ Finset.Icc a b) :
    Real.quantitativeLogarithmicBlockCutoff a b (n : ℝ) = 0 := by
  have hnot_bounds : ¬ (a ≤ n ∧ n ≤ b) :=
    fun hbounds => hn (Finset.mem_Icc.mpr hbounds)
  exact
    Or.elim
      (not_and_or.mp hnot_bounds)
      (fun hleft =>
        Real.quantitativeLogarithmicBlockCutoff_eq_zero_of_lt_left
          (lt_of_not_ge hleft))
      (fun hright =>
        Real.quantitativeLogarithmicBlockCutoff_eq_zero_of_lt_right
          (lt_of_not_ge hright))

end
end LFunctions
end Boundary
