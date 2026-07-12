import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.IntegerBlockCutoff
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Quantitative smooth cutoffs for integer blocks

The older integer-block cutoff is obtained from the abstract `ContDiffBump`
interface.  It supplies support and smoothness but has no numerical derivative
control.  This owner instead starts from `Real.smoothTransition`, an explicit
smooth step, so its two transition collars have a fixed scale independent of
the block length.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

def Real.quantitativeIntegerBlockLeftCutoff
    (a : ℤ) (x : ℝ) : ℝ :=
  Real.smoothTransition (x - (a : ℝ) + 1)

def Real.quantitativeIntegerBlockRightCutoff
    (b : ℤ) (x : ℝ) : ℝ :=
  Real.smoothTransition ((b : ℝ) - x + 1)

def Real.quantitativeIntegerBlockCutoff
    (a b : ℤ) (x : ℝ) : ℝ :=
  Real.quantitativeIntegerBlockLeftCutoff a x *
    Real.quantitativeIntegerBlockRightCutoff b x

theorem Real.quantitativeIntegerBlockLeftCutoff_nonneg
    (a : ℤ) (x : ℝ) :
    0 ≤ Real.quantitativeIntegerBlockLeftCutoff a x := by
  unfold Real.quantitativeIntegerBlockLeftCutoff
  exact Real.smoothTransition.nonneg _

theorem Real.quantitativeIntegerBlockRightCutoff_nonneg
    (b : ℤ) (x : ℝ) :
    0 ≤ Real.quantitativeIntegerBlockRightCutoff b x := by
  unfold Real.quantitativeIntegerBlockRightCutoff
  exact Real.smoothTransition.nonneg _

theorem Real.quantitativeIntegerBlockLeftCutoff_le_one
    (a : ℤ) (x : ℝ) :
    Real.quantitativeIntegerBlockLeftCutoff a x ≤ 1 := by
  unfold Real.quantitativeIntegerBlockLeftCutoff
  exact Real.smoothTransition.le_one _

theorem Real.quantitativeIntegerBlockRightCutoff_le_one
    (b : ℤ) (x : ℝ) :
    Real.quantitativeIntegerBlockRightCutoff b x ≤ 1 := by
  unfold Real.quantitativeIntegerBlockRightCutoff
  exact Real.smoothTransition.le_one _

theorem Real.quantitativeIntegerBlockCutoff_nonneg
    (a b : ℤ) (x : ℝ) :
    0 ≤ Real.quantitativeIntegerBlockCutoff a b x := by
  unfold Real.quantitativeIntegerBlockCutoff
  exact
    mul_nonneg
      (Real.quantitativeIntegerBlockLeftCutoff_nonneg a x)
      (Real.quantitativeIntegerBlockRightCutoff_nonneg b x)

theorem Real.quantitativeIntegerBlockCutoff_le_one
    (a b : ℤ) (x : ℝ) :
    Real.quantitativeIntegerBlockCutoff a b x ≤ 1 := by
  unfold Real.quantitativeIntegerBlockCutoff
  have hleft_nonneg :
      0 ≤ Real.quantitativeIntegerBlockLeftCutoff a x :=
    Real.quantitativeIntegerBlockLeftCutoff_nonneg a x
  have hright_nonneg :
      0 ≤ Real.quantitativeIntegerBlockRightCutoff b x :=
    Real.quantitativeIntegerBlockRightCutoff_nonneg b x
  have hleft_one :
      Real.quantitativeIntegerBlockLeftCutoff a x ≤ 1 :=
    Real.quantitativeIntegerBlockLeftCutoff_le_one a x
  have hright_one :
      Real.quantitativeIntegerBlockRightCutoff b x ≤ 1 :=
    Real.quantitativeIntegerBlockRightCutoff_le_one b x
  have hfirst :
      Real.quantitativeIntegerBlockLeftCutoff a x *
          Real.quantitativeIntegerBlockRightCutoff b x ≤
        1 * Real.quantitativeIntegerBlockRightCutoff b x :=
    mul_le_mul_of_nonneg_right hleft_one hright_nonneg
  have hsecond :
      1 * Real.quantitativeIntegerBlockRightCutoff b x ≤ 1 * 1 :=
    mul_le_mul_of_nonneg_left hright_one zero_le_one
  exact
    le_trans hfirst
      (le_trans hsecond (le_of_eq (one_mul (1 : ℝ))))

theorem Real.contDiff_quantitativeIntegerBlockLeftCutoff
    (a : ℤ) :
    ContDiff ℝ ∞ (Real.quantitativeIntegerBlockLeftCutoff a) := by
  unfold Real.quantitativeIntegerBlockLeftCutoff
  have haffine :
      ContDiff ℝ ∞ (fun x : ℝ => x - (a : ℝ) + 1) :=
    (contDiff_id.sub contDiff_const).add contDiff_const
  exact Real.smoothTransition.contDiff.comp haffine

theorem Real.contDiff_quantitativeIntegerBlockRightCutoff
    (b : ℤ) :
    ContDiff ℝ ∞ (Real.quantitativeIntegerBlockRightCutoff b) := by
  unfold Real.quantitativeIntegerBlockRightCutoff
  have haffine :
      ContDiff ℝ ∞ (fun x : ℝ => (b : ℝ) - x + 1) :=
    (contDiff_const.sub contDiff_id).add contDiff_const
  exact Real.smoothTransition.contDiff.comp haffine

theorem Real.contDiff_quantitativeIntegerBlockCutoff
    (a b : ℤ) :
    ContDiff ℝ ∞ (Real.quantitativeIntegerBlockCutoff a b) := by
  unfold Real.quantitativeIntegerBlockCutoff
  exact
    (Real.contDiff_quantitativeIntegerBlockLeftCutoff a).mul
      (Real.contDiff_quantitativeIntegerBlockRightCutoff b)

theorem Real.quantitativeIntegerBlockLeftCutoff_eq_zero_of_le
    {a : ℤ} {x : ℝ}
    (hx : x ≤ (a : ℝ) - 1) :
    Real.quantitativeIntegerBlockLeftCutoff a x = 0 := by
  unfold Real.quantitativeIntegerBlockLeftCutoff
  have hsub : x - (a : ℝ) ≤ ((a : ℝ) - 1) - (a : ℝ) :=
    sub_le_sub_right hx (a : ℝ)
  have hargument : x - (a : ℝ) + 1 ≤ 0 := by
    calc
      x - (a : ℝ) + 1 ≤ ((a : ℝ) - 1) - (a : ℝ) + 1 :=
        add_le_add_right hsub 1
      _ = ((a : ℝ) - 1) - ((a : ℝ) - 1) :=
        sub_add_eq_sub_sub ((a : ℝ) - 1) (a : ℝ) 1
      _ = 0 := sub_self ((a : ℝ) - 1)
  exact Real.smoothTransition.zero_of_nonpos hargument

theorem Real.quantitativeIntegerBlockRightCutoff_eq_zero_of_le
    {b : ℤ} {x : ℝ}
    (hx : (b : ℝ) + 1 ≤ x) :
    Real.quantitativeIntegerBlockRightCutoff b x = 0 := by
  unfold Real.quantitativeIntegerBlockRightCutoff
  have hsub : (b : ℝ) - x ≤ (b : ℝ) - ((b : ℝ) + 1) :=
    sub_le_sub_left hx (b : ℝ)
  have hargument : (b : ℝ) - x + 1 ≤ 0 := by
    calc
      (b : ℝ) - x + 1 ≤ (b : ℝ) - ((b : ℝ) + 1) + 1 :=
        add_le_add_right hsub 1
      _ = (b : ℝ) - (((b : ℝ) + 1) - 1) := by
        exact sub_add_eq_sub_sub (b : ℝ) ((b : ℝ) + 1) 1
      _ = (b : ℝ) - (b : ℝ) :=
        congrArg (fun value : ℝ => (b : ℝ) - value)
          (add_sub_cancel (b : ℝ) 1)
      _ = 0 := sub_self (b : ℝ)
  exact Real.smoothTransition.zero_of_nonpos hargument

theorem Real.quantitativeIntegerBlockLeftCutoff_eq_one_of_le
    {a : ℤ} {x : ℝ}
    (hx : (a : ℝ) ≤ x) :
    Real.quantitativeIntegerBlockLeftCutoff a x = 1 := by
  unfold Real.quantitativeIntegerBlockLeftCutoff
  have hsub : 0 ≤ x - (a : ℝ) :=
    sub_nonneg.mpr hx
  have hargument : (1 : ℝ) ≤ x - (a : ℝ) + 1 := by
    calc
      (1 : ℝ) = 0 + 1 := (zero_add 1).symm
      _ ≤ x - (a : ℝ) + 1 := add_le_add_right hsub 1
  exact Real.smoothTransition.one_of_one_le hargument

theorem Real.quantitativeIntegerBlockRightCutoff_eq_one_of_le
    {b : ℤ} {x : ℝ}
    (hx : x ≤ (b : ℝ)) :
    Real.quantitativeIntegerBlockRightCutoff b x = 1 := by
  unfold Real.quantitativeIntegerBlockRightCutoff
  have hsub : 0 ≤ (b : ℝ) - x :=
    sub_nonneg.mpr hx
  have hargument : (1 : ℝ) ≤ (b : ℝ) - x + 1 := by
    calc
      (1 : ℝ) = 0 + 1 := (zero_add 1).symm
      _ ≤ (b : ℝ) - x + 1 := add_le_add_right hsub 1
  exact Real.smoothTransition.one_of_one_le hargument

theorem Real.quantitativeIntegerBlockCutoff_eq_zero_of_left
    (a b : ℤ) {x : ℝ}
    (hx : x ≤ (a : ℝ) - 1) :
    Real.quantitativeIntegerBlockCutoff a b x = 0 := by
  unfold Real.quantitativeIntegerBlockCutoff
  exact
    Eq.trans
      (congrArg
        (fun value : ℝ => value * Real.quantitativeIntegerBlockRightCutoff b x)
        (Real.quantitativeIntegerBlockLeftCutoff_eq_zero_of_le hx))
      (zero_mul (Real.quantitativeIntegerBlockRightCutoff b x))

theorem Real.quantitativeIntegerBlockCutoff_eq_zero_of_right
    (a b : ℤ) {x : ℝ}
    (hx : (b : ℝ) + 1 ≤ x) :
    Real.quantitativeIntegerBlockCutoff a b x = 0 := by
  unfold Real.quantitativeIntegerBlockCutoff
  exact
    Eq.trans
      (congrArg
        (fun value : ℝ => Real.quantitativeIntegerBlockLeftCutoff a x * value)
        (Real.quantitativeIntegerBlockRightCutoff_eq_zero_of_le hx))
      (mul_zero (Real.quantitativeIntegerBlockLeftCutoff a x))

theorem Real.quantitativeIntegerBlockCutoff_eq_one_of_mem_Icc
    {a b : ℤ} {x : ℝ}
    (hx : x ∈ Set.Icc (a : ℝ) (b : ℝ)) :
    Real.quantitativeIntegerBlockCutoff a b x = 1 := by
  unfold Real.quantitativeIntegerBlockCutoff
  have hleft : Real.quantitativeIntegerBlockLeftCutoff a x = 1 :=
    Real.quantitativeIntegerBlockLeftCutoff_eq_one_of_le hx.1
  have hright : Real.quantitativeIntegerBlockRightCutoff b x = 1 :=
    Real.quantitativeIntegerBlockRightCutoff_eq_one_of_le hx.2
  calc
    Real.quantitativeIntegerBlockLeftCutoff a x *
        Real.quantitativeIntegerBlockRightCutoff b x =
        1 * Real.quantitativeIntegerBlockRightCutoff b x :=
      congrArg (fun value : ℝ => value * Real.quantitativeIntegerBlockRightCutoff b x)
        hleft
    _ = 1 * 1 :=
      congrArg (fun value : ℝ => 1 * value) hright
    _ = 1 := one_mul 1

theorem Real.support_quantitativeIntegerBlockCutoff_subset_openCollar
    (a b : ℤ) :
    Function.support (Real.quantitativeIntegerBlockCutoff a b) ⊆
      Set.Ioo ((a : ℝ) - 1) ((b : ℝ) + 1) := by
  intro x hx
  have hleft : (a : ℝ) - 1 < x := by
    by_contra hnot
    have hle : x ≤ (a : ℝ) - 1 :=
      le_of_not_gt hnot
    have hzero : Real.quantitativeIntegerBlockCutoff a b x = 0 :=
      Real.quantitativeIntegerBlockCutoff_eq_zero_of_left a b hle
    exact hx hzero
  have hright : x < (b : ℝ) + 1 := by
    by_contra hnot
    have hle : (b : ℝ) + 1 ≤ x :=
      le_of_not_gt hnot
    have hzero : Real.quantitativeIntegerBlockCutoff a b x = 0 :=
      Real.quantitativeIntegerBlockCutoff_eq_zero_of_right a b hle
    exact hx hzero
  exact And.intro hleft hright

theorem Real.support_quantitativeIntegerBlockCutoff_subset_closedCollar
    (a b : ℤ) :
    Function.support (Real.quantitativeIntegerBlockCutoff a b) ⊆
      Set.Icc ((a : ℝ) - 1) ((b : ℝ) + 1) := by
  have hopen :=
    Real.support_quantitativeIntegerBlockCutoff_subset_openCollar a b
  exact
    Set.Subset.trans hopen
      (fun x hx => And.intro (le_of_lt hx.1) (le_of_lt hx.2))

theorem Real.hasCompactSupport_quantitativeIntegerBlockCutoff
    (a b : ℤ) :
    HasCompactSupport (Real.quantitativeIntegerBlockCutoff a b) := by
  exact
    HasCompactSupport.of_support_subset_isCompact
      (Set.isCompact_Icc)
      (Real.support_quantitativeIntegerBlockCutoff_subset_closedCollar a b)

theorem Real.quantitativeIntegerBlockCutoff_eq_zero_of_nonpos
    {a b : ℤ} (ha : 1 ≤ a) {x : ℝ} (hx : x ≤ 0) :
    Real.quantitativeIntegerBlockCutoff a b x = 0 := by
  have ha_real : (1 : ℝ) ≤ (a : ℝ) :=
    Int.cast_le.mpr ha
  have hzero_le_margin : (0 : ℝ) ≤ (a : ℝ) - 1 :=
    sub_nonneg.mpr ha_real
  have hleft : x ≤ (a : ℝ) - 1 :=
    le_trans hx hzero_le_margin
  exact Real.quantitativeIntegerBlockCutoff_eq_zero_of_left a b hleft

theorem Real.quantitativeIntegerBlockCutoff_eq_one_of_mem_Icc_int
    {a b n : ℤ}
    (hn : n ∈ Finset.Icc a b) :
    Real.quantitativeIntegerBlockCutoff a b (n : ℝ) = 1 := by
  have hbounds := Finset.mem_Icc.mp hn
  exact
    Real.quantitativeIntegerBlockCutoff_eq_one_of_mem_Icc
      (And.intro (Int.cast_le.mpr hbounds.1) (Int.cast_le.mpr hbounds.2))

theorem Real.quantitativeIntegerBlockCutoff_eq_zero_of_lt_left
    {a b n : ℤ}
    (hna : n < a) :
    Real.quantitativeIntegerBlockCutoff a b (n : ℝ) = 0 := by
  have hgap : n + 1 ≤ a :=
    Int.add_one_le_iff.mpr hna
  have hgap_real : (n : ℝ) + 1 ≤ (a : ℝ) := by
    exact
      (Int.cast_add n 1).symm.trans
        (Int.cast_le.mpr hgap)
  have hleft : (n : ℝ) ≤ (a : ℝ) - 1 :=
    le_sub_iff_add_le.mpr hgap_real
  exact Real.quantitativeIntegerBlockCutoff_eq_zero_of_left a b hleft

theorem Real.quantitativeIntegerBlockCutoff_eq_zero_of_lt_right
    {a b n : ℤ}
    (hbn : b < n) :
    Real.quantitativeIntegerBlockCutoff a b (n : ℝ) = 0 := by
  have hgap : b + 1 ≤ n :=
    Int.add_one_le_iff.mpr hbn
  have hgap_real : (b : ℝ) + 1 ≤ (n : ℝ) := by
    exact
      (Int.cast_add b 1).symm.trans
        (Int.cast_le.mpr hgap)
  exact Real.quantitativeIntegerBlockCutoff_eq_zero_of_right a b hgap_real

theorem Real.quantitativeIntegerBlockCutoff_eq_zero_of_not_mem_Icc
    {a b n : ℤ}
    (hn : n ∉ Finset.Icc a b) :
    Real.quantitativeIntegerBlockCutoff a b (n : ℝ) = 0 := by
  have hnot_bounds : ¬ (a ≤ n ∧ n ≤ b) :=
    fun hbounds => hn (Finset.mem_Icc.mpr hbounds)
  exact
    Or.elim
      (not_and_or.mp hnot_bounds)
      (fun hleft =>
        Real.quantitativeIntegerBlockCutoff_eq_zero_of_lt_left
          (lt_of_not_ge hleft))
      (fun hright =>
        Real.quantitativeIntegerBlockCutoff_eq_zero_of_lt_right
          (lt_of_not_ge hright))

end
end LFunctions
end Boundary
