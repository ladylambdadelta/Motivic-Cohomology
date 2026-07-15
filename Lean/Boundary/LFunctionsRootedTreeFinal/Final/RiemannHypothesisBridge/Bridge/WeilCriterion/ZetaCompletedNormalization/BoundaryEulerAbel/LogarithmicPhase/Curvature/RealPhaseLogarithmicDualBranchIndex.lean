import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicDualBranchCutCardinality

/-!
# Canonical centered branch index

For a negative increment `v`, the nearest nonnegative angular-frequency index
is

`floor (|v|/(2*pi) + 1/2)`.

Adding `2*pi` times this index places `v` in the centered interval bounded by
`-pi` and `pi`.  The midpoint levels `(2*q+1)*pi` are precisely the points at
which this branch index changes.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Real.centeredAngularBranchIndex
    (v : ℝ) : ℕ :=
  ⌊|v| / (2 * Real.pi) + 1 / 2⌋₊

def Complex.logarithmicPhaseDualContinuousBranchIndex
    (t h x : ℝ) : ℕ :=
  Real.centeredAngularBranchIndex
    (Complex.logarithmicPhaseDualContinuousIncrement t h x)

def Complex.logarithmicPhaseDualDiscreteBranchIndex
    (t : ℝ) (h n : ℕ) : ℕ :=
  Real.centeredAngularBranchIndex
    (Complex.logarithmicPhaseDualShiftedIncrement t h n)

theorem Real.centeredAngularBranchIndex_nat_eq
    (v : ℝ) :
    ((Real.centeredAngularBranchIndex v : ℕ) : ℝ) =
      (⌊|v| / (2 * Real.pi) + 1 / 2⌋₊ : ℕ) := by
  rfl

theorem Real.centeredAngularBranchIndex_cast_le
    (v : ℝ) :
    ((Real.centeredAngularBranchIndex v : ℕ) : ℝ) ≤
      |v| / (2 * Real.pi) + 1 / 2 := by
  unfold Real.centeredAngularBranchIndex
  have hnonneg : 0 ≤ |v| / (2 * Real.pi) + 1 / 2 := by
    exact add_nonneg
      (div_nonneg (abs_nonneg _) (le_of_lt Complex.two_mul_pi_pos))
      (div_nonneg zero_le_one (le_of_lt zero_lt_two))
  exact Nat.floor_le hnonneg

theorem Real.centeredAngularBranchIndex_ratio_lt_succ
    (v : ℝ) :
    |v| / (2 * Real.pi) + 1 / 2 <
      ((Real.centeredAngularBranchIndex v : ℕ) : ℝ) + 1 := by
  unfold Real.centeredAngularBranchIndex
  exact Nat.lt_floor_add_one _

theorem Real.two_pi_mul_branch_le_abs_add_pi
    (v : ℝ) :
    2 * Real.pi * ((Real.centeredAngularBranchIndex v : ℕ) : ℝ) ≤
      |v| + Real.pi := by
  have hbase := Real.centeredAngularBranchIndex_cast_le v
  have hscaled := mul_le_mul_of_nonneg_left hbase
    (le_of_lt Complex.two_mul_pi_pos)
  have hhalf : (2 * Real.pi) * (1 / 2 : ℝ) = Real.pi := by
    calc
      (2 * Real.pi) * (1 / 2 : ℝ) =
          Real.pi * (2 * (1 / 2 : ℝ)) := by
            exact Eq.trans
              (mul_assoc 2 Real.pi (1 / 2 : ℝ)).symm
              (congrArg (fun z : ℝ => z * (1 / 2 : ℝ))
                (mul_comm 2 Real.pi))
      _ = Real.pi := by exact rfl
  have hratio :
      (2 * Real.pi) * (|v| / (2 * Real.pi)) = |v| := by
    exact mul_div_cancel₀ |v| (ne_of_gt Complex.two_mul_pi_pos)
  exact le_trans
    (Eq.subst (motive := fun z : ℝ => z ≤ _)
      (mul_comm (2 * Real.pi)
        ((Real.centeredAngularBranchIndex v : ℕ) : ℝ)) hscaled)
    (le_of_eq
      (Eq.trans
        (mul_add (2 * Real.pi)
          (|v| / (2 * Real.pi)) (1 / 2 : ℝ))
        (congrArg₂ (fun x y : ℝ => x + y) hratio hhalf)))

theorem Real.abs_lt_two_pi_mul_branch_add_pi
    (v : ℝ) :
    |v| <
      2 * Real.pi * ((Real.centeredAngularBranchIndex v : ℕ) : ℝ) + Real.pi := by
  have hbase := Real.centeredAngularBranchIndex_ratio_lt_succ v
  have hscaled := mul_lt_mul_of_pos_left hbase Complex.two_mul_pi_pos
  have hhalf : (2 * Real.pi) * (1 / 2 : ℝ) = Real.pi := by
    exact Eq.trans
      (mul_assoc 2 Real.pi (1 / 2 : ℝ)).symm
      (Eq.trans
        (congrArg (fun z : ℝ => z * (1 / 2 : ℝ))
          (mul_comm 2 Real.pi))
        (by exact rfl))
  have hratio :
      (2 * Real.pi) * (|v| / (2 * Real.pi)) = |v| :=
    mul_div_cancel₀ |v| (ne_of_gt Complex.two_mul_pi_pos)
  have hleft :
      (2 * Real.pi) * (|v| / (2 * Real.pi) + 1 / 2) =
        |v| + Real.pi := by
    exact Eq.trans (mul_add _ _ _)
      (congrArg₂ (fun x y : ℝ => x + y) hratio hhalf)
  have hright :
      (2 * Real.pi) *
          (((Real.centeredAngularBranchIndex v : ℕ) : ℝ) + 1) =
        2 * Real.pi * ((Real.centeredAngularBranchIndex v : ℕ) : ℝ) +
          2 * Real.pi :=
    mul_add _ _ _
  have haddPi :
      |v| + Real.pi <
        2 * Real.pi * ((Real.centeredAngularBranchIndex v : ℕ) : ℝ) +
          2 * Real.pi :=
    Eq.subst (motive := fun z : ℝ => z < _)
      hleft.symm
      (Eq.subst (motive := fun z : ℝ => _ < z) hright.symm hscaled)
  have hpiPos := Real.pi_pos
  exact lt_of_lt_of_le
    (lt_of_add_lt_add_right haddPi)
    (le_add_of_nonneg_right (le_of_lt hpiPos))

theorem Real.negative_add_branch_mem_centered
    {v : ℝ} (hv : v < 0) :
    v + 2 * Real.pi * ((Real.centeredAngularBranchIndex v : ℕ) : ℝ) ∈
      Set.Ioc (-Real.pi) Real.pi := by
  have hvAbs : |v| = -v := abs_of_neg hv
  have hlowerBase := Real.abs_lt_two_pi_mul_branch_add_pi v
  have hlower : -Real.pi <
      v + 2 * Real.pi * ((Real.centeredAngularBranchIndex v : ℕ) : ℝ) := by
    have hnegated :
        -Real.pi < -|v| +
          2 * Real.pi * ((Real.centeredAngularBranchIndex v : ℕ) : ℝ) :=
      (sub_lt_iff_lt_add).mpr hlowerBase
    exact Eq.subst
      (motive := fun z : ℝ =>
        -Real.pi < z +
          2 * Real.pi * ((Real.centeredAngularBranchIndex v : ℕ) : ℝ))
      (Eq.trans (congrArg Neg.neg hvAbs) (neg_neg v)) hnegated
  have hupperBase := Real.two_pi_mul_branch_le_abs_add_pi v
  have hupper :
      v + 2 * Real.pi * ((Real.centeredAngularBranchIndex v : ℕ) : ℝ) ≤
        Real.pi := by
    have hnegated :
        -|v| +
            2 * Real.pi * ((Real.centeredAngularBranchIndex v : ℕ) : ℝ) ≤
          Real.pi :=
      (sub_le_iff_le_add).mpr hupperBase
    exact Eq.subst
      (motive := fun z : ℝ =>
        z + 2 * Real.pi *
          ((Real.centeredAngularBranchIndex v : ℕ) : ℝ) ≤ Real.pi)
      (Eq.trans (congrArg Neg.neg hvAbs) (neg_neg v)) hnegated
  exact And.intro hlower hupper

theorem Complex.logarithmicPhaseDualContinuousBranchIndex_nat_eq_discrete
    (t : ℝ) (h n : ℕ) :
    Complex.logarithmicPhaseDualContinuousBranchIndex t (h : ℝ) (n : ℝ) =
      Complex.logarithmicPhaseDualDiscreteBranchIndex t h n := by
  unfold Complex.logarithmicPhaseDualContinuousBranchIndex
  unfold Complex.logarithmicPhaseDualDiscreteBranchIndex
  exact congrArg Real.centeredAngularBranchIndex
    (Complex.logarithmicPhaseDualContinuousIncrement_nat_eq t h n)

end

end LFunctions
end Boundary
