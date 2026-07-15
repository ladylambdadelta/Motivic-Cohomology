import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicRefinedBudgetArithmetic

/-!
# Canonical logarithmic long-block geometry

The curvature branch repeatedly uses the same five endpoint hypotheses.  This
owner names their conjunction and derives the elementary endpoint and
square-root comparisons consumed by packet-cardinality arithmetic.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Real.logarithmicPhaseLongBranchGeometry
    (t : ℝ) (a b : ℕ) : Prop :=
  1 ≤ a ∧
    a ≤ b ∧
      a < b ∧
        Real.sqrt (1 + ‖t‖) <
          (((b + 1 : ℕ) : ℝ) - (a : ℝ)) ∧
        ((((b + 1 : ℕ) : ℝ) / ‖t‖) <
          (((b + 1 : ℕ) : ℝ) - (a : ℝ)) ∧
        b + 1 ≤ 2 * a)

theorem Real.logarithmicPhaseLongBranchGeometry_first_pos
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    1 ≤ a := by
  exact hgeometry.1

theorem Real.logarithmicPhaseLongBranchGeometry_order
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    a ≤ b := by
  exact hgeometry.2.1

theorem Real.logarithmicPhaseLongBranchGeometry_strict
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    a < b := by
  exact hgeometry.2.2.1

theorem Real.logarithmicPhaseLongBranchGeometry_sqrt
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Real.sqrt (1 + ‖t‖) <
      (((b + 1 : ℕ) : ℝ) - (a : ℝ)) := by
  exact hgeometry.2.2.2.1

theorem Real.logarithmicPhaseLongBranchGeometry_endpoint
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    (((b + 1 : ℕ) : ℝ) / ‖t‖) <
      (((b + 1 : ℕ) : ℝ) - (a : ℝ)) := by
  exact hgeometry.2.2.2.2.1

theorem Real.logarithmicPhaseLongBranchGeometry_comparable
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    b + 1 ≤ 2 * a := by
  exact hgeometry.2.2.2.2.2

theorem Real.logarithmicPhaseLongBranchGeometry_of_endpoint_hypotheses
    {t : ℝ} {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hstrict : a < b)
    (hsqrt : Real.sqrt (1 + ‖t‖) <
      (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hendpoint : (((b + 1 : ℕ) : ℝ) / ‖t‖) <
      (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hcomparable : b + 1 ≤ 2 * a) :
    Real.logarithmicPhaseLongBranchGeometry t a b := by
  exact ⟨ha, hab, hstrict, hsqrt, hendpoint, hcomparable⟩


theorem Real.logarithmicPhaseLongBranchGeometry_zero_lt_a
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    0 < a := by
  exact lt_of_lt_of_le Nat.zero_lt_one hgeometry.1

theorem Real.logarithmicPhaseLongBranchGeometry_one_le_b
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    1 ≤ b := by
  exact le_trans hgeometry.1 hgeometry.2.1

theorem Real.logarithmicPhaseLongBranchGeometry_zero_le_b_int
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    (0 : ℤ) ≤ (b : ℤ) := by
  exact Int.ofNat_zero_le b

theorem Real.logarithmicPhaseLongBranchGeometry_a_cast_ge_one
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    (1 : ℝ) ≤ (a : ℝ) := by
  have hcast : (((1 : ℕ) : ℝ)) ≤ (a : ℝ) :=
    Nat.mono_cast hgeometry.1
  have hone : (((1 : ℕ) : ℝ)) = (1 : ℝ) :=
    Nat.cast_one
  exact Eq.subst
    (motive := fun value : ℝ => value ≤ (a : ℝ))
    hone
    hcast

theorem Real.logarithmicPhaseLongBranchGeometry_length_pos
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    0 < (((b + 1 : ℕ) : ℝ) - (a : ℝ)) := by
  have haSucc : a < b + 1 := lt_of_lt_of_le hgeometry.2.2.1 (Nat.le_succ b)
  have haSuccReal : (a : ℝ) < ((b + 1 : ℕ) : ℝ) :=
    Nat.cast_lt.mpr haSucc
  exact sub_pos.mpr haSuccReal

theorem Real.logarithmicPhaseLongBranchGeometry_length_le_b
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    (((b + 1 : ℕ) : ℝ) - (a : ℝ)) ≤ (b : ℝ) := by
  have haReal : (1 : ℝ) ≤ (a : ℝ) :=
    Real.logarithmicPhaseLongBranchGeometry_a_cast_ge_one hgeometry
  have hneg := neg_le_neg haReal
  have hadd := add_le_add_left hneg (((b + 1 : ℕ) : ℝ))
  have hsuccCast : ((b + 1 : ℕ) : ℝ) = (b : ℝ) + 1 :=
    Eq.trans
      (Nat.cast_add b 1)
      (congrArg (fun value : ℝ => (b : ℝ) + value) Nat.cast_one)
  have hnormalize :
      ((b : ℝ) + 1) + -1 = (b : ℝ) := by
    calc
      ((b : ℝ) + 1) + -1 = (b : ℝ) + (1 + -1) :=
        add_assoc (b : ℝ) 1 (-1)
      _ = (b : ℝ) + 0 :=
        congrArg (fun value : ℝ => (b : ℝ) + value) (add_neg_cancel 1)
      _ = (b : ℝ) := add_zero _
  have htransported :
      ((b + 1 : ℕ) : ℝ) + -(a : ℝ) ≤ (b : ℝ) := by
    exact le_trans hadd
      (le_of_eq
        (Eq.trans
          (congrArg (fun value : ℝ => value + -1) hsuccCast)
          hnormalize))
  exact Eq.subst
    (motive := fun value : ℝ => value ≤ (b : ℝ))
    (sub_eq_add_neg (((b + 1 : ℕ) : ℝ)) (a : ℝ)).symm
    htransported

theorem Real.logarithmicPhaseLongBranchGeometry_sqrt_lt_b
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Real.sqrt (1 + ‖t‖) < (b : ℝ) := by
  exact lt_of_lt_of_le
    hgeometry.2.2.2.1
    (Real.logarithmicPhaseLongBranchGeometry_length_le_b hgeometry)

theorem Real.logarithmicPhaseLongBranchGeometry_sqrt_norm_lt_b
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Real.sqrt ‖t‖ < (b : ℝ) := by
  have hnormLe : ‖t‖ ≤ 1 + ‖t‖ :=
    le_add_of_nonneg_left zero_le_one
  have hsqrtLe : Real.sqrt ‖t‖ ≤ Real.sqrt (1 + ‖t‖) :=
    Real.sqrt_le_sqrt hnormLe
  exact lt_of_le_of_lt hsqrtLe
    (Real.logarithmicPhaseLongBranchGeometry_sqrt_lt_b hgeometry)

theorem Real.logarithmicPhaseLongBranchGeometry_b_pos_real
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    0 < (b : ℝ) := by
  exact Nat.cast_pos.mpr
    (lt_of_lt_of_le Nat.zero_lt_one
      (Real.logarithmicPhaseLongBranchGeometry_one_le_b hgeometry))

theorem Real.logarithmicPhaseLongBranchGeometry_norm_pos
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖) :
    0 < ‖t‖ := by
  exact lt_of_lt_of_le zero_lt_one ht

theorem Real.logarithmicPhaseLongBranchGeometry_norm_eq_sqrt_mul_sqrt
    (t : ℝ) :
    ‖t‖ = Real.sqrt ‖t‖ * Real.sqrt ‖t‖ := by
  exact (Real.mul_self_sqrt (norm_nonneg t)).symm

theorem Real.logarithmicPhaseLongBranchGeometry_norm_div_b_lt_sqrt_norm
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    ‖t‖ / (b : ℝ) < Real.sqrt ‖t‖ := by
  have hbPos :=
    Real.logarithmicPhaseLongBranchGeometry_b_pos_real hgeometry
  have hsqrtPos : 0 < Real.sqrt ‖t‖ :=
    Real.sqrt_pos.mpr
      (Real.logarithmicPhaseLongBranchGeometry_norm_pos
        (a := a) (b := b) ht)
  have hsqrtLtB :=
    Real.logarithmicPhaseLongBranchGeometry_sqrt_norm_lt_b hgeometry
  have hproduct :
      ‖t‖ < Real.sqrt ‖t‖ * (b : ℝ) := by
    have hmul := mul_lt_mul_of_pos_left hsqrtLtB hsqrtPos
    exact Eq.subst
      (motive := fun left : ℝ => left < Real.sqrt ‖t‖ * (b : ℝ))
      (Real.logarithmicPhaseLongBranchGeometry_norm_eq_sqrt_mul_sqrt t).symm
      hmul
  exact (div_lt_iff₀ hbPos).mpr hproduct

theorem Real.logarithmicPhaseLongBranchGeometry_norm_div_b_le_sqrt_one_add
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    ‖t‖ / (b : ℝ) ≤ Real.sqrt (1 + ‖t‖) := by
  have hstrict :=
    Real.logarithmicPhaseLongBranchGeometry_norm_div_b_lt_sqrt_norm
      ht hgeometry
  have hnormLe : ‖t‖ ≤ 1 + ‖t‖ :=
    le_add_of_nonneg_left zero_le_one
  have hsqrtLe : Real.sqrt ‖t‖ ≤ Real.sqrt (1 + ‖t‖) :=
    Real.sqrt_le_sqrt hnormLe
  exact le_trans (le_of_lt hstrict) hsqrtLe

theorem Real.logarithmicPhaseLongBranchGeometry_norm_div_b_le_refinedScale
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    ‖t‖ / (b : ℝ) ≤
      Real.logarithmicPhaseRefinedScale t (b : ℤ) := by
  have hsqrt :=
    Real.logarithmicPhaseLongBranchGeometry_norm_div_b_le_sqrt_one_add
      ht hgeometry
  have hbInt : (0 : ℤ) ≤ (b : ℤ) := Int.ofNat_zero_le b
  have hscale :=
    Real.sqrt_scale_le_refinedScale t (b : ℤ) hbInt
  exact le_trans hsqrt hscale

theorem Real.logarithmicPhaseLongBranchGeometry_to_arguments
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    1 ≤ a ∧ a ≤ b ∧ a < b ∧
      Real.sqrt (1 + ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)) ∧
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)) := by
  exact And.intro hgeometry.1
    (And.intro hgeometry.2.1
      (And.intro hgeometry.2.2.1
        (And.intro hgeometry.2.2.2.1 hgeometry.2.2.2.2.1)))

end
end LFunctions
end Boundary
