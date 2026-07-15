import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFiniteInactiveNearPacking

/-!
# Exact near-inactive collar width arithmetic

The scale identity `norm t = (S-1)(S+1)` cancels the denominator in each
near-inactive collar.  The resulting numerators retain a favorable negative
`(2/3)*norm t` term.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Complex.logarithmicPhaseFiniteLeftNear_width_eq
    (t : ℝ) (a : ℤ) :
    Real.integerBlockCutoffSupportLeftEndpoint a -
        Complex.logarithmicPhaseFiniteLeftNearCenterLower t a =
      (a : ℝ) /
          (Complex.logarithmicPhaseBProcessScale t + 1) - 2 / 3 := by
  let S := Complex.logarithmicPhaseBProcessScale t
  unfold Real.integerBlockCutoffSupportLeftEndpoint
  unfold Complex.logarithmicPhaseFiniteLeftNearCenterLower
  have haddNe : S + 1 ≠ 0 :=
    ne_of_gt (Complex.logarithmicPhaseBProcessScale_add_one_pos t)
  have hfactor :
      (a : ℝ) - (a : ℝ) * S / (S + 1) =
        (a : ℝ) / (S + 1) := by
    have hcommon :
        (a : ℝ) = (a : ℝ) * (S + 1) / (S + 1) := by
      exact (eq_div_iff haddNe).mpr rfl
    calc
      (a : ℝ) - (a : ℝ) * S / (S + 1) =
          ((a : ℝ) * (S + 1) - (a : ℝ) * S) / (S + 1) := by
        exact Eq.trans
          (congrArg
            (fun value : ℝ => value - (a : ℝ) * S / (S + 1))
            hcommon)
          (div_sub_div_same _ _ _)
      _ = ((a : ℝ) * 1) / (S + 1) := by
        exact congrArg (fun value : ℝ => value / (S + 1))
          (Eq.trans
            (Eq.trans
              (congrArg
                (fun value : ℝ => value - (a : ℝ) * S)
                (mul_add (a : ℝ) S 1))
              (add_sub_cancel_left _ _))
            rfl)
      _ = (a : ℝ) / (S + 1) :=
        congrArg (fun value : ℝ => value / (S + 1)) (mul_one _)
  calc
    (a : ℝ) - 2 / 3 - (a : ℝ) * S / (S + 1) =
        (a : ℝ) - (2 / 3 + (a : ℝ) * S / (S + 1)) :=
      sub_sub _ _ _
    _ = (a : ℝ) - ((a : ℝ) * S / (S + 1) + 2 / 3) :=
      congrArg (fun value : ℝ => (a : ℝ) - value)
        (add_comm (2 / 3) ((a : ℝ) * S / (S + 1)))
    _ = ((a : ℝ) - (a : ℝ) * S / (S + 1)) - 2 / 3 :=
      (sub_sub _ _ _).symm
    _ = (a : ℝ) / (S + 1) - 2 / 3 :=
      congrArg (fun value : ℝ => value - 2 / 3) hfactor

theorem Complex.logarithmicPhaseFiniteRightNear_width_eq
    (t : ℝ) (ht : 1 ≤ ‖t‖) (b : ℤ) :
    Complex.logarithmicPhaseFiniteRightNearCenterUpper t b -
        ((b : ℝ) + 2 / 3) =
      (b : ℝ) /
          (Complex.logarithmicPhaseBProcessScale t - 1) - 2 / 3 := by
  let S := Complex.logarithmicPhaseBProcessScale t
  unfold Complex.logarithmicPhaseFiniteRightNearCenterUpper
  have hsubNe : S - 1 ≠ 0 :=
    ne_of_gt (Complex.logarithmicPhaseBProcessScale_sub_one_pos t ht)
  have hfactor :
      (b : ℝ) * S / (S - 1) - (b : ℝ) =
        (b : ℝ) / (S - 1) := by
    have hcommon :
        (b : ℝ) = (b : ℝ) * (S - 1) / (S - 1) := by
      exact (eq_div_iff hsubNe).mpr rfl
    calc
      (b : ℝ) * S / (S - 1) - (b : ℝ) =
          ((b : ℝ) * S - (b : ℝ) * (S - 1)) / (S - 1) := by
        exact Eq.trans
          (congrArg
            (fun value : ℝ => (b : ℝ) * S / (S - 1) - value)
            hcommon)
          (div_sub_div_same _ _ _)
      _ = ((b : ℝ) * 1) / (S - 1) := by
        exact congrArg (fun value : ℝ => value / (S - 1))
          (Eq.trans
            (congrArg
              (fun value : ℝ => (b : ℝ) * S - value)
              (mul_sub (b : ℝ) S 1))
            (sub_sub_cancel _ _))
      _ = (b : ℝ) / (S - 1) :=
        congrArg (fun value : ℝ => value / (S - 1)) (mul_one _)
  exact Eq.trans (sub_add_eq_sub_sub _ _ _)
    (congrArg (fun value : ℝ => value - 2 / 3) hfactor)

theorem Complex.logarithmicPhaseFiniteLeftNear_scaled_width_eq
    (t : ℝ) (a : ℤ) :
    ‖t‖ *
        (Real.integerBlockCutoffSupportLeftEndpoint a -
          Complex.logarithmicPhaseFiniteLeftNearCenterLower t a) =
      (a : ℝ) * (Complex.logarithmicPhaseBProcessScale t - 1) -
        (2 / 3) * ‖t‖ := by
  let S := Complex.logarithmicPhaseBProcessScale t
  have hwidth := Complex.logarithmicPhaseFiniteLeftNear_width_eq t a
  have hnorm := Complex.logarithmicPhaseBProcess_norm_eq_scale_sub_mul_add t
  have haddNe : S + 1 ≠ 0 :=
    ne_of_gt (Complex.logarithmicPhaseBProcessScale_add_one_pos t)
  have hcancel := Real.mul_div_cancel_add_factor (a : ℝ) S haddNe
  calc
    ‖t‖ *
        (Real.integerBlockCutoffSupportLeftEndpoint a -
          Complex.logarithmicPhaseFiniteLeftNearCenterLower t a) =
        ‖t‖ * ((a : ℝ) / (S + 1) - 2 / 3) :=
      congrArg (fun value : ℝ => ‖t‖ * value) hwidth
    _ = ‖t‖ * ((a : ℝ) / (S + 1)) - ‖t‖ * (2 / 3) :=
      mul_sub _ _ _
    _ = (a : ℝ) * (S - 1) - (2 / 3) * ‖t‖ := by
      exact congrArg₂ (fun left right : ℝ => left - right)
        (Eq.subst
          (motive := fun value : ℝ =>
            value * ((a : ℝ) / (S + 1)) = (a : ℝ) * (S - 1))
          hnorm.symm hcancel)
        (mul_comm ‖t‖ (2 / 3))

theorem Complex.logarithmicPhaseFiniteRightNear_scaled_width_eq
    (t : ℝ) (ht : 1 ≤ ‖t‖) (b : ℤ) :
    ‖t‖ *
        (Complex.logarithmicPhaseFiniteRightNearCenterUpper t b -
          ((b : ℝ) + 2 / 3)) =
      (b : ℝ) * (Complex.logarithmicPhaseBProcessScale t + 1) -
        (2 / 3) * ‖t‖ := by
  let S := Complex.logarithmicPhaseBProcessScale t
  have hwidth := Complex.logarithmicPhaseFiniteRightNear_width_eq t ht b
  have hnorm := Complex.logarithmicPhaseBProcess_norm_eq_scale_sub_mul_add t
  have hsubNe : S - 1 ≠ 0 :=
    ne_of_gt (Complex.logarithmicPhaseBProcessScale_sub_one_pos t ht)
  have hcancel := Real.mul_div_cancel_sub_factor (b : ℝ) S hsubNe
  calc
    ‖t‖ *
        (Complex.logarithmicPhaseFiniteRightNearCenterUpper t b -
          ((b : ℝ) + 2 / 3)) =
        ‖t‖ * ((b : ℝ) / (S - 1) - 2 / 3) :=
      congrArg (fun value : ℝ => ‖t‖ * value) hwidth
    _ = ‖t‖ * ((b : ℝ) / (S - 1)) - ‖t‖ * (2 / 3) :=
      mul_sub _ _ _
    _ = (b : ℝ) * (S + 1) - (2 / 3) * ‖t‖ := by
      exact congrArg₂ (fun left right : ℝ => left - right)
        (Eq.subst
          (motive := fun value : ℝ =>
            value * ((b : ℝ) / (S - 1)) = (b : ℝ) * (S + 1))
          hnorm.symm hcancel)
        (mul_comm ‖t‖ (2 / 3))

theorem Complex.logarithmicPhaseFiniteLeftNear_scaled_width_le_a_mul_scale_sub_one
    (t : ℝ) (a : ℤ) :
    ‖t‖ *
        (Real.integerBlockCutoffSupportLeftEndpoint a -
          Complex.logarithmicPhaseFiniteLeftNearCenterLower t a) ≤
      (a : ℝ) * (Complex.logarithmicPhaseBProcessScale t - 1) := by
  have hnonneg : 0 ≤ (2 / 3 : ℝ) * ‖t‖ :=
    mul_nonneg
      (div_nonneg
        (le_of_lt (Nat.cast_pos.mpr (Nat.succ_pos 1)))
        (le_of_lt (Nat.cast_pos.mpr (Nat.succ_pos 2))))
      (norm_nonneg t)
  exact Eq.subst (motive := fun value : ℝ => value ≤ _)
    (Complex.logarithmicPhaseFiniteLeftNear_scaled_width_eq t a).symm
    (sub_le_self _ hnonneg)

theorem Complex.logarithmicPhaseFiniteRightNear_scaled_width_le_b_mul_scale_add_one
    (t : ℝ) (ht : 1 ≤ ‖t‖) (b : ℤ) :
    ‖t‖ *
        (Complex.logarithmicPhaseFiniteRightNearCenterUpper t b -
          ((b : ℝ) + 2 / 3)) ≤
      (b : ℝ) * (Complex.logarithmicPhaseBProcessScale t + 1) := by
  have hnonneg : 0 ≤ (2 / 3 : ℝ) * ‖t‖ :=
    mul_nonneg
      (div_nonneg
        (le_of_lt (Nat.cast_pos.mpr (Nat.succ_pos 1)))
        (le_of_lt (Nat.cast_pos.mpr (Nat.succ_pos 2))))
      (norm_nonneg t)
  exact Eq.subst (motive := fun value : ℝ => value ≤ _)
    (Complex.logarithmicPhaseFiniteRightNear_scaled_width_eq t ht b).symm
    (sub_le_self _ hnonneg)

end

end LFunctions
end Boundary
