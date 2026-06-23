import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.PuncturedStripTopology

/-!
# Punctured-vertical-strip corridor geometry
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
open Filter MeasureTheory Set
local notation "π" => Real.pi

/-- The left safe corridor has positive real coordinate. -/
theorem real_zero_lt_one_half_for_puncturedVerticalStrip :
    (0 : ℝ) < 1 / 2 := by
  exact half_pos zero_lt_one

/-- The left safe corridor lies left of the deleted vertical line. -/
theorem real_one_half_lt_one_for_puncturedVerticalStrip :
    (1 / 2 : ℝ) < 1 := by
  exact half_lt_self zero_lt_one

/-- The left safe corridor lies inside the right strip boundary. -/
theorem real_one_half_lt_two_for_puncturedVerticalStrip :
    (1 / 2 : ℝ) < 2 := by
  exact
    lt_trans
      real_one_half_lt_one_for_puncturedVerticalStrip
      one_lt_two

/-- The numeric comparison used to place the right corridor in the strip. -/
theorem real_two_lt_three_for_puncturedVerticalStrip :
    (2 : ℝ) < 3 := by
  exact (Nat.cast_lt (α := ℝ)).mpr (show (2 : ℕ) < 3 by decide)

/-- The numeric comparison used to bound the right corridor by the strip. -/
theorem real_three_lt_four_for_puncturedVerticalStrip :
    (3 : ℝ) < 4 := by
  exact (Nat.cast_lt (α := ℝ)).mpr (show (3 : ℕ) < 4 by decide)

/-- The casted natural-number sum `2 + 2`. -/
theorem real_two_add_two_eq_four_for_puncturedVerticalStrip :
    (2 : ℝ) + 2 = 4 := by
  calc
    (2 : ℝ) + 2 = ((2 + 2 : ℕ) : ℝ) := (Nat.cast_add 2 2).symm
    _ = 4 := congrArg (fun n : ℕ => (n : ℝ)) (show (2 + 2 : ℕ) = 4 by rfl)

/-- The square of the endpoint denominator in the right corridor. -/
theorem real_two_mul_two_eq_four_for_puncturedVerticalStrip :
    (2 : ℝ) * 2 = 4 := by
  calc
    (2 : ℝ) * 2 = 2 + 2 := two_mul 2
    _ = 4 := real_two_add_two_eq_four_for_puncturedVerticalStrip

/-- The right safe corridor has positive real coordinate. -/
theorem real_zero_lt_three_halves_for_puncturedVerticalStrip :
    (0 : ℝ) < 3 / 2 := by
  exact div_pos (show (0 : ℝ) < 3 by
    calc
      (0 : ℝ) < 1 := zero_lt_one
      _ < 3 := lt_trans one_lt_two (show (2 : ℝ) < 3 by
        exact real_two_lt_three_for_puncturedVerticalStrip)) two_pos

/-- The right safe corridor lies right of the deleted vertical line. -/
theorem real_one_lt_three_halves_for_puncturedVerticalStrip :
    (1 : ℝ) < 3 / 2 := by
  exact
    (lt_div_iff₀ two_pos).2
      (show (1 : ℝ) * 2 < 3 by
        calc
          (1 : ℝ) * 2 = 2 := one_mul 2
          _ < 3 := real_two_lt_three_for_puncturedVerticalStrip)

/-- The right safe corridor lies inside the right strip boundary. -/
theorem real_three_halves_lt_two_for_puncturedVerticalStrip :
    (3 / 2 : ℝ) < 2 := by
  exact
    (div_lt_iff₀ two_pos).2
      (show (3 : ℝ) < 2 * 2 by
        calc
          (3 : ℝ) < 4 := real_three_lt_four_for_puncturedVerticalStrip
          _ = 2 * 2 := real_two_mul_two_eq_four_for_puncturedVerticalStrip.symm)

/-- The left safe corridor real coordinate is not the deleted coordinate. -/
theorem real_one_half_ne_one_for_puncturedVerticalStrip :
    (1 / 2 : ℝ) ≠ 1 := by
  exact ne_of_lt real_one_half_lt_one_for_puncturedVerticalStrip

/-- The right safe corridor real coordinate is not the deleted coordinate. -/
theorem real_three_halves_ne_one_for_puncturedVerticalStrip :
    (3 / 2 : ℝ) ≠ 1 := by
  exact ne_of_gt real_one_lt_three_halves_for_puncturedVerticalStrip

/-- The left safe column lies in the punctured strip. -/
theorem eulerMaclaurin_puncturedVerticalStrip_leftColumn_mem
    {y : ℝ} :
    Complex.mk (1 / 2) y ∈
      ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}) := by
  constructor
  · exact real_zero_lt_one_half_for_puncturedVerticalStrip
  constructor
  · exact real_one_half_lt_two_for_puncturedVerticalStrip
  · intro hbad
    have hre : (Complex.mk (1 / 2 : ℝ) y).re = (1 : ℂ).re :=
      congrArg Complex.re hbad
    exact real_one_half_ne_one_for_puncturedVerticalStrip hre

/-- The right safe column lies in the punctured strip. -/
theorem eulerMaclaurin_puncturedVerticalStrip_rightColumn_mem
    {y : ℝ} :
    Complex.mk (3 / 2) y ∈
      ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}) := by
  constructor
  · exact real_zero_lt_three_halves_for_puncturedVerticalStrip
  constructor
  · exact real_three_halves_lt_two_for_puncturedVerticalStrip
  · intro hbad
    have hre : (Complex.mk (3 / 2 : ℝ) y).re = (1 : ℂ).re :=
      congrArg Complex.re hbad
    exact real_three_halves_ne_one_for_puncturedVerticalStrip hre

/-- The left half-column is a safe vertical corridor inside the punctured
strip. -/
theorem eulerMaclaurin_puncturedVerticalStrip_leftColumn_verticalJoined
    {y₁ y₂ : ℝ} :
    JoinedIn
      ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
      (Complex.mk (1 / 2) y₁)
      (Complex.mk (1 / 2) y₂) := by
  exact
    puncturedVerticalStrip_leftHalf_joined
      eulerMaclaurin_puncturedVerticalStrip_leftColumn_mem
      eulerMaclaurin_puncturedVerticalStrip_leftColumn_mem
      real_one_half_lt_one_for_puncturedVerticalStrip
      real_one_half_lt_one_for_puncturedVerticalStrip

/-- The right half-column is a safe vertical corridor inside the punctured
strip. -/
theorem eulerMaclaurin_puncturedVerticalStrip_rightColumn_verticalJoined
    {y₁ y₂ : ℝ} :
    JoinedIn
      ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
      (Complex.mk (3 / 2) y₁)
      (Complex.mk (3 / 2) y₂) := by
  exact
    puncturedVerticalStrip_rightHalf_joined
      eulerMaclaurin_puncturedVerticalStrip_rightColumn_mem
      eulerMaclaurin_puncturedVerticalStrip_rightColumn_mem
      real_one_lt_three_halves_for_puncturedVerticalStrip
      real_one_lt_three_halves_for_puncturedVerticalStrip

/-- Every point in the punctured strip is joined to one of the two safe
vertical corridors at its own imaginary height. -/
theorem eulerMaclaurin_puncturedVerticalStrip_joinedTo_safeCorridor
    {z : ℂ}
    (hz : z ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}))
    [hz_left_dec : Decidable (z.re < 1)]
    [hz_one_dec : Decidable (z.re = 1)] :
    JoinedIn
        ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
        z
        (Complex.mk (1 / 2) z.im) ∨
    JoinedIn
        ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
        z
        (Complex.mk (3 / 2) z.im) := by
  exact match hz_left_dec with
  | isTrue hz_left =>
      Or.inl
        (puncturedVerticalStrip_leftHalf_joined
          hz
          eulerMaclaurin_puncturedVerticalStrip_leftColumn_mem
          hz_left
          real_one_half_lt_one_for_puncturedVerticalStrip)
  | isFalse hz_not_left =>
      have hz_one_le : 1 ≤ z.re :=
        le_of_not_gt hz_not_left
      match hz_one_dec with
      | isTrue hz_re_eq_one =>
          have hz_im_ne_zero : z.im ≠ 0 := by
            intro hz_im_zero
            have hz_eq_one : z = (1 : ℂ) := by
              exact Complex.ext
                (by
                  calc
                    z.re = 1 := hz_re_eq_one
                    _ = (1 : ℂ).re := rfl)
                (by
                  calc
                    z.im = 0 := hz_im_zero
                    _ = (1 : ℂ).im := rfl)
            exact hz.2.2 hz_eq_one
          have hjoined :
              JoinedIn
                ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
                (Complex.mk z.re z.im)
                (Complex.mk (1 / 2) z.im) :=
              puncturedVerticalStrip_nonzeroHeight_horizontalJoined
              (by
                calc
                  0 < z.re := hz.1)
              (by
                calc
                  z.re < 2 := hz.2.1)
              real_zero_lt_one_half_for_puncturedVerticalStrip
              real_one_half_lt_two_for_puncturedVerticalStrip
              hz_im_ne_zero
          Or.inl
            (Eq.subst
              (motive := fun u : ℂ =>
                JoinedIn
                  ({v : ℂ | 0 < v.re ∧ v.re < 2 ∧ v ≠ 1})
                  u
                  (Complex.mk (1 / 2) z.im))
              (Complex.eta z)
              hjoined)
      | isFalse hz_re_ne_one =>
          have hz_right : 1 < z.re :=
            lt_of_le_of_ne hz_one_le (Ne.symm hz_re_ne_one)
          Or.inr
            (puncturedVerticalStrip_rightHalf_joined
              hz
              eulerMaclaurin_puncturedVerticalStrip_rightColumn_mem
              hz_right
              real_one_lt_three_halves_for_puncturedVerticalStrip)

/-- The two safe vertical corridors are joined at any nonzero imaginary
height. -/
theorem eulerMaclaurin_puncturedVerticalStrip_leftCorridor_joined_rightCorridor
    {h : ℝ}
    (hh : h ≠ 0) :
    JoinedIn
      ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
      (Complex.mk (1 / 2) h)
      (Complex.mk (3 / 2) h) := by
  exact
    puncturedVerticalStrip_nonzeroHeight_horizontalJoined
      real_zero_lt_one_half_for_puncturedVerticalStrip
      real_one_half_lt_two_for_puncturedVerticalStrip
      real_zero_lt_three_halves_for_puncturedVerticalStrip
      real_three_halves_lt_two_for_puncturedVerticalStrip
      hh

/-- Corridor polygonal-path construction in the punctured vertical strip. -/
theorem eulerMaclaurin_puncturedVerticalStrip_joinedIn_via_corridors
    {z w : ℂ}
    (hz : z ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}))
    (hw : w ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})) :
    JoinedIn ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}) z w := by
  have hz_corridor :
      JoinedIn
          ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
          z
          (Complex.mk (1 / 2) z.im) ∨
        JoinedIn
          ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
          z
          (Complex.mk (3 / 2) z.im) :=
    eulerMaclaurin_puncturedVerticalStrip_joinedTo_safeCorridor hz
  have hw_corridor :
      JoinedIn
          ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
          w
          (Complex.mk (1 / 2) w.im) ∨
        JoinedIn
          ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
          w
          (Complex.mk (3 / 2) w.im) :=
    eulerMaclaurin_puncturedVerticalStrip_joinedTo_safeCorridor hw
  cases hz_corridor with
  | inl hz_left =>
      cases hw_corridor with
      | inl hw_left =>
          exact
            hz_left.trans
              ((eulerMaclaurin_puncturedVerticalStrip_leftColumn_verticalJoined).trans
                hw_left.symm)
      | inr hw_right =>
          have hleft_to_right :
              JoinedIn
                ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
                (Complex.mk (1 / 2) z.im)
                (Complex.mk (3 / 2) w.im) :=
              (eulerMaclaurin_puncturedVerticalStrip_leftColumn_verticalJoined
                (y₁ := z.im) (y₂ := 1)).trans
                ((eulerMaclaurin_puncturedVerticalStrip_leftCorridor_joined_rightCorridor
                  (h := 1) one_ne_zero).trans
                  (eulerMaclaurin_puncturedVerticalStrip_rightColumn_verticalJoined
                    (y₁ := 1) (y₂ := w.im)))
          exact hz_left.trans (hleft_to_right.trans hw_right.symm)
  | inr hz_right =>
      cases hw_corridor with
      | inl hw_left =>
          have hright_to_left :
              JoinedIn
                ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
                (Complex.mk (3 / 2) z.im)
                (Complex.mk (1 / 2) w.im) :=
              (eulerMaclaurin_puncturedVerticalStrip_rightColumn_verticalJoined
                (y₁ := z.im) (y₂ := 1)).trans
                ((eulerMaclaurin_puncturedVerticalStrip_leftCorridor_joined_rightCorridor
                  (h := 1) one_ne_zero).symm.trans
                  (eulerMaclaurin_puncturedVerticalStrip_leftColumn_verticalJoined
                    (y₁ := 1) (y₂ := w.im)))
          exact hz_right.trans (hright_to_left.trans hw_left.symm)
      | inr hw_right =>
          exact
            hz_right.trans
              ((eulerMaclaurin_puncturedVerticalStrip_rightColumn_verticalJoined).trans
                hw_right.symm)

/-- Polygonal-path construction in the punctured vertical strip. -/
theorem eulerMaclaurin_puncturedVerticalStrip_joinedIn_via_polygon
    {z w : ℂ}
    (hz : z ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}))
    (hw : w ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})) :
    JoinedIn ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}) z w := by
  exact
    eulerMaclaurin_puncturedVerticalStrip_joinedIn_via_corridors
      hz hw

end
end LFunctions
end Boundary
