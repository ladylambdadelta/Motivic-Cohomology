import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.PuncturedStripTopology

/-!
# Punctured-vertical-strip connectivity

Lemmas establishing connected paths inside `{u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}` used by
Euler–Maclaurin continuation.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
open Filter MeasureTheory Set
local notation "π" => Real.pi

/-- Horizontal segments at nonzero imaginary height stay inside the punctured
strip once their endpoints lie in the strip. -/
theorem eulerMaclaurin_puncturedVerticalStrip_horizontalSegment_mem
    {z w p : ℂ}
    (hz : z ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}))
    (hw : w ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}))
    (hp_re : p.re ∈ Set.Icc z.re w.re ∨ p.re ∈ Set.Icc w.re z.re)
    (hp_im : p.im = z.im)
    (_hzw_im : z.im = w.im)
    (hz_im : z.im ≠ 0) :
    p ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}) := by
  constructor
  · cases hp_re with
    | inl hp_between =>
        exact lt_of_lt_of_le hz.1 hp_between.1
    | inr hp_between =>
        exact lt_of_lt_of_le hw.1 hp_between.1
  constructor
  · cases hp_re with
    | inl hp_between =>
        exact lt_of_le_of_lt hp_between.2 hw.2.1
    | inr hp_between =>
        exact lt_of_le_of_lt hp_between.2 hz.2.1
  · intro hbad
    have hp_one_im : p.im = (1 : ℂ).im :=
      congrArg Complex.im hbad
    have hz_zero : z.im = 0 := by
      calc
        z.im = p.im := hp_im.symm
        _ = (1 : ℂ).im := hp_one_im
        _ = 0 := rfl
    exact hz_im hz_zero

/-- Vertical segments at real part different from `1` stay inside the punctured
strip once their endpoints lie in the strip. -/
theorem eulerMaclaurin_puncturedVerticalStrip_verticalSegment_mem
    {z w p : ℂ}
    (hz : z ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}))
    (_hw : w ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}))
    (hp_re : p.re = z.re)
    (_hp_im : p.im ∈ Set.Icc z.im w.im ∨ p.im ∈ Set.Icc w.im z.im)
    (_hzw_re : z.re = w.re)
    (hz_re : z.re ≠ 1) :
    p ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}) := by
  constructor
  · calc
      0 < z.re := hz.1
      _ = p.re := hp_re.symm
  constructor
  · calc
      p.re = z.re := hp_re
      _ < 2 := hz.2.1
  · intro hbad
    have hp_one_re : p.re = (1 : ℂ).re :=
      congrArg Complex.re hbad
    have hz_one : z.re = 1 := by
      calc
        z.re = p.re := hp_re.symm
        _ = (1 : ℂ).re := hp_one_re
        _ = 1 := rfl
    exact hz_re hz_one

/-- For any two points in the punctured strip, choose an endpoint detour height
away from the deleted point `1`. -/
theorem eulerMaclaurin_puncturedVerticalStrip_detourHeight_exists
    (z w : ℂ)
    (hz : z ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}))
    (hw : w ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})) :
    ∃ h : ℝ, h ≠ 0 ∧
      Complex.mk z.re h ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}) ∧
      Complex.mk w.re h ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}) := by
  have hz_detour :
      Complex.mk z.re (1 : ℝ) ∈
        ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}) :=
    And.intro
      hz.1
      (And.intro
        hz.2.1
        (fun hbad : Complex.mk z.re (1 : ℝ) = 1 =>
          have him : (Complex.mk z.re (1 : ℝ)).im = (1 : ℂ).im :=
            congrArg Complex.im hbad
          one_ne_zero him))
  have hw_detour :
      Complex.mk w.re (1 : ℝ) ∈
        ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}) :=
    And.intro
      hw.1
      (And.intro
        hw.2.1
        (fun hbad : Complex.mk w.re (1 : ℝ) = 1 =>
          have him : (Complex.mk w.re (1 : ℝ)).im = (1 : ℂ).im :=
            congrArg Complex.im hbad
          one_ne_zero him))
  exact Exists.intro 1 (And.intro one_ne_zero (And.intro hz_detour hw_detour))

/-- Points in the left component `0 < Re z < 1` of the punctured strip are
joined inside the punctured strip. -/
theorem eulerMaclaurin_puncturedVerticalStrip_leftHalf_joined
    {z w : ℂ}
    (hz : z ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}))
    (hw : w ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}))
    (hz_left : z.re < 1)
    (hw_left : w.re < 1) :
    JoinedIn
      ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
      z w := by
  exact
    puncturedVerticalStrip_leftHalf_joined
      (z := z) (w := w) hz hw hz_left hw_left

/-- Points in the right component `1 < Re z < 2` of the punctured strip are
joined inside the punctured strip. -/
theorem eulerMaclaurin_puncturedVerticalStrip_rightHalf_joined
    {z w : ℂ}
    (hz : z ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}))
    (hw : w ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}))
    (hz_right : 1 < z.re)
    (hw_right : 1 < w.re) :
    JoinedIn
      ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
      z w := by
  exact
    puncturedVerticalStrip_rightHalf_joined
      (z := z) (w := w) hz hw hz_right hw_right

/-- Horizontal segments at nonzero height cross safely between any two real
parts in the open strip. -/
theorem eulerMaclaurin_puncturedVerticalStrip_nonzeroHeight_horizontalJoined
    {x₁ x₂ h : ℝ}
    (hx₁_left : 0 < x₁)
    (hx₁_right : x₁ < 2)
    (hx₂_left : 0 < x₂)
    (hx₂_right : x₂ < 2)
    (hh : h ≠ 0) :
    JoinedIn
      ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
      (Complex.mk x₁ h)
      (Complex.mk x₂ h) := by
  exact
    puncturedVerticalStrip_nonzeroHeight_horizontalJoined
      hx₁_left hx₁_right hx₂_left hx₂_right hh

end
end LFunctions
end Boundary
