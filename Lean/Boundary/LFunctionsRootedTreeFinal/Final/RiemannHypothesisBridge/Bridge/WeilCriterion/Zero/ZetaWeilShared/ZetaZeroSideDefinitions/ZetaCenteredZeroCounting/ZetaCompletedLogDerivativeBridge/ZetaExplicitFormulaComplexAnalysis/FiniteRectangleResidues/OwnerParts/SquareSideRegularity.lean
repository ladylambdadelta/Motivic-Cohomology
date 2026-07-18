import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part34

/-!
# Square-side regular radius elimination

This owner layer exposes the coordinate inequalities carried by the finite forbidden-radius
selector.  Consumers do not unfold the finite image construction.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Doubling a real half returns the original value. -/
theorem finiteRectangle_two_mul_half (x : ℝ) :
    2 * (x / 2) = x := by
  have htwo : (2 : ℝ) ≠ 0 :=
    two_ne_zero
  calc
    2 * (x / 2) = (2 * x) / 2 := by
      exact mul_div_assoc' 2 x 2
    _ = x := by
      exact mul_div_cancel_left₀ x htwo

/-- A radius unequal to the doubled coordinate difference excludes the corresponding
lower quarter-radius side level. -/
theorem finiteRectangle_lower_quarter_level_ne
    (ε x y : ℝ)
    (hne : ε ≠ 2 * (2 * (x - y))) :
    x - (ε / 2) / 2 ≠ y := by
  intro hlevel
  have hdifference : x - y = (ε / 2) / 2 := by
    calc
      x - y = x - (x - (ε / 2) / 2) := by
        exact congrArg (fun value : ℝ => x - value) hlevel.symm
      _ = (ε / 2) / 2 := by
        exact sub_sub_cancel_left x ((ε / 2) / 2)
  have hinner : 2 * ((ε / 2) / 2) = ε / 2 :=
    finiteRectangle_two_mul_half (ε / 2)
  have houter : 2 * (ε / 2) = ε :=
    finiteRectangle_two_mul_half ε
  have hforbidden : ε = 2 * (2 * (x - y)) := by
    calc
      ε = 2 * (ε / 2) := houter.symm
      _ = 2 * (2 * ((ε / 2) / 2)) := by
        exact congrArg (fun value : ℝ => 2 * value) hinner.symm
      _ = 2 * (2 * (x - y)) := by
        exact congrArg (fun value : ℝ => 2 * (2 * value)) hdifference.symm
  exact hne hforbidden

/-- A radius unequal to the doubled reverse coordinate difference excludes the
corresponding upper quarter-radius side level. -/
theorem finiteRectangle_upper_quarter_level_ne
    (ε x y : ℝ)
    (hne : ε ≠ 2 * (2 * (y - x))) :
    x + (ε / 2) / 2 ≠ y := by
  intro hlevel
  have hdifference : y - x = (ε / 2) / 2 := by
    calc
      y - x = (x + (ε / 2) / 2) - x := by
        exact congrArg (fun value : ℝ => value - x) hlevel.symm
      _ = (ε / 2) / 2 := by
        exact add_sub_cancel_left x ((ε / 2) / 2)
  have hinner : 2 * ((ε / 2) / 2) = ε / 2 :=
    finiteRectangle_two_mul_half (ε / 2)
  have houter : 2 * (ε / 2) = ε :=
    finiteRectangle_two_mul_half ε
  have hforbidden : ε = 2 * (2 * (y - x)) := by
    calc
      ε = 2 * (ε / 2) := houter.symm
      _ = 2 * (2 * ((ε / 2) / 2)) := by
        exact congrArg (fun value : ℝ => 2 * value) hinner.symm
      _ = 2 * (2 * (y - x)) := by
        exact congrArg (fun value : ℝ => 2 * (2 * value)) hdifference.symm
  exact hne hforbidden

/-- A square-side regular radius is not four times any real-coordinate separation in
the finite carrier. -/
theorem finiteRectangle_squareSideRegular_radius_ne_double_double_re_sub
    (S : Finset ℂ) (ε : ℝ)
    (hregular : ε ∉ finiteRectangleSquareSideForbiddenRadii S)
    {a b : ℂ} (ha : a ∈ S) (hb : b ∈ S) :
    ε ≠ 2 * (2 * (a.re - b.re)) := by
  intro heq
  have hab : (a, b) ∈ S.product S :=
    Finset.mem_product.mpr (And.intro ha hb)
  have hvalue : 2 * (2 * (a.re - b.re)) ∈
      (S.product S).image
        (fun pair : ℂ × ℂ => 2 * (2 * (pair.1.re - pair.2.re))) :=
    Finset.mem_image.mpr
      (Exists.intro (a, b)
        (And.intro hab (Eq.refl (2 * (2 * (a.re - b.re))))))
  have hforbidden : 2 * (2 * (a.re - b.re)) ∈
      finiteRectangleSquareSideForbiddenRadii S :=
    Finset.mem_union_left
      ((S.product S).image
        (fun pair : ℂ × ℂ => 2 * (2 * (pair.1.im - pair.2.im))))
      hvalue
  exact hregular (Eq.subst
    (motive := fun value : ℝ =>
      value ∈ finiteRectangleSquareSideForbiddenRadii S)
    heq.symm hforbidden)

/-- A square-side regular radius is not four times any imaginary-coordinate separation
in the finite carrier. -/
theorem finiteRectangle_squareSideRegular_radius_ne_double_double_im_sub
    (S : Finset ℂ) (ε : ℝ)
    (hregular : ε ∉ finiteRectangleSquareSideForbiddenRadii S)
    {a b : ℂ} (ha : a ∈ S) (hb : b ∈ S) :
    ε ≠ 2 * (2 * (a.im - b.im)) := by
  intro heq
  have hab : (a, b) ∈ S.product S :=
    Finset.mem_product.mpr (And.intro ha hb)
  have hvalue : 2 * (2 * (a.im - b.im)) ∈
      (S.product S).image
        (fun pair : ℂ × ℂ => 2 * (2 * (pair.1.im - pair.2.im))) :=
    Finset.mem_image.mpr
      (Exists.intro (a, b)
        (And.intro hab (Eq.refl (2 * (2 * (a.im - b.im))))))
  have hforbidden : 2 * (2 * (a.im - b.im)) ∈
      finiteRectangleSquareSideForbiddenRadii S :=
    Finset.mem_union_right
      ((S.product S).image
        (fun pair : ℂ × ℂ => 2 * (2 * (pair.1.re - pair.2.re))))
      hvalue
  exact hregular (Eq.subst
    (motive := fun value : ℝ =>
      value ∈ finiteRectangleSquareSideForbiddenRadii S)
    heq.symm hforbidden)

/-- No listed singular coordinate lies on the lower horizontal side level of a listed
inscribed square. -/
theorem explicitFormulaRectangleRawInscribedSquareLowerCorner_im_ne_rawSingular
    (S : Finset ℂ) (ε : ℝ)
    (hregular : ε ∉ finiteRectangleSquareSideForbiddenRadii S)
    {a b : ℂ} (ha : a ∈ S) (hb : b ∈ S) :
    (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a).im ≠ b.im := by
  have hlevel : a.im - (ε / 2) / 2 ≠ b.im :=
    finiteRectangle_lower_quarter_level_ne ε a.im b.im
      (finiteRectangle_squareSideRegular_radius_ne_double_double_im_sub
        S ε hregular ha hb)
  intro heq
  exact hlevel
    (Eq.trans
      (explicitFormulaRectangleRawInscribedSquareLowerCorner_im (ε / 2) a).symm
      heq)

/-- No listed singular coordinate lies on the upper horizontal side level of a listed
inscribed square. -/
theorem explicitFormulaRectangleRawInscribedSquareUpperCorner_im_ne_rawSingular
    (S : Finset ℂ) (ε : ℝ)
    (hregular : ε ∉ finiteRectangleSquareSideForbiddenRadii S)
    {a b : ℂ} (ha : a ∈ S) (hb : b ∈ S) :
    (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a).im ≠ b.im := by
  have hlevel : a.im + (ε / 2) / 2 ≠ b.im :=
    finiteRectangle_upper_quarter_level_ne ε a.im b.im
      (finiteRectangle_squareSideRegular_radius_ne_double_double_im_sub
        S ε hregular hb ha)
  intro heq
  exact hlevel
    (Eq.trans
      (explicitFormulaRectangleRawInscribedSquareUpperCorner_im (ε / 2) a).symm
      heq)

/-- No listed singular coordinate lies on the left vertical side level of a listed
inscribed square. -/
theorem explicitFormulaRectangleRawInscribedSquareLowerCorner_re_ne_rawSingular
    (S : Finset ℂ) (ε : ℝ)
    (hregular : ε ∉ finiteRectangleSquareSideForbiddenRadii S)
    {a b : ℂ} (ha : a ∈ S) (hb : b ∈ S) :
    (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a).re ≠ b.re := by
  have hlevel : a.re - (ε / 2) / 2 ≠ b.re :=
    finiteRectangle_lower_quarter_level_ne ε a.re b.re
      (finiteRectangle_squareSideRegular_radius_ne_double_double_re_sub
        S ε hregular ha hb)
  intro heq
  exact hlevel
    (Eq.trans
      (explicitFormulaRectangleRawInscribedSquareLowerCorner_re (ε / 2) a).symm
      heq)

/-- No listed singular coordinate lies on the right vertical side level of a listed
inscribed square. -/
theorem explicitFormulaRectangleRawInscribedSquareUpperCorner_re_ne_rawSingular
    (S : Finset ℂ) (ε : ℝ)
    (hregular : ε ∉ finiteRectangleSquareSideForbiddenRadii S)
    {a b : ℂ} (ha : a ∈ S) (hb : b ∈ S) :
    (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a).re ≠ b.re := by
  have hlevel : a.re + (ε / 2) / 2 ≠ b.re :=
    finiteRectangle_upper_quarter_level_ne ε a.re b.re
      (finiteRectangle_squareSideRegular_radius_ne_double_double_re_sub
        S ε hregular hb ha)
  intro heq
  exact hlevel
    (Eq.trans
      (explicitFormulaRectangleRawInscribedSquareUpperCorner_re (ε / 2) a).symm
      heq)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
