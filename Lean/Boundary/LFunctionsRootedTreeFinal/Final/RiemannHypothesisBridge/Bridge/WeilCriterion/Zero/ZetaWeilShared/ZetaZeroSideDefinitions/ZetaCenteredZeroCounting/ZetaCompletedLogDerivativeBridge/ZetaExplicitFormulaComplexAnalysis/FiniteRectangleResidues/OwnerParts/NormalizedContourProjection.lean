import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.SelectedRadiusResidueAssembly

/-!
# Normalized Cauchy contour projection
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The real `2 pi` contour normalization as a complex scalar. -/
noncomputable def explicitFormulaTwoPi : ℂ := 2 * (Real.pi : ℂ)

/-- The Cauchy `2 pi i` contour normalization as a complex scalar. -/
noncomputable def explicitFormulaTwoPiI : ℂ := explicitFormulaTwoPi * Complex.I

/-- The project-oriented contour divided by its real `2 pi` normalization. -/
noncomputable def zetaCompletedExplicitFormulaNormalizedContourIntegral
    (f : ZetaAdmissibleFunction) (rectangle : ExplicitFormulaRectangle) : ℂ :=
  zetaCompletedExplicitFormulaContourIntegral f rectangle / explicitFormulaTwoPi

/-- The tangent-oriented Cauchy contour divided by `2 pi i`. -/
noncomputable def zetaCompletedExplicitFormulaNormalizedTangentContourIntegral
    (f : ZetaAdmissibleFunction) (rectangle : ExplicitFormulaRectangle) : ℂ :=
  zetaCompletedExplicitFormulaTangentContourIntegral f rectangle / explicitFormulaTwoPiI

/-- The normalized project contour with the two completed-zeta pole residues removed. -/
noncomputable def explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaNormalizedContourIntegral f (F.rectangle T) -
    explicitFormulaRectangle_completedPoleResidueSum f

/-- The real contour normalization is nonzero. -/
theorem explicitFormulaTwoPi_ne_zero : explicitFormulaTwoPi ≠ 0 := by
  exact mul_ne_zero
    (Complex.ofReal_ne_zero.mpr two_ne_zero)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)

/-- The Cauchy contour normalization is nonzero. -/
theorem explicitFormulaTwoPiI_ne_zero : explicitFormulaTwoPiI ≠ 0 := by
  exact mul_ne_zero explicitFormulaTwoPi_ne_zero Complex.I_ne_zero

/-- Multiplication by negative `i` rotates a tangent vertical-minus-horizontal packet
back to an ordinary vertical-plus-rotated-horizontal packet. -/
theorem explicitFormula_negI_mul_tangentPacket
    (vertical horizontal : ℂ) :
    (-Complex.I) * (Complex.I * vertical - horizontal) =
      vertical + Complex.I * horizontal := by
  have hnegI_mul_I : (-Complex.I) * Complex.I = (1 : ℂ) := by
    calc
      (-Complex.I) * Complex.I = -(Complex.I * Complex.I) := by
        exact neg_mul Complex.I Complex.I
      _ = -(-(1 : ℂ)) := by
        exact congrArg Neg.neg Complex.I_mul_I
      _ = 1 := neg_neg 1
  calc
    (-Complex.I) * (Complex.I * vertical - horizontal) =
        (-Complex.I) * (Complex.I * vertical) -
          (-Complex.I) * horizontal := by
      exact mul_sub (-Complex.I) (Complex.I * vertical) horizontal
    _ = ((-Complex.I) * Complex.I) * vertical -
          (-Complex.I) * horizontal := by
      exact congrArg
        (fun value : ℂ => value - (-Complex.I) * horizontal)
        (mul_assoc (-Complex.I) Complex.I vertical).symm
    _ = 1 * vertical - (-Complex.I) * horizontal := by
      exact congrArg
        (fun value : ℂ => value * vertical - (-Complex.I) * horizontal)
        hnegI_mul_I
    _ = vertical - (-Complex.I) * horizontal := by
      exact congrArg (fun value : ℂ => value - (-Complex.I) * horizontal)
        (one_mul vertical)
    _ = vertical - (-(Complex.I * horizontal)) := by
      exact congrArg (fun value : ℂ => vertical - value)
        (neg_mul Complex.I horizontal)
    _ = vertical + Complex.I * horizontal := sub_neg_eq_add vertical (Complex.I * horizontal)

/-- The ordinary project contour is the negative-`i` rotation of the tangent contour plus
the exact horizontal orientation correction. -/
theorem explicitFormula_projectContour_of_tangentPacket
    (vertical horizontal tangent project : ℂ)
    (htangent : tangent = Complex.I * vertical - horizontal)
    (hproject : project = vertical + horizontal) :
    project =
      (-Complex.I) * tangent + ((1 : ℂ) - Complex.I) * horizontal := by
  have hrotate :
      (-Complex.I) * tangent = vertical + Complex.I * horizontal := by
    exact Eq.trans
      (congrArg (fun value : ℂ => (-Complex.I) * value) htangent)
      (explicitFormula_negI_mul_tangentPacket vertical horizontal)
  calc
    project = vertical + horizontal := hproject
    _ = (vertical + Complex.I * horizontal) +
          (horizontal - Complex.I * horizontal) := by
      calc
        vertical + horizontal = vertical +
            (Complex.I * horizontal +
              (horizontal - Complex.I * horizontal)) := by
          exact congrArg (fun value : ℂ => vertical + value)
            (add_sub_cancel_left (Complex.I * horizontal) horizontal).symm
        _ = (vertical + Complex.I * horizontal) +
            (horizontal - Complex.I * horizontal) := by
          exact (add_assoc vertical (Complex.I * horizontal)
            (horizontal - Complex.I * horizontal)).symm
    _ = (-Complex.I) * tangent +
          (horizontal - Complex.I * horizontal) := by
      exact congrArg
        (fun value : ℂ => value + (horizontal - Complex.I * horizontal))
        hrotate.symm
    _ = (-Complex.I) * tangent + ((1 : ℂ) - Complex.I) * horizontal := by
      have hcorrection :
          ((1 : ℂ) - Complex.I) * horizontal =
            horizontal - Complex.I * horizontal := by
        calc
          ((1 : ℂ) - Complex.I) * horizontal =
              1 * horizontal - Complex.I * horizontal := by
            exact sub_mul 1 Complex.I horizontal
          _ = horizontal - Complex.I * horizontal := by
            exact congrArg (fun value : ℂ => value - Complex.I * horizontal)
              (one_mul horizontal)
      exact congrArg (fun value : ℂ => (-Complex.I) * tangent + value)
        hcorrection.symm

/-- Dividing the raw Cauchy residue identity by `2 pi i` gives the exact normalized
tangent residue identity. -/
theorem zetaCompletedExplicitFormulaNormalizedTangentContourIntegral_eq_residueSum
    (f : ZetaAdmissibleFunction) (rectangle : ExplicitFormulaRectangle) (residueSum : ℂ)
    (hraw :
      zetaCompletedExplicitFormulaTangentContourIntegral f rectangle =
        explicitFormulaTwoPiI • residueSum) :
    zetaCompletedExplicitFormulaNormalizedTangentContourIntegral f rectangle = residueSum := by
  have hmul :
      zetaCompletedExplicitFormulaTangentContourIntegral f rectangle =
        residueSum * explicitFormulaTwoPiI := by
    exact Eq.trans hraw
      (Eq.trans
        (Algebra.id.smul_eq_mul explicitFormulaTwoPiI residueSum)
        (mul_comm explicitFormulaTwoPiI residueSum))
  exact (div_eq_iff explicitFormulaTwoPiI_ne_zero).mpr hmul

/-- The selected-radius raw tangent theorem becomes the exact normalized pole-corrected
residue sum. -/
theorem zetaCompletedExplicitFormulaNormalizedTangentContourIntegral_eq_poleCorrectedResidueSum_selected
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) {u : ℝ}
    (hT : 0 < h.height_schedule.height u)
    (hinterior :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        rho ∈ explicitFormulaCompletedZeroContourHeightWindow (h.height_schedule.height u) ↔
          completedZeroResidueCoordinate rho ∈
              explicitFormulaContourFamilyInterior F (h.height_schedule.height u) ∧
            completedZeroResidueCoordinate rho ∈ completedZetaContourIntegrandSingularSet) :
    zetaCompletedExplicitFormulaNormalizedTangentContourIntegral f
        (F.rectangle (h.height_schedule.height u)) =
      explicitFormulaRectangle_poleCorrectedResidueSum f (h.height_schedule.height u) := by
  have hraw :=
    zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_selected
      f F h hT hinterior
  have hscalar : (2 * ↑Real.pi * Complex.I : ℂ) = explicitFormulaTwoPiI := Eq.refl _
  have hnormalizedRaw :
      zetaCompletedExplicitFormulaTangentContourIntegral f
          (F.rectangle (h.height_schedule.height u)) =
        explicitFormulaTwoPiI •
          explicitFormulaRectangle_poleCorrectedResidueSum f
            (h.height_schedule.height u) :=
    Eq.subst
      (motive := fun scalar : ℂ =>
        zetaCompletedExplicitFormulaTangentContourIntegral f
            (F.rectangle (h.height_schedule.height u)) =
          scalar • explicitFormulaRectangle_poleCorrectedResidueSum f
            (h.height_schedule.height u))
      hscalar hraw
  exact
    zetaCompletedExplicitFormulaNormalizedTangentContourIntegral_eq_residueSum
      f (F.rectangle (h.height_schedule.height u))
      (explicitFormulaRectangle_poleCorrectedResidueSum f (h.height_schedule.height u))
      hnormalizedRaw

/-- The concrete ordinary rectangle contour is the rotated tangent contour plus the exact
horizontal orientation correction. -/
theorem zetaCompletedExplicitFormulaContourIntegral_eq_negI_mul_tangent_add_horizontalCorrection
    (f : ZetaAdmissibleFunction) (rectangle : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaContourIntegral f rectangle =
      (-Complex.I) * zetaCompletedExplicitFormulaTangentContourIntegral f rectangle +
        ((1 : ℂ) - Complex.I) *
          (zetaCompletedExplicitFormulaTopLineIntegral f rectangle -
            zetaCompletedExplicitFormulaBottomLineIntegral f rectangle) := by
  let right : ℂ := zetaCompletedExplicitFormulaRightLineIntegral f rectangle
  let left : ℂ := zetaCompletedExplicitFormulaLeftLineIntegral f rectangle
  let top : ℂ := zetaCompletedExplicitFormulaTopLineIntegral f rectangle
  let bottom : ℂ := zetaCompletedExplicitFormulaBottomLineIntegral f rectangle
  let vertical : ℂ := right - left
  let horizontal : ℂ := top - bottom
  have htangentVertical : right * Complex.I - left * Complex.I =
      Complex.I * vertical := by
    calc
      right * Complex.I - left * Complex.I =
          (right - left) * Complex.I := by
        exact (sub_mul right left Complex.I).symm
      _ = Complex.I * (right - left) := mul_comm (right - left) Complex.I
      _ = Complex.I * vertical := Eq.refl _
  have hbottomTop : bottom - top = -horizontal := by
    exact Eq.trans (neg_sub top bottom).symm (congrArg Neg.neg (Eq.refl horizontal))
  have htangent :
      zetaCompletedExplicitFormulaTangentContourIntegral f rectangle =
        Complex.I * vertical - horizontal := by
    calc
      zetaCompletedExplicitFormulaTangentContourIntegral f rectangle =
          bottom - top + (right * Complex.I - left * Complex.I) := by
        exact zetaCompletedExplicitFormulaTangentContourIntegral_eq f rectangle
      _ = -horizontal + Complex.I * vertical := by
        exact congrArg₂ (fun first second : ℂ => first + second)
          hbottomTop htangentVertical
      _ = Complex.I * vertical + -horizontal := add_comm (-horizontal) (Complex.I * vertical)
      _ = Complex.I * vertical - horizontal :=
        (sub_eq_add_neg (Complex.I * vertical) horizontal).symm
  have hproject :
      zetaCompletedExplicitFormulaContourIntegral f rectangle = vertical + horizontal := by
    calc
      zetaCompletedExplicitFormulaContourIntegral f rectangle =
          right - left + top - bottom :=
        zetaCompletedExplicitFormulaContourIntegral_eq f rectangle
      _ = (right - left) + (top - bottom) :=
        calc
          right - left + top - bottom = (right - left + top) + -bottom :=
            sub_eq_add_neg (right - left + top) bottom
          _ = (right - left) + (top + -bottom) :=
            add_assoc (right - left) top (-bottom)
          _ = (right - left) + (top - bottom) := by
            exact congrArg (fun value : ℂ => (right - left) + value)
              (sub_eq_add_neg top bottom).symm
      _ = vertical + horizontal := Eq.refl _
  exact
    explicitFormula_projectContour_of_tangentPacket
      vertical horizontal
      (zetaCompletedExplicitFormulaTangentContourIntegral f rectangle)
      (zetaCompletedExplicitFormulaContourIntegral f rectangle)
      htangent hproject

/-- The two contour normalizations satisfy `2 pi i = (2 pi) * i`. -/
theorem explicitFormulaTwoPiI_eq_twoPi_mul_I :
    explicitFormulaTwoPiI = explicitFormulaTwoPi * Complex.I := Eq.refl _

/-- Rotating a `2 pi i` multiple by negative `i` gives the corresponding `2 pi`
multiple. -/
theorem explicitFormula_negI_mul_twoPiI_mul (value : ℂ) :
    (-Complex.I) * (explicitFormulaTwoPiI * value) = explicitFormulaTwoPi * value := by
  have hnegI_mul_I : (-Complex.I) * Complex.I = (1 : ℂ) := by
    calc
      (-Complex.I) * Complex.I = -(Complex.I * Complex.I) := neg_mul Complex.I Complex.I
      _ = -(-(1 : ℂ)) := congrArg Neg.neg Complex.I_mul_I
      _ = 1 := neg_neg 1
  calc
    (-Complex.I) * (explicitFormulaTwoPiI * value) =
        (-Complex.I) * ((explicitFormulaTwoPi * Complex.I) * value) := Eq.refl _
    _ = ((-Complex.I) * (explicitFormulaTwoPi * Complex.I)) * value :=
      (mul_assoc (-Complex.I) (explicitFormulaTwoPi * Complex.I) value).symm
    _ = (((-Complex.I) * explicitFormulaTwoPi) * Complex.I) * value := by
      exact congrArg (fun scalar : ℂ => scalar * value)
        (mul_assoc (-Complex.I) explicitFormulaTwoPi Complex.I).symm
    _ = ((explicitFormulaTwoPi * (-Complex.I)) * Complex.I) * value := by
      exact congrArg (fun scalar : ℂ => (scalar * Complex.I) * value)
        (mul_comm (-Complex.I) explicitFormulaTwoPi)
    _ = (explicitFormulaTwoPi * ((-Complex.I) * Complex.I)) * value := by
      exact congrArg (fun scalar : ℂ => scalar * value)
        (mul_assoc explicitFormulaTwoPi (-Complex.I) Complex.I)
    _ = (explicitFormulaTwoPi * 1) * value := by
      exact congrArg (fun scalar : ℂ => (explicitFormulaTwoPi * scalar) * value)
        hnegI_mul_I
    _ = explicitFormulaTwoPi * value := by
      exact congrArg (fun scalar : ℂ => scalar * value) (mul_one explicitFormulaTwoPi)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
