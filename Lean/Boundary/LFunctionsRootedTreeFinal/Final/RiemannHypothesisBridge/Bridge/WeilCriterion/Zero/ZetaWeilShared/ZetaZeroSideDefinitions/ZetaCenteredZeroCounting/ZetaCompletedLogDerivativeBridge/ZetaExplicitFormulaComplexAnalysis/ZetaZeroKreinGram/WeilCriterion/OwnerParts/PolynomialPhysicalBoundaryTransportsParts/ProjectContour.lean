import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaHorizontalEdgeBounds.ScheduledPolynomialGrowth
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ScheduledNormalizedContourResidueLimit

/-!
# Polynomial scheduled project-contour transport

This file owns the generic fixed-degree scheduled contour algebra used by the
physical autocorrelation boundary transport.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The horizontal side contribution determined by a polynomial scheduled
analytic package. -/
noncomputable def explicitFormulaPolynomialScheduledPackageHorizontalSideDifference
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage f F)
    (u : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaTopLineIntegral f
      (F.rectangle (h.height_schedule.height u)) -
    zetaCompletedExplicitFormulaBottomLineIntegral f
      (F.rectangle (h.height_schedule.height u))

/-- Polynomial scheduled horizontal-side decay, exported under the
side-difference name. -/
theorem explicitFormulaPolynomialScheduledPackageHorizontalSideDifference_tendsto_zero
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaPolynomialScheduledPackageHorizontalSideDifference h u)
      atTop
      (𝓝 (0 : ℂ)) :=
  zetaCompletedExplicitFormulaHorizontalDifference_tendsto_zero_of_polynomialScheduledPackage
    h

/-- The polynomial scheduled normalized vertical side is the normalized
pole-corrected project contour minus the normalized horizontal side. -/
theorem explicitFormulaPolynomialScheduledPackageNormalizedPoleCorrectedVerticalDifference_eq_contour_sub_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage f F)
    (u : ℝ) :
    (zetaCompletedExplicitFormulaRightLineIntegral f
          (F.rectangle (h.height_schedule.height u)) -
        zetaCompletedExplicitFormulaLeftLineIntegral f
          (F.rectangle (h.height_schedule.height u))) /
        explicitFormulaTwoPi -
      explicitFormulaRectangle_completedPoleResidueSum f =
        explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral
            f F (h.height_schedule.height u) -
          explicitFormulaPolynomialScheduledPackageHorizontalSideDifference h u /
            explicitFormulaTwoPi :=
  let vertical : ℂ :=
    zetaCompletedExplicitFormulaRightLineIntegral f
        (F.rectangle (h.height_schedule.height u)) -
      zetaCompletedExplicitFormulaLeftLineIntegral f
        (F.rectangle (h.height_schedule.height u))
  let horizontal : ℂ :=
    explicitFormulaPolynomialScheduledPackageHorizontalSideDifference h u
  let poles : ℂ := explicitFormulaRectangle_completedPoleResidueSum f
  let hcontour :
      zetaCompletedExplicitFormulaContourIntegral f
          (F.rectangle (h.height_schedule.height u)) =
        vertical + horizontal :=
    Eq.trans
      (zetaCompletedExplicitFormulaContourIntegral_eq
        f (F.rectangle (h.height_schedule.height u)))
      (Eq.trans
        (explicitFormula_four_side_project_split
          (zetaCompletedExplicitFormulaRightLineIntegral f
            (F.rectangle (h.height_schedule.height u)))
          (zetaCompletedExplicitFormulaLeftLineIntegral f
            (F.rectangle (h.height_schedule.height u)))
          (zetaCompletedExplicitFormulaTopLineIntegral f
            (F.rectangle (h.height_schedule.height u)))
          (zetaCompletedExplicitFormulaBottomLineIntegral f
            (F.rectangle (h.height_schedule.height u))))
        (Eq.refl (vertical + horizontal)))
  let hdivision :
      (vertical + horizontal) / explicitFormulaTwoPi =
        vertical / explicitFormulaTwoPi +
          horizontal / explicitFormulaTwoPi :=
    add_div vertical horizontal explicitFormulaTwoPi
  calc
    vertical / explicitFormulaTwoPi - poles =
        (vertical / explicitFormulaTwoPi +
          horizontal / explicitFormulaTwoPi - poles) -
        horizontal / explicitFormulaTwoPi :=
      (explicitFormula_add_sub_sub_right
        (vertical / explicitFormulaTwoPi)
        (horizontal / explicitFormulaTwoPi)
        poles).symm
    _ = ((vertical + horizontal) / explicitFormulaTwoPi - poles) -
          horizontal / explicitFormulaTwoPi :=
      congrArg
        (fun value : ℂ => (value - poles) -
          horizontal / explicitFormulaTwoPi)
        hdivision.symm
    _ =
        (zetaCompletedExplicitFormulaContourIntegral f
            (F.rectangle (h.height_schedule.height u)) /
            explicitFormulaTwoPi - poles) -
          horizontal / explicitFormulaTwoPi :=
      congrArg
        (fun value : ℂ => (value / explicitFormulaTwoPi - poles) -
          horizontal / explicitFormulaTwoPi)
        hcontour.symm
    _ = explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral
          f F (h.height_schedule.height u) -
        explicitFormulaPolynomialScheduledPackageHorizontalSideDifference h u /
          explicitFormulaTwoPi :=
      Eq.refl _

/-- Pointwise normalized tangent-residue equality at positive polynomial
scheduled heights supplies the eventual tangent-residue equality consumed by
the polynomial zero-side endpoint. -/
theorem explicitFormulaRectangle_poleCorrectedResidueSum_eventually_eq_normalizedTangent_of_polynomialScheduledPackage_pointwise
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage f F)
    (pointwise :
      ∀ u : ℝ,
        0 < h.height_schedule.height u →
          zetaCompletedExplicitFormulaNormalizedTangentContourIntegral f
              (F.rectangle (h.height_schedule.height u)) =
            explicitFormulaRectangle_poleCorrectedResidueSum f
              (h.height_schedule.height u)) :
    ∀ᶠ u in atTop,
      explicitFormulaRectangle_poleCorrectedResidueSum f
          (h.height_schedule.height u) =
        zetaCompletedExplicitFormulaNormalizedTangentContourIntegral f
          (F.rectangle (h.height_schedule.height u)) :=
  h.height_schedule.eventually_height_pos.mono
    (fun u heightPositive =>
      (pointwise u heightPositive).symm)

/-- Pointwise raw Cauchy tangent-residue equality at positive polynomial
scheduled heights supplies the eventual normalized tangent-residue equality. -/
theorem explicitFormulaRectangle_poleCorrectedResidueSum_eventually_eq_normalizedTangent_of_polynomialScheduledPackage_rawPointwise
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage f F)
    (rawPointwise :
      ∀ u : ℝ,
        0 < h.height_schedule.height u →
          zetaCompletedExplicitFormulaTangentContourIntegral f
              (F.rectangle (h.height_schedule.height u)) =
            explicitFormulaTwoPiI •
              explicitFormulaRectangle_poleCorrectedResidueSum f
                (h.height_schedule.height u)) :
    ∀ᶠ u in atTop,
      explicitFormulaRectangle_poleCorrectedResidueSum f
          (h.height_schedule.height u) =
        zetaCompletedExplicitFormulaNormalizedTangentContourIntegral f
          (F.rectangle (h.height_schedule.height u)) :=
  explicitFormulaRectangle_poleCorrectedResidueSum_eventually_eq_normalizedTangent_of_polynomialScheduledPackage_pointwise
    f
    F
    h
    (fun u heightPositive =>
      zetaCompletedExplicitFormulaNormalizedTangentContourIntegral_eq_residueSum
        f
        (F.rectangle (h.height_schedule.height u))
        (explicitFormulaRectangle_poleCorrectedResidueSum f
          (h.height_schedule.height u))
        (rawPointwise u heightPositive))

/-- A normalized tangent residue limit and polynomial scheduled horizontal
decay imply the same residue limit for the normalized project-oriented
contour. -/
theorem zetaCompletedExplicitFormulaNormalizedContourIntegral_tendsto_of_polynomialScheduledPackage_tangent_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage f F)
    (residueSum : ℂ)
    (tangentLimit :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaNormalizedTangentContourIntegral f
            (F.rectangle (h.height_schedule.height u)))
        atTop
        (𝓝 residueSum)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaNormalizedContourIntegral f
          (F.rectangle (h.height_schedule.height u)))
      atTop
      (𝓝 residueSum) :=
  let rawTangentLimit :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaTangentContourIntegral f
            (F.rectangle (h.height_schedule.height u)))
        atTop
        (𝓝 (explicitFormulaTwoPiI * residueSum)) :=
    let scaledLimit :
        Tendsto
          (fun u : ℝ =>
            explicitFormulaTwoPiI *
              zetaCompletedExplicitFormulaNormalizedTangentContourIntegral f
                (F.rectangle (h.height_schedule.height u)))
          atTop
          (𝓝 (explicitFormulaTwoPiI * residueSum)) :=
      tangentLimit.const_mul explicitFormulaTwoPiI
    let pointwiseEquality :
        (fun u : ℝ =>
          explicitFormulaTwoPiI *
            zetaCompletedExplicitFormulaNormalizedTangentContourIntegral f
              (F.rectangle (h.height_schedule.height u))) =
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaTangentContourIntegral f
            (F.rectangle (h.height_schedule.height u))) :=
      funext
        (fun u : ℝ =>
          let rightDivision :
              zetaCompletedExplicitFormulaNormalizedTangentContourIntegral f
                  (F.rectangle (h.height_schedule.height u)) *
                explicitFormulaTwoPiI =
              zetaCompletedExplicitFormulaTangentContourIntegral f
                (F.rectangle (h.height_schedule.height u)) :=
            (eq_div_iff explicitFormulaTwoPiI_ne_zero).mp
              (Eq.refl
                (zetaCompletedExplicitFormulaNormalizedTangentContourIntegral f
                  (F.rectangle (h.height_schedule.height u))))
          Eq.trans
            (mul_comm explicitFormulaTwoPiI
              (zetaCompletedExplicitFormulaNormalizedTangentContourIntegral f
                (F.rectangle (h.height_schedule.height u))))
            rightDivision)
    Eq.subst
      (motive := fun values : ℝ → ℂ =>
        Tendsto values atTop (𝓝 (explicitFormulaTwoPiI * residueSum)))
      pointwiseEquality
      scaledLimit
  let rotatedTangentLimit :
      Tendsto
        (fun u : ℝ =>
          (-Complex.I) *
            zetaCompletedExplicitFormulaTangentContourIntegral f
              (F.rectangle (h.height_schedule.height u)))
        atTop
        (𝓝 (explicitFormulaTwoPi * residueSum)) :=
    let baseLimit :=
      rawTangentLimit.const_mul (-Complex.I)
    Eq.subst
      (motive := fun target : ℂ =>
        Tendsto
          (fun u : ℝ =>
            (-Complex.I) *
              zetaCompletedExplicitFormulaTangentContourIntegral f
                (F.rectangle (h.height_schedule.height u)))
          atTop
          (𝓝 target))
      (explicitFormula_negI_mul_twoPiI_mul residueSum)
      baseLimit
  let horizontalLimit :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaPolynomialScheduledPackageHorizontalSideDifference h u)
        atTop
        (𝓝 (0 : ℂ)) :=
    explicitFormulaPolynomialScheduledPackageHorizontalSideDifference_tendsto_zero h
  let correctionLimit :
      Tendsto
        (fun u : ℝ =>
          ((1 : ℂ) - Complex.I) *
            explicitFormulaPolynomialScheduledPackageHorizontalSideDifference h u)
        atTop
        (𝓝 (0 : ℂ)) :=
    let baseLimit :=
      horizontalLimit.const_mul ((1 : ℂ) - Complex.I)
    Eq.subst
      (motive := fun target : ℂ =>
        Tendsto
          (fun u : ℝ =>
            ((1 : ℂ) - Complex.I) *
              explicitFormulaPolynomialScheduledPackageHorizontalSideDifference h u)
          atTop
          (𝓝 target))
      (mul_zero ((1 : ℂ) - Complex.I))
      baseLimit
  let rawProjectLimit :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaContourIntegral f
            (F.rectangle (h.height_schedule.height u)))
        atTop
        (𝓝 (explicitFormulaTwoPi * residueSum)) :=
    let sumLimit :
        Tendsto
          (fun u : ℝ =>
            (-Complex.I) *
                zetaCompletedExplicitFormulaTangentContourIntegral f
                  (F.rectangle (h.height_schedule.height u)) +
              ((1 : ℂ) - Complex.I) *
                explicitFormulaPolynomialScheduledPackageHorizontalSideDifference h u)
          atTop
          (𝓝 (explicitFormulaTwoPi * residueSum + 0)) :=
      rotatedTangentLimit.add correctionLimit
    let targetEquality :
        explicitFormulaTwoPi * residueSum + 0 =
          explicitFormulaTwoPi * residueSum :=
      add_zero (explicitFormulaTwoPi * residueSum)
    let pointwiseEquality :
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaContourIntegral f
            (F.rectangle (h.height_schedule.height u))) =
        (fun u : ℝ =>
          (-Complex.I) *
              zetaCompletedExplicitFormulaTangentContourIntegral f
                (F.rectangle (h.height_schedule.height u)) +
            ((1 : ℂ) - Complex.I) *
              explicitFormulaPolynomialScheduledPackageHorizontalSideDifference h u) :=
      funext
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaContourIntegral_eq_negI_mul_tangent_add_horizontalCorrection
            f
            (F.rectangle (h.height_schedule.height u)))
    Eq.subst
      (motive := fun values : ℝ → ℂ =>
        Tendsto values atTop (𝓝 (explicitFormulaTwoPi * residueSum)))
      pointwiseEquality.symm
      (Eq.subst
        (motive := fun target : ℂ =>
          Tendsto
            (fun u : ℝ =>
              (-Complex.I) *
                  zetaCompletedExplicitFormulaTangentContourIntegral f
                    (F.rectangle (h.height_schedule.height u)) +
                ((1 : ℂ) - Complex.I) *
                  explicitFormulaPolynomialScheduledPackageHorizontalSideDifference h u)
            atTop
            (𝓝 target))
        targetEquality
        sumLimit)
  let normalizedProjectLimit :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaContourIntegral f
              (F.rectangle (h.height_schedule.height u)) /
            explicitFormulaTwoPi)
        atTop
        (𝓝 ((explicitFormulaTwoPi * residueSum) / explicitFormulaTwoPi)) :=
    rawProjectLimit.div_const explicitFormulaTwoPi
  let targetEquality :
      (explicitFormulaTwoPi * residueSum) / explicitFormulaTwoPi =
        residueSum :=
    Eq.trans
      (congrArg
        (fun value : ℂ => value / explicitFormulaTwoPi)
        (mul_comm explicitFormulaTwoPi residueSum))
      (mul_div_cancel_right₀ residueSum explicitFormulaTwoPi_ne_zero)
  Eq.subst
    (motive := fun target : ℂ =>
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaNormalizedContourIntegral f
            (F.rectangle (h.height_schedule.height u)))
        atTop
        (𝓝 target))
    targetEquality
    normalizedProjectLimit

/-- Polynomial scheduled tangent-residue equality gives normalized
project-contour convergence to the completed zero-side plus completed-pole
packet. -/
theorem explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral_tendsto_zeroSideComplex_of_polynomialScheduledPackage_tangentEventual
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage f F)
    (tangentEventual :
      ∀ᶠ u in atTop,
        explicitFormulaRectangle_poleCorrectedResidueSum f
            (h.height_schedule.height u) =
          zetaCompletedExplicitFormulaNormalizedTangentContourIntegral f
            (F.rectangle (h.height_schedule.height u)))
    (zeroSideSummable :
      Summable
        (fun rho : {rho : ℂ // ZetaCompletedZero rho} =>
          zetaZeroSideContribution (rho : ℂ) f)) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedZeroSideComplex f)) :=
  let polePacket : ℂ := explicitFormulaRectangle_completedPoleResidueSum f
  let poleLimit :
      Tendsto
        (fun value : ℝ => polePacket)
        atTop
        (𝓝 polePacket) :=
    tendsto_const_nhds
  let poleCorrectedResidueLimit :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaRectangle_poleCorrectedResidueSum f
            (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedZeroSideComplex f + polePacket)) :=
    explicitFormulaRectangle_poleCorrectedResidueSum_tendsto_zeroSideComplex_add_poles
      f F h.height_schedule zeroSideSummable
  let tangentLimit :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaNormalizedTangentContourIntegral f
            (F.rectangle (h.height_schedule.height u)))
        atTop
        (𝓝 (zetaCompletedZeroSideComplex f + polePacket)) :=
    poleCorrectedResidueLimit.congr' tangentEventual
  let projectLimit :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaNormalizedContourIntegral f
            (F.rectangle (h.height_schedule.height u)))
        atTop
        (𝓝 (zetaCompletedZeroSideComplex f + polePacket)) :=
    zetaCompletedExplicitFormulaNormalizedContourIntegral_tendsto_of_polynomialScheduledPackage_tangent_horizontal
      f F h (zetaCompletedZeroSideComplex f + polePacket) tangentLimit
  let correctedLimit :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaNormalizedContourIntegral f
              (F.rectangle (h.height_schedule.height u)) -
            polePacket)
        atTop
        (𝓝 (zetaCompletedZeroSideComplex f + polePacket - polePacket)) :=
    projectLimit.sub poleLimit
  let targetEquality :
      zetaCompletedZeroSideComplex f + polePacket - polePacket =
        zetaCompletedZeroSideComplex f :=
    add_sub_cancel_right (zetaCompletedZeroSideComplex f) polePacket
  Eq.subst
    (motive := fun target : ℂ =>
      Tendsto
        (fun u : ℝ =>
          explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 target))
    targetEquality
    correctedLimit

/-- A polynomial scheduled normalized project-contour zero-side limit gives the
polynomial scheduled vertical zero-side endpoint. -/
theorem explicitFormulaPolynomialScheduledPackageNormalizedPoleCorrectedVerticalDifference_tendsto_zeroSideComplex_of_projectContourLimit
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage f F)
    (projectLimit :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedZeroSideComplex f))) :
    Tendsto
      (fun u : ℝ =>
        (zetaCompletedExplicitFormulaRightLineIntegral f
              (F.rectangle (h.height_schedule.height u)) -
            zetaCompletedExplicitFormulaLeftLineIntegral f
              (F.rectangle (h.height_schedule.height u))) /
            explicitFormulaTwoPi -
          explicitFormulaRectangle_completedPoleResidueSum f)
      atTop
      (𝓝 (zetaCompletedZeroSideComplex f)) :=
  let horizontalLimit :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaPolynomialScheduledPackageHorizontalSideDifference h u)
        atTop
        (𝓝 (0 : ℂ)) :=
    explicitFormulaPolynomialScheduledPackageHorizontalSideDifference_tendsto_zero h
  let normalizedHorizontalLimit :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaPolynomialScheduledPackageHorizontalSideDifference h u /
            explicitFormulaTwoPi)
        atTop
        (𝓝 ((0 : ℂ) / explicitFormulaTwoPi)) :=
    horizontalLimit.div_const explicitFormulaTwoPi
  let differenceLimit :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral
              f F (h.height_schedule.height u) -
            explicitFormulaPolynomialScheduledPackageHorizontalSideDifference h u /
              explicitFormulaTwoPi)
        atTop
        (𝓝 (zetaCompletedZeroSideComplex f - (0 : ℂ) / explicitFormulaTwoPi)) :=
    projectLimit.sub normalizedHorizontalLimit
  let zeroDivision :
      (0 : ℂ) / explicitFormulaTwoPi = 0 :=
    zero_div explicitFormulaTwoPi
  let targetEquality :
      zetaCompletedZeroSideComplex f - (0 : ℂ) / explicitFormulaTwoPi =
        zetaCompletedZeroSideComplex f :=
    Eq.trans
      (congrArg
        (fun term : ℂ => zetaCompletedZeroSideComplex f - term)
        zeroDivision)
      (sub_zero (zetaCompletedZeroSideComplex f))
  let functionEquality :
      (fun u : ℝ =>
        explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral
            f F (h.height_schedule.height u) -
          explicitFormulaPolynomialScheduledPackageHorizontalSideDifference h u /
            explicitFormulaTwoPi) =
      (fun u : ℝ =>
        (zetaCompletedExplicitFormulaRightLineIntegral f
              (F.rectangle (h.height_schedule.height u)) -
            zetaCompletedExplicitFormulaLeftLineIntegral f
              (F.rectangle (h.height_schedule.height u))) /
            explicitFormulaTwoPi -
          explicitFormulaRectangle_completedPoleResidueSum f) :=
    funext
      (fun u : ℝ =>
        (explicitFormulaPolynomialScheduledPackageNormalizedPoleCorrectedVerticalDifference_eq_contour_sub_horizontal
          f F h u).symm)
  Eq.subst
    (motive := fun values : ℝ → ℂ =>
      Tendsto values atTop (𝓝 (zetaCompletedZeroSideComplex f)))
    functionEquality
    (Eq.subst
      (motive := fun target : ℂ =>
        Tendsto
          (fun u : ℝ =>
            explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral
                f F (h.height_schedule.height u) -
              explicitFormulaPolynomialScheduledPackageHorizontalSideDifference h u /
                explicitFormulaTwoPi)
          atTop
          (𝓝 target))
      targetEquality
      differenceLimit)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
