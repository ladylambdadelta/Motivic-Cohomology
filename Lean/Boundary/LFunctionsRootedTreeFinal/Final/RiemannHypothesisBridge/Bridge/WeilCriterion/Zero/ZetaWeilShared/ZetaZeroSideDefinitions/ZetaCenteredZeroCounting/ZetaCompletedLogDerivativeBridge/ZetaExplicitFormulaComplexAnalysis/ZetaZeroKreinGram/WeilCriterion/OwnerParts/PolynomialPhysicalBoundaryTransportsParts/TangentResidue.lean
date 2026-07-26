import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PolynomialPhysicalBoundaryTransportsParts.ProjectContour
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.ScheduledSelectedRadiusResidueClosedGeometry

/-!
# Polynomial scheduled tangent residue equality

This file owns the selected-radius residue theorem for fixed-degree polynomial
scheduled packages.  It uses the local transform-control field directly and
does not promote the polynomial package to a full scheduled analytic package.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Polynomial scheduled finite-hole Cauchy at one selected square-side regular
radius. -/
theorem explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_polynomialScheduledPackage_selectedRegularRadius
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage f F) {u epsilon : ℝ}
    (hT : 0 < h.height_schedule.height u) (hepsilon : 0 < epsilon)
    (hinterior :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        rho ∈ explicitFormulaCompletedZeroContourHeightWindow
            (h.height_schedule.height u) ↔
          completedZeroResidueCoordinate rho ∈
              explicitFormulaContourFamilyInterior F (h.height_schedule.height u) ∧
            completedZeroResidueCoordinate rho ∈ completedZetaContourIntegrandSingularSet)
    (hboundaryRegular :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F (h.height_schedule.height u) →
          ContinuousAt
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hboundaryAvoidance :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F (h.height_schedule.height u) →
          z ∉ completedZetaContourIntegrandSingularSet)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
          Metric.closedBall a epsilon ⊆
            explicitFormulaContourFamilyInterior F (h.height_schedule.height u))
    (hseparated :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
              a ≠ b → epsilon + epsilon < dist a b)
    (hregular :
      epsilon ∉ finiteRectangleSquareSideForbiddenRadii
        (explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u))) :
    explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral
      f F (h.height_schedule.height u) epsilon = 0 :=
  explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_selectedRegularRadius_boundaryData_phiControl
    f F h.phi_control hT hepsilon hinterior hboundaryRegular hboundaryAvoidance
    hclosed hseparated hregular
    (explicitFormulaRectangleComplement_hgrid_noPackage f F hT)
    (explicitFormulaRectangleComplement_circleEqSquare_of_puncturedResidueRegularity
      f (h.height_schedule.height u) epsilon hepsilon
      (fun a ha =>
        explicitFormulaRectangleRawSingular_puncturedResidueRegularity_of_coefficientRegularity
          f h.phi_control a ha
          (explicitFormulaRectangleRawSingular_coefficientRegularity_of_phiControl
            f F h.phi_control hT hinterior epsilon hepsilon hclosed hseparated a ha)))

/-- Polynomial scheduled selected-radius residue assembly after finite-hole
Cauchy has been proved at the selected radius. -/
theorem zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_polynomialScheduledPackage_selectedRegularRadius_localRegularity
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage f F) (u epsilon : ℝ)
    (hT : 0 < h.height_schedule.height u) (hepsilon : 0 < epsilon)
    (hinterior :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        rho ∈ explicitFormulaCompletedZeroContourHeightWindow
            (h.height_schedule.height u) ↔
          completedZeroResidueCoordinate rho ∈
              explicitFormulaContourFamilyInterior F (h.height_schedule.height u) ∧
            completedZeroResidueCoordinate rho ∈ completedZetaContourIntegrandSingularSet)
    (hboundaryRegular :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F (h.height_schedule.height u) →
          ContinuousAt
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hboundaryAvoidance :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F (h.height_schedule.height u) →
          z ∉ completedZetaContourIntegrandSingularSet)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
          Metric.closedBall a epsilon ⊆
            explicitFormulaContourFamilyInterior F (h.height_schedule.height u))
    (hseparated :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
              a ≠ b → epsilon + epsilon < dist a b)
    (hregular :
      epsilon ∉ finiteRectangleSquareSideForbiddenRadii
        (explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u)))
    (s0 s1 : Set ℂ) (hs0 : s0.Countable) (hs1 : s1.Countable)
    (szero : {rho : ℂ // ZetaCompletedZero rho} → Set ℂ)
    (hszero :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        rho ∈ explicitFormulaCompletedZeroContourHeightWindow
            (h.height_schedule.height u) →
          (szero rho).Countable)
    (hzero_continuous :
      ContinuousOn
        (fun z : ℂ => (z - 0) * zetaCompletedExplicitFormulaContourIntegrand f z)
        (Metric.closedBall (0 : ℂ) epsilon \ {(0 : ℂ)}))
    (hzero_differentiable :
      ∀ z : ℂ,
        z ∈ (Metric.ball (0 : ℂ) epsilon \ {(0 : ℂ)}) \ s0 →
          DifferentiableAt ℂ
            (fun w : ℂ => (w - 0) * zetaCompletedExplicitFormulaContourIntegrand f w)
            z)
    (hone_continuous :
      ContinuousOn
        (fun z : ℂ => (z - 1) * zetaCompletedExplicitFormulaContourIntegrand f z)
        (Metric.closedBall (1 : ℂ) epsilon \ {(1 : ℂ)}))
    (hone_differentiable :
      ∀ z : ℂ,
        z ∈ (Metric.ball (1 : ℂ) epsilon \ {(1 : ℂ)}) \ s1 →
          DifferentiableAt ℂ
            (fun w : ℂ => (w - 1) * zetaCompletedExplicitFormulaContourIntegrand f w)
            z)
    (hcompleted_continuous :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        rho ∈ explicitFormulaCompletedZeroContourHeightWindow
            (h.height_schedule.height u) →
          ContinuousOn
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate rho) *
                zetaCompletedExplicitFormulaContourIntegrand f z)
            (Metric.closedBall (completedZeroResidueCoordinate rho) epsilon \
              {completedZeroResidueCoordinate rho}))
    (hcompleted_differentiable :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        ∀ hrho : rho ∈ explicitFormulaCompletedZeroContourHeightWindow
            (h.height_schedule.height u),
          ∀ z : ℂ,
            z ∈ (Metric.ball (completedZeroResidueCoordinate rho) epsilon \
                {completedZeroResidueCoordinate rho}) \ szero rho →
              DifferentiableAt ℂ
                (fun w : ℂ =>
                  (w - completedZeroResidueCoordinate rho) *
                    zetaCompletedExplicitFormulaContourIntegrand f w)
                z)
    (hlocal :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        rho ∈ explicitFormulaCompletedZeroContourHeightWindow
            (h.height_schedule.height u) →
          Tendsto
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate rho) *
                zetaCompletedExplicitFormulaContourIntegrand f z)
            (𝓝[≠] (completedZeroResidueCoordinate rho))
            (𝓝 (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero rho)))) :
    zetaCompletedExplicitFormulaTangentContourIntegral f
        (F.rectangle (h.height_schedule.height u)) =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        explicitFormulaRectangle_poleCorrectedResidueSum f
          (h.height_schedule.height u) :=
  let hcauchy :
      explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral
        f F (h.height_schedule.height u) epsilon = 0 :=
    explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_polynomialScheduledPackage_selectedRegularRadius
      f F h hT hepsilon hinterior hboundaryRegular hboundaryAvoidance
      hclosed hseparated hregular
  zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_finiteRadiusPuncturedBoundary_and_localRegularity
    f F (h.height_schedule.height u) epsilon h.phi_control hepsilon
    s0 s1 hs0 hs1 szero hszero hcauchy
    hzero_continuous hzero_differentiable
    hone_continuous hone_differentiable
    hcompleted_continuous hcompleted_differentiable
    hlocal

/-- Polynomial scheduled closed-radius residue assembly after finite-hole Cauchy
has been proved at the selected radius. -/
theorem zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_polynomialScheduledPackage_closedRadiusGeometry
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage f F) (u epsilon : ℝ)
    (hT : 0 < h.height_schedule.height u) (hepsilon : 0 < epsilon)
    (hinterior :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        rho ∈ explicitFormulaCompletedZeroContourHeightWindow
            (h.height_schedule.height u) ↔
          completedZeroResidueCoordinate rho ∈
              explicitFormulaContourFamilyInterior F (h.height_schedule.height u) ∧
            completedZeroResidueCoordinate rho ∈ completedZetaContourIntegrandSingularSet)
    (hboundaryRegular :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F (h.height_schedule.height u) →
          ContinuousAt
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hboundaryAvoidance :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F (h.height_schedule.height u) →
          z ∉ completedZetaContourIntegrandSingularSet)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
          Metric.closedBall a epsilon ⊆
            explicitFormulaContourFamilyInterior F (h.height_schedule.height u))
    (hseparated :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
              a ≠ b → epsilon + epsilon < dist a b)
    (hregular :
      epsilon ∉ finiteRectangleSquareSideForbiddenRadii
        (explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u)))
    (hlocal :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        rho ∈ explicitFormulaCompletedZeroContourHeightWindow
            (h.height_schedule.height u) →
          Tendsto
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate rho) *
                zetaCompletedExplicitFormulaContourIntegrand f z)
            (𝓝[≠] (completedZeroResidueCoordinate rho))
            (𝓝 (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero rho)))) :
    zetaCompletedExplicitFormulaTangentContourIntegral f
        (F.rectangle (h.height_schedule.height u)) =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        explicitFormulaRectangle_poleCorrectedResidueSum f
          (h.height_schedule.height u) :=
  let s : Set ℂ := completedZetaContourIntegrandSingularSet
  let hs : s.Countable := completedZetaContourIntegrandSingularSet_countable
  let hgeometry :
      (∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
          Metric.closedBall a epsilon ⊆
            explicitFormulaContourFamilyInterior F (h.height_schedule.height u)) ∧
      (∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
              a ≠ b →
                Disjoint (Metric.closedBall a epsilon) (Metric.closedBall b epsilon)) :=
    explicitFormulaRectangleRawClosedDisks_geometry_of_radius_controls
      F (h.height_schedule.height u) epsilon hclosed hseparated
  let hzeroRawReg :
      ContinuousOn
          (fun z : ℂ => z * zetaCompletedExplicitFormulaContourIntegrand f z)
          (Metric.closedBall (0 : ℂ) epsilon \ {(0 : ℂ)}) ∧
        (∀ z : ℂ,
          z ∈ (Metric.ball (0 : ℂ) epsilon \ {(0 : ℂ)}) \ s →
            DifferentiableAt ℂ
              (fun w : ℂ => w * zetaCompletedExplicitFormulaContourIntegrand f w)
              z) :=
    explicitFormulaRectangle_zeroPole_rawDeletedCircle_regular_of_closedRadiusGeometry_phiControl
      f F h.phi_control hT hepsilon hinterior hgeometry s
  let hzero_coeff :
      (fun z : ℂ => z * zetaCompletedExplicitFormulaContourIntegrand f z) =
        fun z : ℂ => (z - 0) * zetaCompletedExplicitFormulaContourIntegrand f z :=
    funext
      (fun z : ℂ =>
        congrArg
          (fun value : ℂ => value * zetaCompletedExplicitFormulaContourIntegrand f z)
          (Eq.symm (sub_zero z)))
  let hzeroReg :
      ContinuousOn
          (fun z : ℂ => (z - 0) * zetaCompletedExplicitFormulaContourIntegrand f z)
          (Metric.closedBall (0 : ℂ) epsilon \ {(0 : ℂ)}) ∧
        (∀ z : ℂ,
          z ∈ (Metric.ball (0 : ℂ) epsilon \ {(0 : ℂ)}) \ s →
            DifferentiableAt ℂ
              (fun w : ℂ => (w - 0) * zetaCompletedExplicitFormulaContourIntegrand f w)
              z) :=
    And.intro
      (Eq.subst
        (motive := fun g : ℂ → ℂ =>
          ContinuousOn g (Metric.closedBall (0 : ℂ) epsilon \ {(0 : ℂ)}))
        hzero_coeff
        hzeroRawReg.1)
      (Eq.subst
        (motive := fun g : ℂ → ℂ =>
          ∀ z : ℂ,
            z ∈ (Metric.ball (0 : ℂ) epsilon \ {(0 : ℂ)}) \ s →
              DifferentiableAt ℂ g z)
        hzero_coeff
        hzeroRawReg.2)
  let honeReg :
      ContinuousOn
          (fun z : ℂ => (z - 1) * zetaCompletedExplicitFormulaContourIntegrand f z)
          (Metric.closedBall (1 : ℂ) epsilon \ {(1 : ℂ)}) ∧
        (∀ z : ℂ,
          z ∈ (Metric.ball (1 : ℂ) epsilon \ {(1 : ℂ)}) \ s →
            DifferentiableAt ℂ
              (fun w : ℂ => (w - 1) * zetaCompletedExplicitFormulaContourIntegrand f w)
              z) :=
    explicitFormulaRectangle_onePole_rawDeletedCircle_regular_of_closedRadiusGeometry_phiControl
      f F h.phi_control hT hepsilon hinterior hgeometry s
  let hcompletedReg :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        ∀ hrho : rho ∈ explicitFormulaCompletedZeroContourHeightWindow
            (h.height_schedule.height u),
          ContinuousOn
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate rho) *
                zetaCompletedExplicitFormulaContourIntegrand f z)
            (Metric.closedBall (completedZeroResidueCoordinate rho) epsilon \
              {completedZeroResidueCoordinate rho}) ∧
          (∀ z : ℂ,
            z ∈ (Metric.ball (completedZeroResidueCoordinate rho) epsilon \
                {completedZeroResidueCoordinate rho}) \ s →
              DifferentiableAt ℂ
                (fun w : ℂ =>
                  (w - completedZeroResidueCoordinate rho) *
                    zetaCompletedExplicitFormulaContourIntegrand f w)
                z) :=
    fun rho hrho =>
      explicitFormulaRectangle_completedZero_rawDeletedCircle_regular_of_closedRadiusGeometry_phiControl
        f F h.phi_control hT hepsilon hinterior hgeometry rho hrho s
  zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_polynomialScheduledPackage_selectedRegularRadius_localRegularity
    f F h u epsilon hT hepsilon hinterior hboundaryRegular hboundaryAvoidance
    hclosed hseparated hregular
    s s hs hs
    (fun rho => s)
    (fun rho hrho => hs)
    hzeroReg.1 hzeroReg.2
    honeReg.1 honeReg.2
    (fun rho hrho => (hcompletedReg rho hrho).1)
    (fun rho hrho => (hcompletedReg rho hrho).2)
    hlocal

/-- Polynomial scheduled selected-radius tangent residue assembly, with
completed-zero local residue limits supplied explicitly. -/
theorem zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_polynomialScheduledPackage_selectedRegularRadius
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage f F) {u : ℝ}
    (hT : 0 < h.height_schedule.height u)
    (hinterior :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        rho ∈ explicitFormulaCompletedZeroContourHeightWindow
            (h.height_schedule.height u) ↔
          completedZeroResidueCoordinate rho ∈
              explicitFormulaContourFamilyInterior F (h.height_schedule.height u) ∧
            completedZeroResidueCoordinate rho ∈ completedZetaContourIntegrandSingularSet)
    (hboundaryRegular :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F (h.height_schedule.height u) →
          ContinuousAt
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hboundaryAvoidance :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F (h.height_schedule.height u) →
          z ∉ completedZetaContourIntegrandSingularSet)
    (hlocal :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        rho ∈ explicitFormulaCompletedZeroContourHeightWindow
            (h.height_schedule.height u) →
          Tendsto
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate rho) *
                zetaCompletedExplicitFormulaContourIntegrand f z)
            (𝓝[≠] (completedZeroResidueCoordinate rho))
            (𝓝 (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero rho)))) :
    zetaCompletedExplicitFormulaTangentContourIntegral f
        (F.rectangle (h.height_schedule.height u)) =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        explicitFormulaRectangle_poleCorrectedResidueSum f
          (h.height_schedule.height u) :=
  let hlocalInterior :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
          ∃ radius : ℝ,
            0 < radius ∧
              Metric.ball a radius ⊆
                explicitFormulaContourFamilyInterior F (h.height_schedule.height u) :=
    fun a ha =>
      explicitFormulaRectangleRawSingularCoordinates_localInterior_ball
        F hT hinterior ha
  match explicitFormulaRectangleRawSingularCoordinates_exists_squareSideRegular_closedRadiusControls
      F (h.height_schedule.height u) hlocalInterior with
  | ⟨epsilon, hepsilon, hclosed, hseparated, hregular⟩ =>
      zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_polynomialScheduledPackage_closedRadiusGeometry
        f F h u epsilon hT hepsilon hinterior hboundaryRegular hboundaryAvoidance
        hclosed hseparated hregular hlocal

/-- Canonical polynomial scheduled selected-radius tangent residue assembly. -/
theorem zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_polynomialScheduledPackage_selected
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage f F) {u : ℝ}
    (hT : 0 < h.height_schedule.height u)
    (hinterior :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        rho ∈ explicitFormulaCompletedZeroContourHeightWindow
            (h.height_schedule.height u) ↔
          completedZeroResidueCoordinate rho ∈
              explicitFormulaContourFamilyInterior F (h.height_schedule.height u) ∧
            completedZeroResidueCoordinate rho ∈ completedZetaContourIntegrandSingularSet)
    (hboundaryRegular :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F (h.height_schedule.height u) →
          ContinuousAt
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hboundaryAvoidance :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F (h.height_schedule.height u) →
          z ∉ completedZetaContourIntegrandSingularSet) :
    zetaCompletedExplicitFormulaTangentContourIntegral f
        (F.rectangle (h.height_schedule.height u)) =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        explicitFormulaRectangle_poleCorrectedResidueSum f
          (h.height_schedule.height u) :=
  let hlocal :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        rho ∈ explicitFormulaCompletedZeroContourHeightWindow
            (h.height_schedule.height u) →
          Tendsto
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate rho) *
                zetaCompletedExplicitFormulaContourIntegrand f z)
            (𝓝[≠] (completedZeroResidueCoordinate rho))
            (𝓝 (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero rho))) :=
    fun rho hrho =>
      let hphi :
          zetaCompletedExplicitFormulaPhi f (rho : ℂ) =
            zetaCompletedExplicitFormulaPhi f (rho : ℂ) :=
        explicitFormulaRectangle_completedZeroResidueWindow_phiConventionCorrection
          f (h.height_schedule.height u) rho hrho
      let hnormalize :
          explicitFormulaZeroResidue f (explicitFormulaContourZeroDataOfCompletedZero rho) =
            explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero rho) :=
        explicitFormulaRectangle_completedZeroResidueWindow_contourToZeroSideResidueEquality
          f (h.height_schedule.height u) rho hrho hphi
      Eq.subst
        (motive := fun residue : ℂ =>
          Tendsto
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate rho) *
                zetaCompletedExplicitFormulaContourIntegrand f z)
            (𝓝[≠] (completedZeroResidueCoordinate rho))
            (𝓝 residue))
        hnormalize
        (explicitFormulaRectangle_completedZero_localResidue_tendsto_contourSummand
          f h.phi_control rho)
  zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_polynomialScheduledPackage_selectedRegularRadius
    f F h hT hinterior hboundaryRegular hboundaryAvoidance hlocal

/-- Polynomial scheduled tangent-residue equality at every positive scheduled
height. -/
theorem zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_polynomialScheduledPackage_selected_of_positive
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage f F) :
    ∀ u : ℝ,
      0 < h.height_schedule.height u →
        zetaCompletedExplicitFormulaTangentContourIntegral f
            (F.rectangle (h.height_schedule.height u)) =
          explicitFormulaTwoPiI •
            explicitFormulaRectangle_poleCorrectedResidueSum f
              (h.height_schedule.height u) :=
  fun u hT =>
    zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_polynomialScheduledPackage_selected
      f F h hT
      (fun rho =>
        explicitFormulaCompletedZeroContourHeightWindow_mem_iff_interiorSingular
          F (h.height_schedule.height u) rho)
      (fun z hboundary =>
        let hoff :
            z ∉ completedZetaContourIntegrandSingularSet :=
          completedZetaContourIntegrand_not_mem_singularSet_of_avoidsBoundary
            F
            (h.height_schedule.height u)
            (h.height_schedule.avoids_boundary u)
            hboundary
        And.intro
          (completedZetaContourIntegrand_continuousAt_off_singularSet
            h.phi_control hoff)
          (completedZetaContourIntegrand_differentiableAt_off_singularSet
            h.phi_control hoff))
      (fun z hboundary =>
        completedZetaContourIntegrand_not_mem_singularSet_of_avoidsBoundary
          F
          (h.height_schedule.height u)
          (h.height_schedule.avoids_boundary u)
          hboundary)

/-- Polynomial scheduled tangent-residue equality supplies the eventual
normalized tangent-residue equality. -/
theorem explicitFormulaRectangle_poleCorrectedResidueSum_eventually_eq_normalizedTangent_of_polynomialScheduledPackage_selected
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage f F) :
    ∀ᶠ u in atTop,
      explicitFormulaRectangle_poleCorrectedResidueSum f
          (h.height_schedule.height u) =
        zetaCompletedExplicitFormulaNormalizedTangentContourIntegral f
          (F.rectangle (h.height_schedule.height u)) :=
  explicitFormulaRectangle_poleCorrectedResidueSum_eventually_eq_normalizedTangent_of_polynomialScheduledPackage_rawPointwise
    f F h
    (zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_polynomialScheduledPackage_selected_of_positive
      f F h)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
