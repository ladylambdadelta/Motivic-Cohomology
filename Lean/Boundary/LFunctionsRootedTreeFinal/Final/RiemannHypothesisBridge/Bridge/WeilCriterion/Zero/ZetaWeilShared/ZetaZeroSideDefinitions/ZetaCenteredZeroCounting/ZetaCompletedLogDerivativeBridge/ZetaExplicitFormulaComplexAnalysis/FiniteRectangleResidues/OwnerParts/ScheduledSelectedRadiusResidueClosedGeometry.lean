import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.ScheduledSelectedRadiusResidueAssembly

/-!
# Scheduled selected-radius residue closed geometry

This file peels the deleted-circle local-regularity inputs for the scheduled
selected-radius residue theorem away from the full analytic package.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Closed-radius regularity for the deleted circle at the completed-zeta pole `0`,
using only transform control. -/
theorem explicitFormulaRectangle_zeroPole_rawDeletedCircle_regular_of_closedRadiusGeometry_phiControl
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (phiControl : ZetaPhiAnalyticControl f)
    {T epsilon : ℝ} (hT : 0 < T) (hepsilon : 0 < epsilon)
    (hinterior :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        rho ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate rho ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate rho ∈ completedZetaContourIntegrandSingularSet)
    (hgeometry :
      (∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a epsilon ⊆ explicitFormulaContourFamilyInterior F T) ∧
      (∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b →
                Disjoint (Metric.closedBall a epsilon) (Metric.closedBall b epsilon)))
    (s : Set ℂ) :
    ContinuousOn
        (fun z : ℂ => z * zetaCompletedExplicitFormulaContourIntegrand f z)
        (Metric.closedBall (0 : ℂ) epsilon \ {(0 : ℂ)}) ∧
      (∀ z : ℂ,
        z ∈ (Metric.ball (0 : ℂ) epsilon \ {(0 : ℂ)}) \ s →
          DifferentiableAt ℂ
            (fun w : ℂ => w * zetaCompletedExplicitFormulaContourIntegrand f w)
            z) :=
  let hraw :
      ContinuousOn
          (fun z : ℂ => (z - (0 : ℂ)) * zetaCompletedExplicitFormulaContourIntegrand f z)
          (Metric.closedBall (0 : ℂ) epsilon \ {(0 : ℂ)}) ∧
        (∀ z : ℂ,
          z ∈ (Metric.ball (0 : ℂ) epsilon \ {(0 : ℂ)}) \ s →
            DifferentiableAt ℂ
              (fun w : ℂ => (w - (0 : ℂ)) *
                zetaCompletedExplicitFormulaContourIntegrand f w)
              z) :=
    explicitFormulaRectangle_rawDeletedClosedBall_localResidueCoefficient_regular_phiControl
      f F phiControl hT hepsilon hinterior hgeometry.1 hgeometry.2
      (0 : ℂ) (explicitFormulaRectangleRawSingularCoordinates_zero_mem T) s
  let hcoeff :
      (fun z : ℂ => (z - (0 : ℂ)) * zetaCompletedExplicitFormulaContourIntegrand f z) =
        fun z : ℂ => z * zetaCompletedExplicitFormulaContourIntegrand f z :=
    funext
      (fun z : ℂ =>
        congrArg
          (fun x : ℂ => x * zetaCompletedExplicitFormulaContourIntegrand f z)
          (sub_zero z))
  And.intro
    (Eq.subst
      (motive := fun phi : ℂ → ℂ =>
        ContinuousOn phi (Metric.closedBall (0 : ℂ) epsilon \ {(0 : ℂ)}))
      hcoeff
      hraw.1)
    (fun z hz =>
      Eq.subst
        (motive := fun phi : ℂ → ℂ => DifferentiableAt ℂ phi z)
        hcoeff
        (hraw.2 z hz))

/-- Closed-radius regularity for the deleted circle at the completed-zeta pole `1`,
using only transform control. -/
theorem explicitFormulaRectangle_onePole_rawDeletedCircle_regular_of_closedRadiusGeometry_phiControl
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (phiControl : ZetaPhiAnalyticControl f)
    {T epsilon : ℝ} (hT : 0 < T) (hepsilon : 0 < epsilon)
    (hinterior :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        rho ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate rho ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate rho ∈ completedZetaContourIntegrandSingularSet)
    (hgeometry :
      (∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a epsilon ⊆ explicitFormulaContourFamilyInterior F T) ∧
      (∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b →
                Disjoint (Metric.closedBall a epsilon) (Metric.closedBall b epsilon)))
    (s : Set ℂ) :
    ContinuousOn
        (fun z : ℂ => (z - 1) * zetaCompletedExplicitFormulaContourIntegrand f z)
        (Metric.closedBall (1 : ℂ) epsilon \ {(1 : ℂ)}) ∧
      (∀ z : ℂ,
        z ∈ (Metric.ball (1 : ℂ) epsilon \ {(1 : ℂ)}) \ s →
          DifferentiableAt ℂ
            (fun w : ℂ => (w - 1) * zetaCompletedExplicitFormulaContourIntegrand f w)
            z) :=
  explicitFormulaRectangle_rawDeletedClosedBall_localResidueCoefficient_regular_phiControl
    f F phiControl hT hepsilon hinterior hgeometry.1 hgeometry.2
    (1 : ℂ) (explicitFormulaRectangleRawSingularCoordinates_one_mem T) s

/-- Closed-radius regularity for a deleted circle centered at a completed zero,
using only transform control. -/
theorem explicitFormulaRectangle_completedZero_rawDeletedCircle_regular_of_closedRadiusGeometry_phiControl
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (phiControl : ZetaPhiAnalyticControl f)
    {T epsilon : ℝ} (hT : 0 < T) (hepsilon : 0 < epsilon)
    (hinterior :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        rho ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate rho ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate rho ∈ completedZetaContourIntegrandSingularSet)
    (hgeometry :
      (∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a epsilon ⊆ explicitFormulaContourFamilyInterior F T) ∧
      (∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b →
                Disjoint (Metric.closedBall a epsilon) (Metric.closedBall b epsilon)))
    (rho : {rho : ℂ // ZetaCompletedZero rho})
    (hrho : rho ∈ explicitFormulaCompletedZeroContourHeightWindow T)
    (s : Set ℂ) :
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
  explicitFormulaRectangle_rawDeletedClosedBall_localResidueCoefficient_regular_phiControl
    f F phiControl hT hepsilon hinterior hgeometry.1 hgeometry.2
    (completedZeroResidueCoordinate rho)
    (explicitFormulaRectangleRawSingularCoordinates_completedZero_mem T hrho)
    s

/-- Scheduled closed-radius residue assembly after finite-hole Cauchy has been
proved at the selected radius. -/
theorem zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_scheduledPackage_closedRadiusGeometry
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F) (u epsilon : ℝ)
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
        (fun z : ℂ => (z - 0) * zetaCompletedExplicitFormulaContourIntegrand f z) :=
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
        hzeroRawReg.left)
      (Eq.subst
        (motive := fun g : ℂ → ℂ =>
          ∀ z : ℂ,
            z ∈ (Metric.ball (0 : ℂ) epsilon \ {(0 : ℂ)}) \ s →
              DifferentiableAt ℂ g z)
        hzero_coeff
        hzeroRawReg.right)
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
  zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_scheduledPackage_selectedRegularRadius_localRegularity
    f F h u epsilon hT hepsilon hinterior hboundaryRegular hboundaryAvoidance hclosed hseparated hregular
    s s hs hs
    (fun _rho => s)
    (fun _rho _hrho => hs)
    hzeroReg.1 hzeroReg.2
    honeReg.1 honeReg.2
    (fun rho hrho => (hcompletedReg rho hrho).1)
    (fun rho hrho => (hcompletedReg rho hrho).2)
    hlocal

/-- Scheduled selected-radius tangent residue assembly, with completed-zero local
residue limits supplied explicitly. -/
theorem zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_scheduledPackage_selectedRegularRadius
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F) {u : ℝ}
    (hT : 0 < h.height_schedule.height u)
    (hinterior :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        rho ∈ explicitFormulaCompletedZeroContourHeightWindow (h.height_schedule.height u) ↔
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
      zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_scheduledPackage_closedRadiusGeometry
        f F h u epsilon hT hepsilon hinterior hboundaryRegular hboundaryAvoidance
        hclosed hseparated hregular hlocal

/-- Canonical scheduled selected-radius tangent residue assembly; the completed-zero
local residue limits are discharged from the corrected contour coordinate. -/
theorem zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_scheduledPackage_selected
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F) {u : ℝ}
    (hT : 0 < h.height_schedule.height u)
    (hinterior :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        rho ∈ explicitFormulaCompletedZeroContourHeightWindow (h.height_schedule.height u) ↔
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
        rho ∈ explicitFormulaCompletedZeroContourHeightWindow (h.height_schedule.height u) →
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
  zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_scheduledPackage_selectedRegularRadius
    f F h hT hinterior hboundaryRegular hboundaryAvoidance hlocal

/- The scheduled analytic package already contains the boundary regularity and
avoidance data.  This owner theorem exposes the resulting finite-height
residue identity without making callers duplicate those consequences. -/
theorem zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_scheduledPackage_owner
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F) {u : ℝ}
    (hT : 0 < h.height_schedule.height u)
    (hinterior :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        rho ∈ explicitFormulaCompletedZeroContourHeightWindow
            (h.height_schedule.height u) ↔
          completedZeroResidueCoordinate rho ∈
              explicitFormulaContourFamilyInterior F (h.height_schedule.height u) ∧
            completedZeroResidueCoordinate rho ∈ completedZetaContourIntegrandSingularSet) :
    zetaCompletedExplicitFormulaTangentContourIntegral f
        (F.rectangle (h.height_schedule.height u)) =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        explicitFormulaRectangle_poleCorrectedResidueSum f
          (h.height_schedule.height u) :=
  zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_scheduledPackage_selected
    f F h hT hinterior
    (fun z hz =>
      (explicitFormulaRectangleContourIntegrand_boundaryRegular_of_avoidsBoundary
        f F h (h.height_schedule.height u)
        (explicitFormulaScheduledRectangle_avoidsSingularBoundary f F h u)) z hz)
    (fun z hz =>
      completedZetaContourIntegrand_not_mem_singularSet_of_scheduledBoundary
        f F h u hz)

theorem zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_scheduledPackage_canonicalInterior_owner
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F) {u : ℝ}
    (hT : 0 < h.height_schedule.height u) :
    zetaCompletedExplicitFormulaTangentContourIntegral f
        (F.rectangle (h.height_schedule.height u)) =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        explicitFormulaRectangle_poleCorrectedResidueSum f
          (h.height_schedule.height u) :=
  zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_scheduledPackage_owner
    f F h hT
    (fun rho =>
      explicitFormulaCompletedZeroContourHeightWindow_mem_iff_scheduledPackageInteriorSingular
        F h u rho)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
