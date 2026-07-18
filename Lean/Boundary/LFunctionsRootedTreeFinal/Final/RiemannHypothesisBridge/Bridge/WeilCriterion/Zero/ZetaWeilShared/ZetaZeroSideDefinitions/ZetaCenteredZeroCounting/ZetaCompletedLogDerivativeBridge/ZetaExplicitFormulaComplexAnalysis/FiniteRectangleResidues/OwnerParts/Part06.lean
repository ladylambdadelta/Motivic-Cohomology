import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part05

/-!
# Explicit-formula finite rectangle residues

This owner layer contains finite-rectangle residue equalities, scheduled avoidance, and residue-window error transport.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The raw completed contour integral with the two completed-zeta pole principal parts
removed in the tangent-weighted contour normalization used by residue calculus. -/
noncomputable def explicitFormulaRectangle_tangentPoleCorrectedContourIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) -
    explicitFormulaRectangle_completedPoleTangentBoundaryContribution f F T

/-- The tangent-weighted completed contour with the tangent-weighted completed-zeta pole
principal parts removed.  This is the finite Cauchy-residue target, before transporting
back to the project's non-tangent explicit-formula side convention. -/
noncomputable def explicitFormulaRectangle_fullTangentPoleCorrectedContourIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
    explicitFormulaRectangle_completedPoleTangentBoundaryContribution f F T

/-- The tangent-weighted completed contour unfolds to the four side integrals with
tangent factors on the vertical sides. -/
theorem zetaCompletedExplicitFormulaTangentContourIntegral_eq
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaTangentContourIntegral f r =
      zetaCompletedExplicitFormulaBottomLineIntegral f r -
        zetaCompletedExplicitFormulaTopLineIntegral f r +
          (zetaCompletedExplicitFormulaRightLineIntegral f r * Complex.I -
            zetaCompletedExplicitFormulaLeftLineIntegral f r * Complex.I) := by
  rfl

/-- The pole-boundary contribution unfolds to the `0` and `1` principal-part boundary
integrals. -/
theorem explicitFormulaRectangle_completedPoleBoundaryContribution_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaRectangle_completedPoleBoundaryContribution f F T =
      zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral f F T +
        zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral f F T := by
  rfl

/-- The tangent pole-boundary contribution unfolds to the two tangent principal-part
boundary integrals. -/
theorem explicitFormulaRectangle_completedPoleTangentBoundaryContribution_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaRectangle_completedPoleTangentBoundaryContribution f F T =
      zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral f F T +
        zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral f F T := by
  rfl

/-- The tangent defect is exactly tangent contribution minus the project's non-tangent
pole-boundary contribution. -/
theorem explicitFormulaRectangle_completedPoleBoundaryTangentDefect_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaRectangle_completedPoleBoundaryTangentDefect f F T =
      explicitFormulaRectangle_completedPoleTangentBoundaryContribution f F T -
        explicitFormulaRectangle_completedPoleBoundaryContribution f F T := by
  rfl

/-- The tangent pole-boundary contribution is the project pole-boundary contribution plus
the named tangent defect. -/
theorem explicitFormulaRectangle_completedPoleTangentBoundaryContribution_eq_boundary_add_defect
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaRectangle_completedPoleTangentBoundaryContribution f F T =
      explicitFormulaRectangle_completedPoleBoundaryContribution f F T +
        explicitFormulaRectangle_completedPoleBoundaryTangentDefect f F T := by
  let A : ℂ := explicitFormulaRectangle_completedPoleTangentBoundaryContribution f F T
  let B : ℂ := explicitFormulaRectangle_completedPoleBoundaryContribution f F T
  calc
    explicitFormulaRectangle_completedPoleTangentBoundaryContribution f F T = A := by
      rfl
    _ = (A - B) + B := by
      exact (sub_add_cancel A B).symm
    _ = B + (A - B) := by
      exact add_comm (A - B) B
    _ = explicitFormulaRectangle_completedPoleBoundaryContribution f F T +
        explicitFormulaRectangle_completedPoleBoundaryTangentDefect f F T := by
      rfl

/-- The project pole-boundary contribution is the tangent contribution minus the named
tangent defect. -/
theorem explicitFormulaRectangle_completedPoleBoundaryContribution_eq_tangent_sub_defect
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaRectangle_completedPoleBoundaryContribution f F T =
      explicitFormulaRectangle_completedPoleTangentBoundaryContribution f F T -
        explicitFormulaRectangle_completedPoleBoundaryTangentDefect f F T := by
  let A : ℂ := explicitFormulaRectangle_completedPoleTangentBoundaryContribution f F T
  let B : ℂ := explicitFormulaRectangle_completedPoleBoundaryContribution f F T
  calc
    explicitFormulaRectangle_completedPoleBoundaryContribution f F T = B := by
      rfl
    _ = A - (A - B) := by
      exact (sub_sub_cancel A B).symm
    _ = explicitFormulaRectangle_completedPoleTangentBoundaryContribution f F T -
        explicitFormulaRectangle_completedPoleBoundaryTangentDefect f F T := by
      rfl

/-- If the tangent-weighted pole contour has the pole residue sum and the tangent defect
vanishes, then the project-normalized pole boundary contribution has the pole residue sum. -/
theorem explicitFormulaRectangle_completedPoleBoundaryContribution_eq_residueSum_of_tangentResidue_and_defect_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (htangent :
      explicitFormulaRectangle_completedPoleTangentBoundaryContribution f F T =
        explicitFormulaRectangle_completedPoleResidueSum f)
    (hdefect :
      explicitFormulaRectangle_completedPoleBoundaryTangentDefect f F T = 0) :
    explicitFormulaRectangle_completedPoleBoundaryContribution f F T =
      explicitFormulaRectangle_completedPoleResidueSum f := by
  calc
    explicitFormulaRectangle_completedPoleBoundaryContribution f F T =
        explicitFormulaRectangle_completedPoleTangentBoundaryContribution f F T -
          explicitFormulaRectangle_completedPoleBoundaryTangentDefect f F T := by
      exact explicitFormulaRectangle_completedPoleBoundaryContribution_eq_tangent_sub_defect f F T
    _ = explicitFormulaRectangle_completedPoleResidueSum f -
          explicitFormulaRectangle_completedPoleBoundaryTangentDefect f F T := by
      exact congrArg
        (fun z : ℂ => z - explicitFormulaRectangle_completedPoleBoundaryTangentDefect f F T)
        htangent
    _ = explicitFormulaRectangle_completedPoleResidueSum f - 0 := by
      exact congrArg
        (fun z : ℂ => explicitFormulaRectangle_completedPoleResidueSum f - z)
        hdefect
    _ = explicitFormulaRectangle_completedPoleResidueSum f := by
      exact sub_zero (explicitFormulaRectangle_completedPoleResidueSum f)

/-- Exact expansion of the tangent defect in the project's side convention.  The horizontal
terms agree with the tangent contour; only the vertical sides carry the extra tangent
factor `I`. -/
theorem explicitFormulaRectangle_completedPoleBoundaryTangentDefect_eq_verticalTangent_expansion
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaRectangle_completedPoleBoundaryTangentDefect f F T =
      (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral f F T * Complex.I -
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral f F T * Complex.I +
          zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral f F T -
          zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral f F T +
        (zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral f F T * Complex.I -
          zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral f F T * Complex.I +
          zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral f F T -
          zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral f F T)) -
      (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral f F T -
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral f F T +
          zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral f F T -
          zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral f F T +
        (zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral f F T -
          zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral f F T +
          zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral f F T -
          zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral f F T)) := by
  let ZT : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral f F T
  let OT : ℂ :=
    zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral f F T
  let Z : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral f F T
  let O : ℂ :=
    zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral f F T
  have hZT :
      ZT =
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral f F T * Complex.I -
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral f F T * Complex.I +
          zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral f F T -
          zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral f F T :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral_eq_verticalTangent_add_horizontal
      f F T
  have hOT :
      OT =
        zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral f F T * Complex.I -
          zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral f F T * Complex.I +
          zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral f F T -
          zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral f F T :=
    zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral_eq_verticalTangent_add_horizontal
      f F T
  calc
    explicitFormulaRectangle_completedPoleBoundaryTangentDefect f F T =
        (ZT + OT) - (Z + O) := by
      rfl
    _ =
        (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral f F T * Complex.I -
            zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral f F T * Complex.I +
            zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral f F T -
            zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral f F T + OT) -
        (Z + O) := by
      exact congrArg (fun x : ℂ => (x + OT) - (Z + O)) hZT
    _ =
        (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral f F T * Complex.I -
            zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral f F T * Complex.I +
            zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral f F T -
            zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral f F T +
          (zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral f F T * Complex.I -
            zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral f F T * Complex.I +
            zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral f F T -
            zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral f F T)) -
        (Z + O) := by
      exact congrArg
        (fun x : ℂ =>
          (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral f F T * Complex.I -
              zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral f F T * Complex.I +
              zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral f F T -
              zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral f F T + x) -
            (Z + O))
        hOT
    _ =
        (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral f F T * Complex.I -
            zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral f F T * Complex.I +
            zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral f F T -
            zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral f F T +
          (zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral f F T * Complex.I -
            zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral f F T * Complex.I +
            zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral f F T -
            zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral f F T)) -
        (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral f F T -
            zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral f F T +
            zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral f F T -
            zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral f F T + O) := by
      rfl
    _ =
        (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral f F T * Complex.I -
            zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral f F T * Complex.I +
            zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral f F T -
            zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral f F T +
          (zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral f F T * Complex.I -
            zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral f F T * Complex.I +
            zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral f F T -
            zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral f F T)) -
        (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral f F T -
            zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral f F T +
            zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral f F T -
            zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral f F T +
          (zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral f F T -
            zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral f F T +
            zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral f F T -
            zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral f F T)) := by
      rfl

/-- The tangent defect vanishes once the tangent and non-tangent boundary normalizations
agree separately for the two isolated pole kernels. -/
theorem explicitFormulaRectangle_completedPoleBoundaryTangentDefect_eq_zero_of_pole_normalizations
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hzero :
      zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral f F T =
        zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral f F T)
    (hone :
      zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral f F T =
        zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral f F T) :
    explicitFormulaRectangle_completedPoleBoundaryTangentDefect f F T = 0 := by
  let ZT : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral f F T
  let OT : ℂ :=
    zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral f F T
  let Z : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral f F T
  let O : ℂ :=
    zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral f F T
  have hsum : ZT + OT = Z + O := by
    calc
      ZT + OT = Z + OT := by
        exact congrArg (fun x : ℂ => x + OT) hzero
      _ = Z + O := by
        exact congrArg (fun x : ℂ => Z + x) hone
  calc
    explicitFormulaRectangle_completedPoleBoundaryTangentDefect f F T =
        (ZT + OT) - (Z + O) := by
      rfl
    _ = (Z + O) - (Z + O) := by
      exact congrArg (fun x : ℂ => x - (Z + O)) hsum
    _ = 0 := by
      exact sub_self (Z + O)

/-- The combined tangent pole-boundary residue identity follows from the two isolated
tangent pole residue identities. -/
theorem explicitFormulaRectangle_completedPoleTangentBoundaryContribution_eq_residueSum_of_isolated
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hzero :
      zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral f F T =
        explicitFormulaRectangle_zeroPoleResidue f)
    (hone :
      zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral f F T =
        explicitFormulaRectangle_onePoleResidue f) :
    explicitFormulaRectangle_completedPoleTangentBoundaryContribution f F T =
      explicitFormulaRectangle_completedPoleResidueSum f := by
  let ZT : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral f F T
  let OT : ℂ :=
    zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral f F T
  let Z : ℂ := explicitFormulaRectangle_zeroPoleResidue f
  let O : ℂ := explicitFormulaRectangle_onePoleResidue f
  calc
    explicitFormulaRectangle_completedPoleTangentBoundaryContribution f F T =
        ZT + OT := by
      rfl
    _ = Z + OT := by
      exact congrArg (fun x : ℂ => x + OT) hzero
    _ = Z + O := by
      exact congrArg (fun x : ℂ => Z + x) hone
    _ = explicitFormulaRectangle_completedPoleResidueSum f := by
      rfl

/-- The project-normalized pole boundary contribution has the pole residue sum once the
two isolated tangent residue identities and the two tangent/non-tangent normalization
identities are available. -/
theorem explicitFormulaRectangle_completedPoleBoundaryContribution_eq_residueSum_of_isolated_tangent
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hzeroResidue :
      zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral f F T =
        explicitFormulaRectangle_zeroPoleResidue f)
    (honeResidue :
      zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral f F T =
        explicitFormulaRectangle_onePoleResidue f)
    (hzeroNormalize :
      zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral f F T =
        zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral f F T)
    (honeNormalize :
      zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral f F T =
        zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral f F T) :
    explicitFormulaRectangle_completedPoleBoundaryContribution f F T =
      explicitFormulaRectangle_completedPoleResidueSum f := by
  have htangent :
      explicitFormulaRectangle_completedPoleTangentBoundaryContribution f F T =
        explicitFormulaRectangle_completedPoleResidueSum f :=
    explicitFormulaRectangle_completedPoleTangentBoundaryContribution_eq_residueSum_of_isolated
      f F T hzeroResidue honeResidue
  have hdefect :
      explicitFormulaRectangle_completedPoleBoundaryTangentDefect f F T = 0 :=
    explicitFormulaRectangle_completedPoleBoundaryTangentDefect_eq_zero_of_pole_normalizations
      f F T hzeroNormalize honeNormalize
  exact
    explicitFormulaRectangle_completedPoleBoundaryContribution_eq_residueSum_of_tangentResidue_and_defect_zero
      f F T htangent hdefect

/-- The corrected contour integral unfolds as the raw contour integral minus the two
completed-zeta pole principal-part boundary contributions. -/
theorem explicitFormulaRectangle_poleCorrectedContourIntegral_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaRectangle_poleCorrectedContourIntegral f F T =
      zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) -
        explicitFormulaRectangle_completedPoleBoundaryContribution f F T := by
  rfl

/-- The tangent-corrected contour integral unfolds as the raw contour integral minus the
tangent-weighted completed-zeta pole principal-part boundary contribution. -/
theorem explicitFormulaRectangle_tangentPoleCorrectedContourIntegral_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaRectangle_tangentPoleCorrectedContourIntegral f F T =
      zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) -
        explicitFormulaRectangle_completedPoleTangentBoundaryContribution f F T := by
  rfl

/-- The full tangent-corrected contour unfolds as the tangent rectangle contour minus the
tangent-weighted completed-zeta pole principal-part boundary contribution. -/
theorem explicitFormulaRectangle_fullTangentPoleCorrectedContourIntegral_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaRectangle_fullTangentPoleCorrectedContourIntegral f F T =
      zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
        explicitFormulaRectangle_completedPoleTangentBoundaryContribution f F T := by
  rfl

/-- Recovering the raw contour integral from the corrected contour integral adds back the
two completed-zeta pole boundary contributions. -/
theorem zetaCompletedExplicitFormulaContourIntegral_eq_poleCorrected_add_poles
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) =
      explicitFormulaRectangle_poleCorrectedContourIntegral f F T +
        explicitFormulaRectangle_completedPoleBoundaryContribution f F T := by
  let C : ℂ := zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T)
  let P : ℂ := explicitFormulaRectangle_completedPoleBoundaryContribution f F T
  calc
    zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) = C := by
      rfl
    _ = (C - P) + P := by
      exact (sub_add_cancel C P).symm
    _ = explicitFormulaRectangle_poleCorrectedContourIntegral f F T +
        explicitFormulaRectangle_completedPoleBoundaryContribution f F T := by
      rfl

/-- Recovering the raw contour integral from the tangent-corrected contour integral adds
back the tangent-weighted completed-zeta pole boundary contribution. -/
theorem zetaCompletedExplicitFormulaContourIntegral_eq_tangentPoleCorrected_add_tangentPoles
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) =
      explicitFormulaRectangle_tangentPoleCorrectedContourIntegral f F T +
        explicitFormulaRectangle_completedPoleTangentBoundaryContribution f F T := by
  let C : ℂ := zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T)
  let P : ℂ := explicitFormulaRectangle_completedPoleTangentBoundaryContribution f F T
  calc
    zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) = C := by
      rfl
    _ = (C - P) + P := by
      exact (sub_add_cancel C P).symm
    _ = explicitFormulaRectangle_tangentPoleCorrectedContourIntegral f F T +
        explicitFormulaRectangle_completedPoleTangentBoundaryContribution f F T := by
      rfl

/-- Recovering the full tangent contour from the full tangent-corrected contour adds back
the tangent-weighted completed-zeta pole boundary contribution. -/
theorem zetaCompletedExplicitFormulaTangentContourIntegral_eq_fullTangentPoleCorrected_add_tangentPoles
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) =
      explicitFormulaRectangle_fullTangentPoleCorrectedContourIntegral f F T +
        explicitFormulaRectangle_completedPoleTangentBoundaryContribution f F T := by
  let C : ℂ := zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T)
  let P : ℂ := explicitFormulaRectangle_completedPoleTangentBoundaryContribution f F T
  calc
    zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) = C := by
      rfl
    _ = (C - P) + P := by
      exact (sub_add_cancel C P).symm
    _ = explicitFormulaRectangle_fullTangentPoleCorrectedContourIntegral f F T +
        explicitFormulaRectangle_completedPoleTangentBoundaryContribution f F T := by
      rfl

/-- The non-tangent corrected contour is the tangent-corrected contour plus the tangent
normalization defect. -/
theorem explicitFormulaRectangle_poleCorrectedContourIntegral_eq_tangentCorrected_add_defect
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaRectangle_poleCorrectedContourIntegral f F T =
      explicitFormulaRectangle_tangentPoleCorrectedContourIntegral f F T +
        explicitFormulaRectangle_completedPoleBoundaryTangentDefect f F T := by
  let C : ℂ := zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T)
  let B : ℂ := explicitFormulaRectangle_completedPoleBoundaryContribution f F T
  let A : ℂ := explicitFormulaRectangle_completedPoleTangentBoundaryContribution f F T
  calc
    explicitFormulaRectangle_poleCorrectedContourIntegral f F T = C - B := by
      rfl
    _ = (C - A) + (A - B) := by
      exact (sub_add_sub_cancel C A B).symm
    _ = explicitFormulaRectangle_tangentPoleCorrectedContourIntegral f F T +
        explicitFormulaRectangle_completedPoleBoundaryTangentDefect f F T := by
      rfl

/-- The finite union of deleted disks around a finite set of singular coordinates. -/
def finiteRectangleDeletedDisks (S : Finset ℂ) (ε : ℝ) : Set ℂ :=
  {z : ℂ | ∃ a : ℂ, a ∈ S ∧ z ∈ Metric.ball a ε}

/-- The rectangle domain with the finite singular disks deleted. -/
def finiteRectanglePuncturedDomain (R : Set ℂ) (S : Finset ℂ) (ε : ℝ) : Set ℂ :=
  {z : ℂ | z ∈ R ∧ z ∉ finiteRectangleDeletedDisks S ε}

/-- A finite union of deleted disks indexed by an arbitrary finite singular-coordinate
carrier. -/
def finiteRectangleIndexedDeletedDisks {α : Type*}
    (S : Finset α) (center : α → ℂ) (ε : ℝ) : Set ℂ :=
  {z : ℂ | ∃ a : α, a ∈ S ∧ z ∈ Metric.ball (center a) ε}

/-- The base domain with disks around an indexed finite singular-coordinate carrier
deleted. -/
def finiteRectangleIndexedPuncturedDomain {α : Type*}
    (R : Set ℂ) (S : Finset α) (center : α → ℂ) (ε : ℝ) : Set ℂ :=
  {z : ℂ | z ∈ R ∧ z ∉ finiteRectangleIndexedDeletedDisks S center ε}

/-- Deleted disks around the completed-zero coordinates in the finite height window. -/
def explicitFormulaCompletedZeroWindowDeletedDisks (T ε : ℝ) : Set ℂ :=
  finiteRectangleIndexedDeletedDisks
    (explicitFormulaCompletedZeroContourHeightWindow T)
    (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} => completedZeroResidueCoordinate ρ)
    ε

/-- The finite set of completed-zero contour coordinates in the height window. -/
def explicitFormulaCompletedZeroWindowCoordinates (T : ℝ) : Finset ℂ :=
  (explicitFormulaCompletedZeroContourHeightWindow T).image
    (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} => completedZeroResidueCoordinate ρ)

/-- Every coordinate in the finite completed-zero carrier comes from a completed zero in
the height window. -/
theorem explicitFormulaCompletedZeroWindowCoordinates_exists_window_of_mem
    (T : ℝ) {z : ℂ}
    (hz : z ∈ explicitFormulaCompletedZeroWindowCoordinates T) :
    ∃ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
      ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T ∧
        completedZeroResidueCoordinate ρ = z :=
  Finset.mem_image.mp hz

/-- The finite singular-coordinate carrier for the raw completed contour integrand:
the completed-zero window coordinates together with the completed-zeta pole coordinates
`0` and `1`. -/
def explicitFormulaRectangleRawSingularCoordinates (T : ℝ) : Finset ℂ :=
  insert (0 : ℂ) (insert (1 : ℂ) (explicitFormulaCompletedZeroWindowCoordinates T))

/-- Finite deleted-circle boundary contributions are recorded with positive residue
orientation.  The punctured rectangle boundary therefore appears as outer boundary minus
this deleted-circle sum. -/
noncomputable def finiteRectangleDeletedCircleBoundarySum
    (S : Finset ℂ) (deletedCircle : ℂ → ℂ) : ℂ :=
  ∑ a in S, deletedCircle a

/-- Indexed raw singularities of the completed contour integrand in a finite rectangle:
the two completed-zeta pole coordinates and the finite completed-zero window.  This index
carrier preserves residue summands before mapping them to geometric coordinates. -/
inductive ExplicitFormulaRectangleRawSingularIndex (T : ℝ) where
  | zeroPole : ExplicitFormulaRectangleRawSingularIndex T
  | onePole : ExplicitFormulaRectangleRawSingularIndex T
  | completedZero :
      (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) →
      ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T →
      ExplicitFormulaRectangleRawSingularIndex T

/-- Coordinate of an indexed raw singularity. -/
def explicitFormulaRectangleRawSingularIndexCoordinate
    (T : ℝ) : ExplicitFormulaRectangleRawSingularIndex T → ℂ
  | ExplicitFormulaRectangleRawSingularIndex.zeroPole => 0
  | ExplicitFormulaRectangleRawSingularIndex.onePole => 1
  | ExplicitFormulaRectangleRawSingularIndex.completedZero ρ _ =>
      completedZeroResidueCoordinate ρ

/-- Residue summand of an indexed raw singularity. -/
noncomputable def explicitFormulaRectangleRawSingularIndexResidue
    (f : ZetaAdmissibleFunction) (T : ℝ) :
    ExplicitFormulaRectangleRawSingularIndex T → ℂ
  | ExplicitFormulaRectangleRawSingularIndex.zeroPole =>
      explicitFormulaRectangle_zeroPoleResidue f
  | ExplicitFormulaRectangleRawSingularIndex.onePole =>
      explicitFormulaRectangle_onePoleResidue f
  | ExplicitFormulaRectangleRawSingularIndex.completedZero ρ _ =>
      explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ)

/-- The indexed raw singular residue sum: completed-zeta pole residues plus the finite
completed-zero residue window. -/
noncomputable def explicitFormulaRectangleRawSingularIndexedResidueSum
    (f : ZetaAdmissibleFunction) (T : ℝ) : ℂ :=
  explicitFormulaRectangle_zeroPoleResidue f +
    explicitFormulaRectangle_onePoleResidue f +
      ∑ ρ in explicitFormulaCompletedZeroContourHeightWindow T,
        explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ)

/-- The indexed raw singular residue sum is the pole-corrected residue target. -/
theorem explicitFormulaRectangleRawSingularIndexedResidueSum_eq_poleCorrectedResidueSum
    (f : ZetaAdmissibleFunction) (T : ℝ) :
    explicitFormulaRectangleRawSingularIndexedResidueSum f T =
      explicitFormulaRectangle_poleCorrectedResidueSum f T := by
  let Z : ℂ := explicitFormulaRectangle_zeroPoleResidue f
  let O : ℂ := explicitFormulaRectangle_onePoleResidue f
  let W : ℂ :=
    ∑ ρ in explicitFormulaCompletedZeroContourHeightWindow T,
      explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ)
  have hW : W = explicitFormulaCompletedZeroContourHeightWindowResidueSum f T :=
    explicitFormulaRectangle_completedZeroResidueWindowSum_eq_heightWindowResidueSum f T
  calc
    explicitFormulaRectangleRawSingularIndexedResidueSum f T = Z + O + W := by
      rfl
    _ = W + (Z + O) := by
      calc
        Z + O + W = (Z + O) + W := by
          rfl
        _ = W + (Z + O) := by
          exact add_comm (Z + O) W
    _ = explicitFormulaCompletedZeroContourHeightWindowResidueSum f T + (Z + O) := by
      exact congrArg (fun x : ℂ => x + (Z + O)) hW
    _ = explicitFormulaCompletedZeroContourHeightWindowResidueSum f T +
        explicitFormulaRectangle_completedPoleResidueSum f := by
      rfl
    _ = explicitFormulaRectangle_poleCorrectedResidueSum f T := by
      exact (explicitFormulaRectangle_poleCorrectedResidueSum_eq f T).symm

/-- Evaluating the deleted-circle boundary contribution on the raw finite singular
coordinate carrier gives the indexed raw residue sum, provided each carrier coordinate has
the corresponding local deleted-circle residue value. -/
theorem finiteRectangleDeletedCircleBoundarySum_rawSingularCoordinates_eq_indexedResidueSum_of_values
    (f : ZetaAdmissibleFunction) (T : ℝ) (deletedCircle : ℂ → ℂ)
    (hzero :
      deletedCircle 0 = explicitFormulaRectangle_zeroPoleResidue f)
    (hone :
      deletedCircle 1 = explicitFormulaRectangle_onePoleResidue f)
    (hcompleted :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ∀ _hρ : ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T,
          deletedCircle (completedZeroResidueCoordinate ρ) =
            explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ)) :
    finiteRectangleDeletedCircleBoundarySum
        (explicitFormulaRectangleRawSingularCoordinates T) deletedCircle =
      explicitFormulaRectangleRawSingularIndexedResidueSum f T := by
  let C : Finset ℂ := explicitFormulaCompletedZeroWindowCoordinates T
  let W : Finset {ρ : ℂ // ZetaCompletedZero ρ} :=
    explicitFormulaCompletedZeroContourHeightWindow T
  have hzero_not_C : (0 : ℂ) ∉ C := by
    intro hmem
    exact
      Exists.elim
        (explicitFormulaCompletedZeroWindowCoordinates_exists_window_of_mem T hmem)
        (fun ρ hρ =>
          (completedZeroResidueCoordinate_ne_zero ρ) hρ.right)
  have hone_not_C : (1 : ℂ) ∉ C := by
    intro hmem
    exact
      Exists.elim
        (explicitFormulaCompletedZeroWindowCoordinates_exists_window_of_mem T hmem)
        (fun ρ hρ =>
          (completedZeroResidueCoordinate_ne_one ρ) hρ.right)
  have hzero_ne_one : (0 : ℂ) ≠ 1 :=
    zero_ne_one
  have hzero_not_insert : (0 : ℂ) ∉ insert (1 : ℂ) C := by
    intro hmem
    match Finset.mem_insert.mp hmem with
    | Or.inl h01 =>
        exact hzero_ne_one h01
    | Or.inr h0C =>
        exact hzero_not_C h0C
  have hone_not_insert_base : (1 : ℂ) ∉ C :=
    hone_not_C
  have himage :
      (∑ z in C, deletedCircle z) =
        ∑ ρ in W, deletedCircle (completedZeroResidueCoordinate ρ) := by
    exact
      Finset.sum_image
        (s := W)
        (f := fun z : ℂ => deletedCircle z)
        (g := fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          completedZeroResidueCoordinate ρ)
        (fun ρ _hρ σ _hσ hcoord =>
          completedZeroResidueCoordinate_injective hcoord)
  have hcompleted_sum :
      (∑ ρ in W, deletedCircle (completedZeroResidueCoordinate ρ)) =
        ∑ ρ in W,
          explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ) := by
    exact
      Finset.sum_congr rfl
        (fun ρ hρ => hcompleted ρ hρ)
  let Z : ℂ := explicitFormulaRectangle_zeroPoleResidue f
  let O : ℂ := explicitFormulaRectangle_onePoleResidue f
  let R : ℂ :=
    ∑ ρ in W,
      explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ)
  calc
    finiteRectangleDeletedCircleBoundarySum
        (explicitFormulaRectangleRawSingularCoordinates T) deletedCircle =
        ∑ z in insert (0 : ℂ) (insert (1 : ℂ) C), deletedCircle z := by
      rfl
    _ = deletedCircle 0 + ∑ z in insert (1 : ℂ) C, deletedCircle z := by
      exact Finset.sum_insert hzero_not_insert
    _ = deletedCircle 0 + (deletedCircle 1 + ∑ z in C, deletedCircle z) := by
      exact congrArg
        (fun x : ℂ => deletedCircle 0 + x)
        (Finset.sum_insert hone_not_insert_base)
    _ = Z + (deletedCircle 1 + ∑ z in C, deletedCircle z) := by
      exact congrArg
        (fun x : ℂ => x + (deletedCircle 1 + ∑ z in C, deletedCircle z))
        hzero
    _ = Z + (O + ∑ z in C, deletedCircle z) := by
      exact congrArg
        (fun x : ℂ => Z + (x + ∑ z in C, deletedCircle z))
        hone
    _ = Z + (O + ∑ ρ in W, deletedCircle (completedZeroResidueCoordinate ρ)) := by
      exact congrArg (fun x : ℂ => Z + (O + x)) himage
    _ = Z + (O + R) := by
      exact congrArg (fun x : ℂ => Z + (O + x)) hcompleted_sum
    _ = Z + O + R := by
      exact (add_assoc Z O R).symm
    _ = explicitFormulaRectangleRawSingularIndexedResidueSum f T := by
      rfl

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
