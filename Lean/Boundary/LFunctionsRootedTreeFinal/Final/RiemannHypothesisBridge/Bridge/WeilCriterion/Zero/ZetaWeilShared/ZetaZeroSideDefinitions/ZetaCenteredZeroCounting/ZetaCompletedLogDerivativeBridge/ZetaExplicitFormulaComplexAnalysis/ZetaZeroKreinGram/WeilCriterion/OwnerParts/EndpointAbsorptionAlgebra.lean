import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.NormalizedSignedBoundary
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PhysicalContourBoundaryCore
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.NormalizedCorrectionTarget
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.RightHalfPlaneGrowth.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.CompletedZetaGrowth.PoleCleared.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.EndpointCorrectionPacket

/-!
# Endpoint-absorption algebra for completed Weil positivity

This owner part contains the algebraic reduction from endpoint-absorbed
physical boundary nonnegativity to completed Weil positivity.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Boundary nonnegativity transports to the signed scalar absorption
inequality. -/
theorem completedBoundaryChannel_convolutionAutocorrelation_re_nonnegative_to_archimedeanAbsorption
    (f : ZetaAdmissibleFunction)
    (boundaryNonnegative :
      0 ≤ Complex.re
        (ZetaAdmissibleFunction.completedBoundaryChannel
          (ZetaAdmissibleFunction.convolutionAutocorrelation f))) :
      ZetaAdmissibleFunction.zetaCompletedArchimedeanNegativeVariationScalar f ≤
        ZetaAdmissibleFunction.zetaCompletedPhysicalPrimeBoundaryScalar f +
          ZetaAdmissibleFunction.zetaCompletedPhysicalCorrectionBoundaryScalar f +
          ZetaAdmissibleFunction.zetaCompletedArchimedeanPositiveVariationScalar f :=
  let boundaryEquality :
      Complex.re
          (ZetaAdmissibleFunction.completedBoundaryChannel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)) =
        ZetaAdmissibleFunction.zetaCompletedNormalizedSignedBoundaryScalar f :=
    ZetaAdmissibleFunction.completedBoundaryChannel_convolutionAutocorrelation_re_eq_normalizedSignedScalar
      f
  let scalarNonnegative :
      0 ≤
        ZetaAdmissibleFunction.zetaCompletedNormalizedSignedBoundaryScalar f :=
    Eq.subst
      (motive := fun value : ℝ => 0 ≤ value)
      boundaryEquality
      boundaryNonnegative
  (ZetaAdmissibleFunction.zetaCompletedNormalizedSignedBoundaryScalar_nonnegative_iff_absorption
    f).mp scalarNonnegative

/-- Signed scalar absorption transports to completed-boundary nonnegativity. -/
theorem archimedeanAbsorption_to_completedBoundaryChannel_convolutionAutocorrelation_re_nonnegative
    (f : ZetaAdmissibleFunction)
    (absorption :
      ZetaAdmissibleFunction.zetaCompletedArchimedeanNegativeVariationScalar f ≤
        ZetaAdmissibleFunction.zetaCompletedPhysicalPrimeBoundaryScalar f +
          ZetaAdmissibleFunction.zetaCompletedPhysicalCorrectionBoundaryScalar f +
          ZetaAdmissibleFunction.zetaCompletedArchimedeanPositiveVariationScalar f) :
    0 ≤ Complex.re
      (ZetaAdmissibleFunction.completedBoundaryChannel
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :=
  let boundaryEquality :
      Complex.re
          (ZetaAdmissibleFunction.completedBoundaryChannel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)) =
        ZetaAdmissibleFunction.zetaCompletedNormalizedSignedBoundaryScalar f :=
    ZetaAdmissibleFunction.completedBoundaryChannel_convolutionAutocorrelation_re_eq_normalizedSignedScalar
      f
  let scalarNonnegative :
      0 ≤
        ZetaAdmissibleFunction.zetaCompletedNormalizedSignedBoundaryScalar f :=
    (ZetaAdmissibleFunction.zetaCompletedNormalizedSignedBoundaryScalar_nonnegative_iff_absorption
      f).mpr absorption
  Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    boundaryEquality.symm
    scalarNonnegative

/-- Boundary nonnegativity is exactly absorption of the negative
archimedean variation by the physical prime scalar, the pole correction scalar,
and the positive archimedean variation. -/
theorem completedBoundaryChannel_convolutionAutocorrelation_re_nonnegative_iff_archimedeanAbsorption_owner
    (f : ZetaAdmissibleFunction) :
    0 ≤ Complex.re
        (ZetaAdmissibleFunction.completedBoundaryChannel
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) ↔
      ZetaAdmissibleFunction.zetaCompletedArchimedeanNegativeVariationScalar f ≤
        ZetaAdmissibleFunction.zetaCompletedPhysicalPrimeBoundaryScalar f +
          ZetaAdmissibleFunction.zetaCompletedPhysicalCorrectionBoundaryScalar f +
          ZetaAdmissibleFunction.zetaCompletedArchimedeanPositiveVariationScalar f :=
  Iff.intro
    (completedBoundaryChannel_convolutionAutocorrelation_re_nonnegative_to_archimedeanAbsorption
      f)
    (archimedeanAbsorption_to_completedBoundaryChannel_convolutionAutocorrelation_re_nonnegative
      f)

/-- Pointwise completed-boundary positivity gives pointwise signed scalar
absorption. -/
theorem completedBoundaryQuadraticPositivity_to_physicalArchimedeanAbsorption
    (boundaryPositive :
      ∀ f : ZetaAdmissibleFunction,
        0 ≤ Complex.re
          (ZetaAdmissibleFunction.completedBoundaryChannel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f))) :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.zetaCompletedArchimedeanNegativeVariationScalar f ≤
          ZetaAdmissibleFunction.zetaCompletedPhysicalPrimeBoundaryScalar f +
            ZetaAdmissibleFunction.zetaCompletedPhysicalCorrectionBoundaryScalar f +
            ZetaAdmissibleFunction.zetaCompletedArchimedeanPositiveVariationScalar f :=
  fun f =>
    completedBoundaryChannel_convolutionAutocorrelation_re_nonnegative_to_archimedeanAbsorption
      f
      (boundaryPositive f)

/-- Pointwise signed scalar absorption gives completed-boundary positivity. -/
theorem physicalArchimedeanAbsorption_to_completedBoundaryQuadraticPositivity
    (absorption :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.zetaCompletedArchimedeanNegativeVariationScalar f ≤
          ZetaAdmissibleFunction.zetaCompletedPhysicalPrimeBoundaryScalar f +
            ZetaAdmissibleFunction.zetaCompletedPhysicalCorrectionBoundaryScalar f +
            ZetaAdmissibleFunction.zetaCompletedArchimedeanPositiveVariationScalar f) :
    ∀ f : ZetaAdmissibleFunction,
      0 ≤ Complex.re
        (ZetaAdmissibleFunction.completedBoundaryChannel
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :=
  fun f =>
    archimedeanAbsorption_to_completedBoundaryChannel_convolutionAutocorrelation_re_nonnegative
      f
      (absorption f)

/-- Completed-boundary positivity on every autocorrelation probe is exactly
the physical prime and signed-archimedean absorption inequality on every
seed. -/
theorem completedBoundaryQuadraticPositivity_iff_physicalArchimedeanAbsorption_owner :
    (∀ f : ZetaAdmissibleFunction,
      0 ≤ Complex.re
        (ZetaAdmissibleFunction.completedBoundaryChannel
          (ZetaAdmissibleFunction.convolutionAutocorrelation f))) ↔
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.zetaCompletedArchimedeanNegativeVariationScalar f ≤
          ZetaAdmissibleFunction.zetaCompletedPhysicalPrimeBoundaryScalar f +
            ZetaAdmissibleFunction.zetaCompletedPhysicalCorrectionBoundaryScalar f +
            ZetaAdmissibleFunction.zetaCompletedArchimedeanPositiveVariationScalar f :=
  Iff.intro
    completedBoundaryQuadraticPositivity_to_physicalArchimedeanAbsorption
    physicalArchimedeanAbsorption_to_completedBoundaryQuadraticPositivity

/-- Completed Weil positivity transports across a boundary identification to
completed-boundary positivity. -/
theorem zetaWeilQuadraticPositivity_to_completedBoundaryQuadraticPositivity_of_boundaryIdentification
    (boundaryIdentification :
      ∀ f : ZetaAdmissibleFunction,
        zetaWeilFormCompleted
            (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
          Complex.re
            (ZetaAdmissibleFunction.completedBoundaryChannel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)))
    (weilPositive : ZetaWeilQuadraticPositivity) :
    ∀ f : ZetaAdmissibleFunction,
      0 ≤ Complex.re
        (ZetaAdmissibleFunction.completedBoundaryChannel
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :=
  fun f =>
    Eq.subst
      (motive := fun value : ℝ => 0 ≤ value)
      (boundaryIdentification f)
      (weilPositive f)

/-- Completed-boundary positivity transports back across a boundary
identification to completed Weil positivity. -/
theorem completedBoundaryQuadraticPositivity_to_zetaWeilQuadraticPositivity_of_boundaryIdentification
    (boundaryIdentification :
      ∀ f : ZetaAdmissibleFunction,
        zetaWeilFormCompleted
            (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
          Complex.re
            (ZetaAdmissibleFunction.completedBoundaryChannel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)))
    (boundaryPositive :
      ∀ f : ZetaAdmissibleFunction,
        0 ≤ Complex.re
          (ZetaAdmissibleFunction.completedBoundaryChannel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f))) :
    ZetaWeilQuadraticPositivity :=
  fun f =>
    Eq.subst
      (motive := fun value : ℝ => 0 ≤ value)
      (boundaryIdentification f).symm
      (boundaryPositive f)

/-- Completed Weil positivity gives signed scalar absorption after boundary
identification. -/
theorem zetaWeilQuadraticPositivity_to_physicalArchimedeanAbsorption_of_boundaryIdentification
    (boundaryIdentification :
      ∀ f : ZetaAdmissibleFunction,
        zetaWeilFormCompleted
            (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
          Complex.re
            (ZetaAdmissibleFunction.completedBoundaryChannel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)))
    (weilPositive : ZetaWeilQuadraticPositivity) :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.zetaCompletedArchimedeanNegativeVariationScalar f ≤
          ZetaAdmissibleFunction.zetaCompletedPhysicalPrimeBoundaryScalar f +
            ZetaAdmissibleFunction.zetaCompletedPhysicalCorrectionBoundaryScalar f +
            ZetaAdmissibleFunction.zetaCompletedArchimedeanPositiveVariationScalar f :=
  completedBoundaryQuadraticPositivity_to_physicalArchimedeanAbsorption
    (zetaWeilQuadraticPositivity_to_completedBoundaryQuadraticPositivity_of_boundaryIdentification
      boundaryIdentification
      weilPositive)

/-- Signed scalar absorption gives completed Weil positivity after boundary
identification. -/
theorem physicalArchimedeanAbsorption_to_zetaWeilQuadraticPositivity_of_boundaryIdentification
    (boundaryIdentification :
      ∀ f : ZetaAdmissibleFunction,
        zetaWeilFormCompleted
            (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
          Complex.re
            (ZetaAdmissibleFunction.completedBoundaryChannel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)))
    (absorption :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.zetaCompletedArchimedeanNegativeVariationScalar f ≤
          ZetaAdmissibleFunction.zetaCompletedPhysicalPrimeBoundaryScalar f +
            ZetaAdmissibleFunction.zetaCompletedPhysicalCorrectionBoundaryScalar f +
            ZetaAdmissibleFunction.zetaCompletedArchimedeanPositiveVariationScalar f) :
    ZetaWeilQuadraticPositivity :=
  completedBoundaryQuadraticPositivity_to_zetaWeilQuadraticPositivity_of_boundaryIdentification
    boundaryIdentification
    (physicalArchimedeanAbsorption_to_completedBoundaryQuadraticPositivity
      absorption)

/-- Once the contour formula identifies the completed Weil form with the
physical completed boundary, quadratic Weil positivity is exactly the
physical prime and signed-archimedean absorption inequality. -/
theorem zetaWeilQuadraticPositivity_iff_physicalArchimedeanAbsorption_of_boundaryIdentification
    (boundaryIdentification :
      ∀ f : ZetaAdmissibleFunction,
        zetaWeilFormCompleted
            (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
          Complex.re
            (ZetaAdmissibleFunction.completedBoundaryChannel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f))) :
    ZetaWeilQuadraticPositivity ↔
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.zetaCompletedArchimedeanNegativeVariationScalar f ≤
          ZetaAdmissibleFunction.zetaCompletedPhysicalPrimeBoundaryScalar f +
            ZetaAdmissibleFunction.zetaCompletedPhysicalCorrectionBoundaryScalar f +
            ZetaAdmissibleFunction.zetaCompletedArchimedeanPositiveVariationScalar f :=
  Iff.intro
    (zetaWeilQuadraticPositivity_to_physicalArchimedeanAbsorption_of_boundaryIdentification
      boundaryIdentification)
    (physicalArchimedeanAbsorption_to_zetaWeilQuadraticPositivity_of_boundaryIdentification
      boundaryIdentification)

/-- Endpoint-absorbed physical nonnegativity is sufficient for nonnegativity
of the canonical completed Weil boundary on one autocorrelation probe. -/
theorem completedWeilBoundaryChannel_convolutionAutocorrelation_re_nonnegative_of_endpointAbsorbedPhysical_owner
    (f : ZetaAdmissibleFunction)
    (endpointAbsorption :
      0 ≤ ZetaAdmissibleFunction.completedWeilEndpointAbsorbedPhysicalScalar f) :
    0 ≤ Complex.re
      (ZetaAdmissibleFunction.completedWeilBoundaryChannel
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :=
  ZetaAdmissibleFunction.completedWeilBoundaryChannel_convolutionAutocorrelation_re_nonnegative_of_absorbedPhysical
    f endpointAbsorption

/-- On an autocorrelation probe, the completed pole residue packet is the
endpoint correction channel. -/
theorem explicitFormulaRectangle_completedPoleResidueSum_convolutionAutocorrelation_eq_endpointCorrection_owner
    (f : ZetaAdmissibleFunction) :
    ZetaAdmissibleFunction.explicitFormulaRectangle_completedPoleResidueSum
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      ZetaAdmissibleFunction.completedWeilEndpointCorrectionChannel
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) :=
  Eq.trans
    (ZetaAdmissibleFunction.explicitFormulaRectangle_completedPoleResidueSum_eq
      (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (ZetaAdmissibleFunction.completedWeilEndpointCorrectionChannel_eq
      (ZetaAdmissibleFunction.convolutionAutocorrelation f)).symm

/-- On an autocorrelation probe, the completed pole residue real part is the
endpoint square minus the diagonal debt. -/
theorem explicitFormulaRectangle_completedPoleResidueSum_convolutionAutocorrelation_re_eq_completedSquare_sub_diagonalDebt_owner
    (f : ZetaAdmissibleFunction) :
    Complex.re
        (ZetaAdmissibleFunction.explicitFormulaRectangle_completedPoleResidueSum
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) =
      (ZetaAdmissibleFunction.zetaCompletedEndpointCorrectionPacket f).completedSquare -
        (ZetaAdmissibleFunction.zetaCompletedEndpointCorrectionPacket f).diagonalDebt :=
  Eq.trans
    (congrArg Complex.re
      (explicitFormulaRectangle_completedPoleResidueSum_convolutionAutocorrelation_eq_endpointCorrection_owner
        f))
    (ZetaAdmissibleFunction.completedWeilEndpointCorrectionChannel_convolutionAutocorrelation_re_eq_completedSquare_sub_diagonalDebt
      f)

/-- The pole-corrected completed boundary real part is the completed boundary
real part minus the endpoint correction real part. -/
theorem zetaCompletedPoleCorrectedBoundaryChannel_convolutionAutocorrelation_re_eq_boundary_re_sub_pole_re_owner
    (f : ZetaAdmissibleFunction) :
    Complex.re
        (ZetaAdmissibleFunction.zetaCompletedPoleCorrectedBoundaryChannel
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) =
      Complex.re
          (ZetaAdmissibleFunction.completedBoundaryChannel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)) -
        Complex.re
          (ZetaAdmissibleFunction.explicitFormulaRectangle_completedPoleResidueSum
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :=
  Eq.trans
    (congrArg Complex.re
      (ZetaAdmissibleFunction.zetaCompletedPoleCorrectedBoundaryChannel_eq
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)))
    (Complex.sub_re
      (ZetaAdmissibleFunction.completedBoundaryChannel
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
      (ZetaAdmissibleFunction.explicitFormulaRectangle_completedPoleResidueSum
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)))

/-! The complex-valued endpoint transport precedes taking real parts. -/
theorem completedBoundaryChannel_convolutionAutocorrelation_eq_poleCorrected_add_endpointCorrectionChannel_owner
    (f : ZetaAdmissibleFunction) :
    ZetaAdmissibleFunction.completedBoundaryChannel
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      ZetaAdmissibleFunction.zetaCompletedPoleCorrectedBoundaryChannel
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) +
        ZetaAdmissibleFunction.completedWeilEndpointCorrectionChannel
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) := by
  exact
    Eq.trans
      (sub_eq_iff_eq_add.mp
        (ZetaAdmissibleFunction.zetaCompletedPoleCorrectedBoundaryChannel_eq
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)).symm)
      (congrArg
        (fun value : ℂ =>
          ZetaAdmissibleFunction.zetaCompletedPoleCorrectedBoundaryChannel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f) + value)
        (explicitFormulaRectangle_completedPoleResidueSum_convolutionAutocorrelation_eq_endpointCorrection_owner
          f))

/-- The pole-corrected completed boundary real part is the completed boundary
real part minus the endpoint square-minus-debt packet. -/
theorem zetaCompletedPoleCorrectedBoundaryChannel_convolutionAutocorrelation_re_eq_boundary_re_sub_endpointSquareSubDebt_owner
    (f : ZetaAdmissibleFunction) :
    Complex.re
        (ZetaAdmissibleFunction.zetaCompletedPoleCorrectedBoundaryChannel
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) =
      Complex.re
          (ZetaAdmissibleFunction.completedBoundaryChannel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)) -
        ((ZetaAdmissibleFunction.zetaCompletedEndpointCorrectionPacket f).completedSquare -
          (ZetaAdmissibleFunction.zetaCompletedEndpointCorrectionPacket f).diagonalDebt) :=
  Eq.trans
    (zetaCompletedPoleCorrectedBoundaryChannel_convolutionAutocorrelation_re_eq_boundary_re_sub_pole_re_owner
      f)
    (congrArg
      (fun value : ℝ =>
        Complex.re
            (ZetaAdmissibleFunction.completedBoundaryChannel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)) -
          value)
        (explicitFormulaRectangle_completedPoleResidueSum_convolutionAutocorrelation_re_eq_completedSquare_sub_diagonalDebt_owner
        f))

/-! Reverse transport is the form needed when the contour theorem supplies the
pole-corrected boundary and the endpoint packet must be restored. -/
theorem completedBoundaryChannel_convolutionAutocorrelation_re_eq_poleCorrected_add_endpointSquareSubDebt_owner
    (f : ZetaAdmissibleFunction) :
    Complex.re
        (ZetaAdmissibleFunction.completedBoundaryChannel
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) =
      Complex.re
          (ZetaAdmissibleFunction.zetaCompletedPoleCorrectedBoundaryChannel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)) +
        ((ZetaAdmissibleFunction.zetaCompletedEndpointCorrectionPacket f).completedSquare -
          (ZetaAdmissibleFunction.zetaCompletedEndpointCorrectionPacket f).diagonalDebt) := by
  exact
    Eq.trans
      (congrArg Complex.re
        (completedBoundaryChannel_convolutionAutocorrelation_eq_poleCorrected_add_endpointCorrectionChannel_owner
          f))
      (congrArg
        (fun value : ℝ =>
          Complex.re
              (ZetaAdmissibleFunction.zetaCompletedPoleCorrectedBoundaryChannel
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)) + value)
        (ZetaAdmissibleFunction.completedWeilEndpointCorrectionChannel_convolutionAutocorrelation_re_eq_completedSquare_sub_diagonalDebt
          f))

/-! Restore the pole packet in its canonical endpoint-channel form before
expanding that channel into the square/debt coordinates. -/
theorem completedBoundaryChannel_convolutionAutocorrelation_re_eq_poleCorrected_add_endpointCorrectionChannel_owner
    (f : ZetaAdmissibleFunction) :
    Complex.re
        (ZetaAdmissibleFunction.completedBoundaryChannel
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) =
      Complex.re
          (ZetaAdmissibleFunction.zetaCompletedPoleCorrectedBoundaryChannel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)) +
        Complex.re
          (ZetaAdmissibleFunction.completedWeilEndpointCorrectionChannel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)) := by
  exact
    congrArg Complex.re
      (completedBoundaryChannel_convolutionAutocorrelation_eq_poleCorrected_add_endpointCorrectionChannel_owner
        f)

/-! The pole-corrected channel is therefore the completed boundary with the
explicit endpoint channel removed, before expanding that channel into packet
coordinates. -/
theorem zetaCompletedPoleCorrectedBoundaryChannel_convolutionAutocorrelation_re_eq_boundary_re_sub_endpointCorrectionChannel_owner
    (f : ZetaAdmissibleFunction) :
    Complex.re
        (ZetaAdmissibleFunction.zetaCompletedPoleCorrectedBoundaryChannel
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) =
      Complex.re
          (ZetaAdmissibleFunction.completedBoundaryChannel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)) -
        Complex.re
          (ZetaAdmissibleFunction.completedWeilEndpointCorrectionChannel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)) := by
  exact
    sub_eq_iff_eq_add.mpr
      (completedBoundaryChannel_convolutionAutocorrelation_re_eq_poleCorrected_add_endpointCorrectionChannel_owner
        f)

/-- Twice a debt minus a square is two explicit debt copies and the negative
square. -/
theorem endpointAbsorption_two_mul_sub_eq_add_add_neg
    (debt square : ℝ) :
    2 * debt - square = debt + (debt + -square) :=
  calc
    2 * debt - square =
        2 * debt + -square :=
      sub_eq_add_neg (2 * debt) square
    _ = (debt + debt) + -square :=
      congrArg
        (fun value : ℝ => value + -square)
        (two_mul debt)
    _ = debt + (debt + -square) :=
      add_assoc debt debt (-square)

/-- The right-hand endpoint reserve expression regroups to the same
`physical + debt - square` normal form. -/
theorem endpointAbsorption_regroupRight
    (physical debt square : ℝ) :
    (physical - debt) + (2 * debt - square) =
      physical + (debt + -square) :=
  calc
    (physical - debt) + (2 * debt - square) =
        (physical + -debt) + (2 * debt - square) :=
      congrArg
        (fun value : ℝ => value + (2 * debt - square))
        (sub_eq_add_neg physical debt)
    _ = (physical + -debt) + (debt + (debt + -square)) :=
      congrArg
        (fun value : ℝ => (physical + -debt) + value)
        (endpointAbsorption_two_mul_sub_eq_add_add_neg debt square)
    _ = physical + (-debt + (debt + (debt + -square))) :=
      add_assoc physical (-debt) (debt + (debt + -square))
    _ = physical + ((-debt + debt) + (debt + -square)) :=
      congrArg
        (fun value : ℝ => physical + value)
        (add_assoc (-debt) debt (debt + -square)).symm
    _ = physical + (0 + (debt + -square)) :=
      congrArg
        (fun value : ℝ => physical + (value + (debt + -square)))
        (add_left_neg debt)
    _ = physical + (debt + -square) :=
      congrArg
        (fun value : ℝ => physical + value)
        (zero_add (debt + -square))

/-- Subtracting the endpoint square-minus-debt packet regroups as absorbed
physical plus the endpoint reserve. -/
theorem endpointAbsorption_scalarRegroup
    (physical debt square : ℝ) :
    physical - (square - debt) =
      (physical - debt) + (2 * debt - square) :=
  let negSubtraction :
      -(square + -debt) = -square + - -debt :=
    neg_add square (-debt)
  let negNegDebt :
      - -debt = debt :=
    neg_neg debt
  let negSubtractionAsDebt :
      -(square + -debt) = -square + debt :=
    Eq.trans
      negSubtraction
      (congrArg
        (fun value : ℝ => -square + value)
        negNegDebt)
  calc
    physical - (square - debt) =
        physical + -(square - debt) :=
      sub_eq_add_neg physical (square - debt)
    _ = physical + -(square + -debt) :=
      congrArg
        (fun value : ℝ => physical + -value)
        (sub_eq_add_neg square debt)
    _ = physical + (-square + debt) :=
      congrArg
        (fun value : ℝ => physical + value)
        negSubtractionAsDebt
    _ = physical + (debt + -square) :=
      congrArg
        (fun value : ℝ => physical + value)
        (add_comm (-square) debt)
    _ = (physical - debt) + (2 * debt - square) :=
      (endpointAbsorption_regroupRight physical debt square).symm

/-- The pole-corrected contour boundary is the endpoint-absorbed physical
scalar plus the nonnegative two-endpoint Cauchy reserve. -/
theorem zetaCompletedPoleCorrectedBoundaryChannel_convolutionAutocorrelation_re_eq_absorbedPhysical_add_endpointReserve_owner
    (f : ZetaAdmissibleFunction) :
    Complex.re
        (ZetaAdmissibleFunction.zetaCompletedPoleCorrectedBoundaryChannel
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) =
      ZetaAdmissibleFunction.completedWeilEndpointAbsorbedPhysicalScalar f +
        (2 * (ZetaAdmissibleFunction.zetaCompletedEndpointCorrectionPacket f).diagonalDebt -
          (ZetaAdmissibleFunction.zetaCompletedEndpointCorrectionPacket f).completedSquare) :=
  let physical : ℝ :=
    Complex.re
      (ZetaAdmissibleFunction.completedBoundaryChannel
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
  let debt : ℝ :=
    (ZetaAdmissibleFunction.zetaCompletedEndpointCorrectionPacket f).diagonalDebt
  let square : ℝ :=
    (ZetaAdmissibleFunction.zetaCompletedEndpointCorrectionPacket f).completedSquare
  let boundarySplit :
      Complex.re
          (ZetaAdmissibleFunction.zetaCompletedPoleCorrectedBoundaryChannel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)) =
        physical - (square - debt) :=
    Eq.trans
      (sub_eq_iff_eq_add.mpr
        (congrArg Complex.re
          (completedBoundaryChannel_convolutionAutocorrelation_eq_poleCorrected_add_endpointCorrectionChannel_owner
            f))).symm
      (congrArg
        (fun value : ℝ => physical - value)
        (ZetaAdmissibleFunction.completedWeilEndpointCorrectionChannel_convolutionAutocorrelation_re_eq_completedSquare_sub_diagonalDebt
          f))
  let absorbedUnfold :
      ZetaAdmissibleFunction.completedWeilEndpointAbsorbedPhysicalScalar f =
        physical - debt :=
    ZetaAdmissibleFunction.completedWeilEndpointAbsorbedPhysicalScalar_eq_boundaryChannel_re_sub_diagonalDebt
      f
  let scalarRegroup :
      physical - (square - debt) =
        (physical - debt) + (2 * debt - square) :=
    endpointAbsorption_scalarRegroup physical debt square
  Eq.trans boundarySplit
    (Eq.trans scalarRegroup
      (congrArg₂ HAdd.hAdd absorbedUnfold.symm (Eq.refl (2 * debt - square))))

/-- A square bounded by twice the endpoint debt leaves a nonnegative reserve. -/
theorem endpointReserve_nonnegative_of_square_le_twoDebt
    (debt square : ℝ)
    (square_le_twoDebt : square ≤ 2 * debt) :
    0 ≤ 2 * debt - square :=
  sub_nonneg.mpr square_le_twoDebt

/-- The two-endpoint Cauchy reserve is nonnegative. -/
theorem zetaCompletedEndpointReserve_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤
      2 * (ZetaAdmissibleFunction.zetaCompletedEndpointCorrectionPacket f).diagonalDebt -
        (ZetaAdmissibleFunction.zetaCompletedEndpointCorrectionPacket f).completedSquare :=
  endpointReserve_nonnegative_of_square_le_twoDebt
    (ZetaAdmissibleFunction.zetaCompletedEndpointCorrectionPacket f).diagonalDebt
    (ZetaAdmissibleFunction.zetaCompletedEndpointCorrectionPacket f).completedSquare
    (ZetaAdmissibleFunction.ZetaCompletedEndpointCorrectionPacket.completedSquare_le_two_diagonalDebt
      (ZetaAdmissibleFunction.zetaCompletedEndpointCorrectionPacket f))

/-- Endpoint-absorbed physical nonnegativity plus reserve nonnegativity gives
nonnegativity of their sum. -/
theorem completedWeilEndpointAbsorbedPhysical_add_endpointReserve_nonnegative
    (f : ZetaAdmissibleFunction)
    (endpointAbsorption :
      0 ≤ ZetaAdmissibleFunction.completedWeilEndpointAbsorbedPhysicalScalar f) :
    0 ≤ ZetaAdmissibleFunction.completedWeilEndpointAbsorbedPhysicalScalar f +
      (2 * (ZetaAdmissibleFunction.zetaCompletedEndpointCorrectionPacket f).diagonalDebt -
        (ZetaAdmissibleFunction.zetaCompletedEndpointCorrectionPacket f).completedSquare) :=
  add_nonneg endpointAbsorption (zetaCompletedEndpointReserve_nonnegative f)

/-- Endpoint-absorbed physical nonnegativity is sufficient for nonnegativity
of the pole-corrected completed boundary identified by the normalized contour. -/
theorem zetaCompletedPoleCorrectedBoundaryChannel_convolutionAutocorrelation_re_nonnegative_of_endpointAbsorbedPhysical_owner
    (f : ZetaAdmissibleFunction)
    (endpointAbsorption :
      0 ≤ ZetaAdmissibleFunction.completedWeilEndpointAbsorbedPhysicalScalar f) :
    0 ≤ Complex.re
      (ZetaAdmissibleFunction.zetaCompletedPoleCorrectedBoundaryChannel
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :=
  Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (zetaCompletedPoleCorrectedBoundaryChannel_convolutionAutocorrelation_re_eq_absorbedPhysical_add_endpointReserve_owner
      f).symm
    (completedWeilEndpointAbsorbedPhysical_add_endpointReserve_nonnegative
      f
      endpointAbsorption)

/-- Boundary plus endpoint debt restores the raw physical boundary scalar. -/
theorem endpointAbsorption_boundary_add_debt_eq_physical
    (physical absorbed debt : ℝ)
    (absorbed_eq : absorbed = physical - debt) :
    absorbed + debt = physical :=
  Eq.trans
    (congrArg (fun value : ℝ => value + debt) absorbed_eq)
    (sub_add_cancel physical debt)

/-- The completed boundary real part splits as endpoint-absorbed physical
scalar plus the endpoint diagonal debt. -/
theorem completedBoundaryChannel_convolutionAutocorrelation_re_eq_absorbedPhysical_add_diagonalDebt_owner
    (f : ZetaAdmissibleFunction) :
    Complex.re
        (ZetaAdmissibleFunction.completedBoundaryChannel
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) =
      ZetaAdmissibleFunction.completedWeilEndpointAbsorbedPhysicalScalar f +
        (ZetaAdmissibleFunction.zetaCompletedEndpointCorrectionPacket f).diagonalDebt :=
  let physical : ℝ :=
    Complex.re
      (ZetaAdmissibleFunction.completedBoundaryChannel
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
  let debt : ℝ :=
    (ZetaAdmissibleFunction.zetaCompletedEndpointCorrectionPacket f).diagonalDebt
  let absorbed : ℝ :=
    ZetaAdmissibleFunction.completedWeilEndpointAbsorbedPhysicalScalar f
  let absorbedUnfold :
      absorbed = physical - debt :=
    ZetaAdmissibleFunction.completedWeilEndpointAbsorbedPhysicalScalar_eq_boundaryChannel_re_sub_diagonalDebt
      f
  (endpointAbsorption_boundary_add_debt_eq_physical physical absorbed debt
    absorbedUnfold).symm

/-- The absorbed physical scalar and endpoint debt have nonnegative sum. -/
theorem completedWeilEndpointAbsorbedPhysical_add_diagonalDebt_nonnegative
    (f : ZetaAdmissibleFunction)
    (endpointAbsorption :
      0 ≤ ZetaAdmissibleFunction.completedWeilEndpointAbsorbedPhysicalScalar f) :
    0 ≤
      ZetaAdmissibleFunction.completedWeilEndpointAbsorbedPhysicalScalar f +
        (ZetaAdmissibleFunction.zetaCompletedEndpointCorrectionPacket f).diagonalDebt :=
  add_nonneg
    endpointAbsorption
    (ZetaAdmissibleFunction.zetaCompletedEndpointCorrectionPacket f).diagonalDebt_nonnegative

/-- Endpoint-absorbed physical nonnegativity plus endpoint diagonal-debt
nonnegativity gives completed-boundary nonnegativity. -/
theorem completedBoundaryChannel_convolutionAutocorrelation_re_nonnegative_of_endpointAbsorbedPhysical_split_owner
    (f : ZetaAdmissibleFunction)
    (endpointAbsorption :
      0 ≤ ZetaAdmissibleFunction.completedWeilEndpointAbsorbedPhysicalScalar f) :
    0 ≤ Complex.re
      (ZetaAdmissibleFunction.completedBoundaryChannel
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :=
  Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (completedBoundaryChannel_convolutionAutocorrelation_re_eq_absorbedPhysical_add_diagonalDebt_owner
      f).symm
    (completedWeilEndpointAbsorbedPhysical_add_diagonalDebt_nonnegative
      f
      endpointAbsorption)

/-- Endpoint-absorbed physical nonnegativity is sufficient for nonnegativity
of the canonical completed boundary itself.  This is the coordinate used by
the standard contour assembly owner. -/
theorem completedBoundaryChannel_convolutionAutocorrelation_re_nonnegative_of_endpointAbsorbedPhysical_owner
    (f : ZetaAdmissibleFunction)
    (endpointAbsorption :
      0 ≤ ZetaAdmissibleFunction.completedWeilEndpointAbsorbedPhysicalScalar f) :
    0 ≤ Complex.re
      (ZetaAdmissibleFunction.completedBoundaryChannel
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :=
  completedBoundaryChannel_convolutionAutocorrelation_re_nonnegative_of_endpointAbsorbedPhysical_split_owner
    f
    endpointAbsorption

/-- Completed Weil positivity reduces to the endpoint-absorbed physical
boundary inequality.  This is the owner-level reduction to positive trace
reconstruction. -/
theorem zetaWeilQuadraticPositivity_of_endpointAbsorbedPhysical_owner
    (boundaryIdentification :
      ZetaWeilAutocorrelationCompletedBoundaryIdentification)
    (endpointAbsorption :
      ∀ f : ZetaAdmissibleFunction,
        0 ≤ ZetaAdmissibleFunction.completedWeilEndpointAbsorbedPhysicalScalar f) :
    ZetaWeilQuadraticPositivity :=
  fun f =>
    Eq.subst
      (motive := fun value : ℝ => 0 ≤ value)
      (boundaryIdentification f).symm
      (completedBoundaryChannel_convolutionAutocorrelation_re_nonnegative_of_endpointAbsorbedPhysical_owner
        f (endpointAbsorption f))

end

end LFunctions
end Boundary
