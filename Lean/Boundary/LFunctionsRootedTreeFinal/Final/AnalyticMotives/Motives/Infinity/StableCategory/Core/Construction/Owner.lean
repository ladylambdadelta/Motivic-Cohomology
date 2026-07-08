import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.VerdierQuotient.Zero.Owner

/-!
# Construction of the stable infinity category of analytic motives

This file owns the concrete assembled value of the stable-infinity package.
The structure fields live one level up in `StableCategory/Core/Owner.lean`.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The stable infinity category of analytic motives, built from the analytic
Verdier quotient and its nerve. -/
def traceAnalyticStableInfinityCategory :
    TraceAnalyticStableInfinityCategory where
  quasicategory :=
    TraceAnalyticStableMotiveQuasicategory.quasicategory
  localization :=
    TraceAnalyticStableMotiveQuasicategory.isLocalization
  preadditive :=
    TraceAnalyticStableMotiveCategory.preadditiveStructure
  zeroObject :=
    TraceAnalyticStableMotiveCategory.zeroObjectStructure
  shift :=
    TraceAnalyticStableMotiveQuasicategory.hasShiftStructure
  suspension :=
    TraceAnalyticStableMotiveQuasicategory.suspensionFunctor
  loop :=
    TraceAnalyticStableMotiveQuasicategory.loopFunctor
  suspensionLoopEquivalence :=
    TraceAnalyticStableMotiveQuasicategory.suspensionLoopEquivalence
  suspension_eq_shift :=
    rfl
  loop_eq_shift :=
    rfl
  suspensionLoopEquivalence_eq_shiftEquiv :=
    rfl
  quotientCommShift :=
    TraceAnalyticStableMotiveCategory.quotientFunctorCommShift
  pretriangulated :=
    TraceAnalyticStableMotiveQuasicategory.pretriangulatedStructure
  triangulated :=
    TraceAnalyticStableMotiveQuasicategory.triangulatedStructure
  distinguishedTriangles :=
    TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles
  distinguishedTriangles_eq :=
    rfl
  distinguishedCofiberTriangle :=
    TraceAnalyticStableMotiveQuasicategory.distinguishedCofiberTriangle
  contractibleTriangle_distinguished :=
    TraceAnalyticStableMotiveQuasicategory.contractibleTriangle_distinguished
  rotate_distinguishedTriangle :=
    TraceAnalyticStableMotiveQuasicategory.rotate_distinguishedTriangle
  complete_distinguishedTriangleMorphism :=
    TraceAnalyticStableMotiveQuasicategory.complete_distinguishedTriangleMorphism
  triangleFirstProjection :=
    TraceAnalyticStableMotiveQuasicategory.triangleFirstProjection
  triangleSecondProjection :=
    TraceAnalyticStableMotiveQuasicategory.triangleSecondProjection
  triangleThirdProjection :=
    TraceAnalyticStableMotiveQuasicategory.triangleThirdProjection
  triangleRotateFunctor :=
    TraceAnalyticStableMotiveQuasicategory.triangleRotateFunctor
  triangleInvRotateFunctor :=
    TraceAnalyticStableMotiveQuasicategory.triangleInvRotateFunctor
  triangleRotationEquivalence :=
    TraceAnalyticStableMotiveQuasicategory.triangleRotationEquivalence
  triangleShiftFunctor :=
    TraceAnalyticStableMotiveQuasicategory.triangleShiftFunctor
  triangleShiftZeroIso :=
    TraceAnalyticStableMotiveQuasicategory.triangleShiftZeroIso
  triangleShiftAddIso :=
    TraceAnalyticStableMotiveQuasicategory.triangleShiftAddIso
  rotateRotateRotateIso :=
    TraceAnalyticStableMotiveQuasicategory.rotateRotateRotateIso
  invRotateInvRotateInvRotateIso :=
    TraceAnalyticStableMotiveQuasicategory.invRotateInvRotateInvRotateIso
  identityMapTriangle :=
    TraceAnalyticStableMotiveQuasicategory.identityMapTriangle
  identityMapTriangleIso :=
    TraceAnalyticStableMotiveQuasicategory.identityMapTriangleIso
  identityMapTriangle_obj_distinguished :=
    TraceAnalyticStableMotiveQuasicategory
      .identityMapTriangle_obj_distinguished
  triangleShift_obj_distinguished :=
    TraceAnalyticStableMotiveQuasicategory
      .triangleShift_obj_distinguished
  binaryBiproductTriangle :=
    TraceAnalyticStableMotiveQuasicategory.binaryBiproductTriangle
  binaryProductTriangle :=
    TraceAnalyticStableMotiveQuasicategory.binaryProductTriangle
  binaryBiproductTriangle_distinguished :=
    TraceAnalyticStableMotiveQuasicategory
      .binaryBiproductTriangle_distinguished
  binaryProductTriangle_distinguished :=
    TraceAnalyticStableMotiveQuasicategory
      .binaryProductTriangle_distinguished
  binaryProductTriangleIsoBinaryBiproductTriangle :=
    TraceAnalyticStableMotiveQuasicategory
      .binaryProductTriangleIsoBinaryBiproductTriangle
  contractibleTriangleFunctor :=
    TraceAnalyticStableMotiveQuasicategory.contractibleTriangleFunctor
  contractibleTriangleFunctor_obj_distinguished :=
    TraceAnalyticStableMotiveQuasicategory
      .contractibleTriangleFunctor_obj_distinguished
  cofiberObject :=
    TraceAnalyticStableMotiveQuasicategory.cofiberObject
  cofiberCoconeMap :=
    TraceAnalyticStableMotiveQuasicategory.cofiberCoconeMap
  cofiberBoundary :=
    TraceAnalyticStableMotiveQuasicategory.cofiberBoundary
  cofiberTriangle :=
    TraceAnalyticStableMotiveQuasicategory.cofiberTriangle
  cofiberTriangle_distinguished :=
    TraceAnalyticStableMotiveQuasicategory.cofiberTriangle_distinguished
  rotatedCofiberTriangle :=
    TraceAnalyticStableMotiveQuasicategory.rotatedCofiberTriangle
  rotatedCofiberTriangle_distinguished :=
    TraceAnalyticStableMotiveQuasicategory
      .rotatedCofiberTriangle_distinguished
  invRotatedCofiberTriangle :=
    TraceAnalyticStableMotiveQuasicategory.invRotatedCofiberTriangle
  invRotatedCofiberTriangle_distinguished :=
    TraceAnalyticStableMotiveQuasicategory
      .invRotatedCofiberTriangle_distinguished
  fiberObject :=
    TraceAnalyticStableMotiveQuasicategory.fiberObject
  fiberMap :=
    TraceAnalyticStableMotiveQuasicategory.fiberMap
  fiberTriangle :=
    TraceAnalyticStableMotiveQuasicategory.fiberTriangle
  fiberTriangle_distinguished :=
    TraceAnalyticStableMotiveQuasicategory.fiberTriangle_distinguished
  fiberObject_eq_cofiber_shift_neg :=
    TraceAnalyticStableMotiveQuasicategory
      .fiberObject_eq_cofiber_shift_neg
  fiberMap_eq_cofiberBoundary_shift :=
    TraceAnalyticStableMotiveQuasicategory
      .fiberMap_eq_cofiberBoundary_shift
  fiberConnectingMap_eq_cofiberCocone :=
    TraceAnalyticStableMotiveQuasicategory
      .fiberConnectingMap_eq_cofiberCocone
  fiberTriangle_eq_invRotate_cofiber :=
    TraceAnalyticStableMotiveQuasicategory
      .fiberTriangle_eq_invRotate_cofiber
  distinguished_iff_of_triangleIso :=
    TraceAnalyticStableMotiveQuasicategory.distinguished_iff_of_triangleIso
  completedTriangleMap₃ :=
    TraceAnalyticStableMotiveQuasicategory.completedTriangleMap₃
  completedTriangleMap₃_mor₂ :=
    TraceAnalyticStableMotiveQuasicategory.completedTriangleMap₃_mor₂
  completedTriangleMap₃_mor₃ :=
    TraceAnalyticStableMotiveQuasicategory.completedTriangleMap₃_mor₃
  cofiberComparisonMap :=
    TraceAnalyticStableMotiveQuasicategory.cofiberComparisonMap
  cofiberComparisonMap_cocone :=
    TraceAnalyticStableMotiveQuasicategory.cofiberComparisonMap_cocone
  cofiberComparisonMap_boundary :=
    TraceAnalyticStableMotiveQuasicategory.cofiberComparisonMap_boundary
  cofiberTriangleComparisonMap :=
    TraceAnalyticStableMotiveQuasicategory.cofiberTriangleComparisonMap
  rotatedCofiberTriangleComparisonMap :=
    TraceAnalyticStableMotiveQuasicategory
      .rotatedCofiberTriangleComparisonMap
  invRotatedCofiberTriangleComparisonMap :=
    TraceAnalyticStableMotiveQuasicategory
      .invRotatedCofiberTriangleComparisonMap
  fiberTriangleComparisonMap :=
    TraceAnalyticStableMotiveQuasicategory.fiberTriangleComparisonMap
  shortComplexOfDistinguishedTriangle :=
    TraceAnalyticStableMotiveQuasicategory
      .shortComplexOfDistinguishedTriangle
  cofiberShortComplex :=
    TraceAnalyticStableMotiveQuasicategory.cofiberShortComplex
  cofiberShortComplexComparisonMap :=
    TraceAnalyticStableMotiveQuasicategory.cofiberShortComplexComparisonMap
  rotatedCofiberShortComplex :=
    TraceAnalyticStableMotiveQuasicategory.rotatedCofiberShortComplex
  invRotatedCofiberShortComplex :=
    TraceAnalyticStableMotiveQuasicategory.invRotatedCofiberShortComplex
  rotatedCofiberShortComplexComparisonMap :=
    TraceAnalyticStableMotiveQuasicategory
      .rotatedCofiberShortComplexComparisonMap
  invRotatedCofiberShortComplexComparisonMap :=
    TraceAnalyticStableMotiveQuasicategory
      .invRotatedCofiberShortComplexComparisonMap
  fiberShortComplex :=
    TraceAnalyticStableMotiveQuasicategory.fiberShortComplex
  fiberShortComplexComparisonMap :=
    TraceAnalyticStableMotiveQuasicategory.fiberShortComplexComparisonMap
  shortComplexIsoOfTriangleIso :=
    TraceAnalyticStableMotiveQuasicategory.shortComplexIsoOfTriangleIso
  coyonedaShortComplex_exact :=
    TraceAnalyticStableMotiveQuasicategory.coyonedaShortComplex_exact
  yonedaShortComplex_exact :=
    TraceAnalyticStableMotiveQuasicategory.yonedaShortComplex_exact
  cofiberCoyonedaShortComplex_exact :=
    TraceAnalyticStableMotiveQuasicategory
      .cofiberCoyonedaShortComplex_exact
  cofiberYonedaShortComplex_exact :=
    TraceAnalyticStableMotiveQuasicategory
      .cofiberYonedaShortComplex_exact
  rotatedCofiberCoyonedaShortComplex_exact :=
    TraceAnalyticStableMotiveQuasicategory
      .rotatedCofiberCoyonedaShortComplex_exact
  rotatedCofiberYonedaShortComplex_exact :=
    TraceAnalyticStableMotiveQuasicategory
      .rotatedCofiberYonedaShortComplex_exact
  invRotatedCofiberCoyonedaShortComplex_exact :=
    TraceAnalyticStableMotiveQuasicategory
      .invRotatedCofiberCoyonedaShortComplex_exact
  invRotatedCofiberYonedaShortComplex_exact :=
    TraceAnalyticStableMotiveQuasicategory
      .invRotatedCofiberYonedaShortComplex_exact
  fiberCoyonedaShortComplex_exact :=
    TraceAnalyticStableMotiveQuasicategory
      .fiberCoyonedaShortComplex_exact
  fiberYonedaShortComplex_exact :=
    TraceAnalyticStableMotiveQuasicategory
      .fiberYonedaShortComplex_exact
  binaryBiproductShortComplex :=
    TraceAnalyticStableMotiveQuasicategory.binaryBiproductShortComplex
  binaryProductShortComplex :=
    TraceAnalyticStableMotiveQuasicategory.binaryProductShortComplex
  binaryBiproductCoyonedaShortComplex_exact :=
    TraceAnalyticStableMotiveQuasicategory
      .binaryBiproductCoyonedaShortComplex_exact
  binaryBiproductYonedaShortComplex_exact :=
    TraceAnalyticStableMotiveQuasicategory
      .binaryBiproductYonedaShortComplex_exact
  binaryProductCoyonedaShortComplex_exact :=
    TraceAnalyticStableMotiveQuasicategory
      .binaryProductCoyonedaShortComplex_exact
  binaryProductYonedaShortComplex_exact :=
    TraceAnalyticStableMotiveQuasicategory
      .binaryProductYonedaShortComplex_exact
  distinguishedTriangle_mor₁_comp_mor₂ :=
    TraceAnalyticStableMotiveQuasicategory
      .distinguishedTriangle_mor₁_comp_mor₂
  distinguishedTriangle_mor₂_comp_mor₃ :=
    TraceAnalyticStableMotiveQuasicategory
      .distinguishedTriangle_mor₂_comp_mor₃
  distinguishedTriangle_mor₃_comp_shift_mor₁ :=
    TraceAnalyticStableMotiveQuasicategory
      .distinguishedTriangle_mor₃_comp_shift_mor₁
  cofiber_morphism_comp_cocone :=
    TraceAnalyticStableMotiveQuasicategory.cofiber_morphism_comp_cocone
  cofiber_cocone_comp_boundary :=
    TraceAnalyticStableMotiveQuasicategory.cofiber_cocone_comp_boundary
  cofiber_boundary_comp_shift_morphism :=
    TraceAnalyticStableMotiveQuasicategory
      .cofiber_boundary_comp_shift_morphism
  fiberMap_comp_morphism :=
    TraceAnalyticStableMotiveQuasicategory.fiberMap_comp_morphism

end AnalyticMotives
end LFunctions
end Boundary
