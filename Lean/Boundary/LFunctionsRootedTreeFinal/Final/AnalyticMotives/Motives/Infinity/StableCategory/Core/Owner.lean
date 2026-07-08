import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Geometry.Contractible.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Geometry.Biproduct.YonedaExact.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Geometry.ExactFunctor.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Completion.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Cofiber.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Cofiber.Comparison.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Cofiber.Comparison.Rotation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Cofiber.Comparison.Triangle.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Cofiber.InvRotation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Cofiber.Rotation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Fiber.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Fiber.Comparison.Triangle.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.FiberCofiber.Duality.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Isomorphism.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.Cofiber.Comparison.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.CofiberRotations.Comparison.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.CofiberRotations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.Fiber.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.Fiber.Comparison.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.Isomorphism.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.YonedaExact.CofiberRotations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.YonedaExact.Fiber.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.YonedaExact.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.ZeroComposition.Owner

/-!
# The stable infinity category of analytic motives

This file owns the concrete stable-infinity package for analytic motives in
the current formalization.  The package is not downstream comparison data: it
collects the quasicategory, its Verdier-localized presented category, the
localization universal property, shifts, pretriangulated and triangulated
structures, distinguished triangles, and the quotient-shift compatibility in
one owner-level object.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Concrete stable-infinity structure carried by the analytic motive
quasicategory.  Every field is tied to the already constructed Verdier
localization of analytic additive homotopy motives. -/
structure TraceAnalyticStableInfinityCategory where
  quasicategory :
    Quasicategory TraceAnalyticStableMotiveQuasicategory
  localization :
    TraceAnalyticStableMotiveQuasicategory.quotientFunctor.IsLocalization
      TraceAnalyticStableMotiveQuasicategory.invertedMorphisms
  preadditive :
    Preadditive StableInfinityOwner.PresentedCategory
  zeroObject :
    HasZeroObject StableInfinityOwner.PresentedCategory
  shift :
    HasShift StableInfinityOwner.PresentedCategory ℤ
  suspension :
    StableInfinityOwner.PresentedCategory ⥤
      StableInfinityOwner.PresentedCategory
  loop :
    StableInfinityOwner.PresentedCategory ⥤
      StableInfinityOwner.PresentedCategory
  suspensionLoopEquivalence :
    StableInfinityOwner.PresentedCategory ≌
      StableInfinityOwner.PresentedCategory
  suspension_eq_shift :
    suspension =
      shiftFunctor StableInfinityOwner.PresentedCategory (1 : ℤ)
  loop_eq_shift :
    loop =
      shiftFunctor StableInfinityOwner.PresentedCategory (-1 : ℤ)
  suspensionLoopEquivalence_eq_shiftEquiv :
    suspensionLoopEquivalence =
      shiftEquiv StableInfinityOwner.PresentedCategory (1 : ℤ)
  quotientCommShift :
    TraceAnalyticStableMotiveQuasicategory.quotientFunctor.CommShift ℤ
  pretriangulated :
    Pretriangulated StableInfinityOwner.PresentedCategory
  triangulated :
    IsTriangulated StableInfinityOwner.PresentedCategory
  distinguishedTriangles :
    Set StableInfinityOwner.PresentedTriangle
  distinguishedTriangles_eq :
    distinguishedTriangles =
      TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles
  distinguishedCofiberTriangle :
    ∀ {source target : StableInfinityOwner.PresentedCategory}
      (morphism : source ⟶ target),
      ∃ (cofiber : StableInfinityOwner.PresentedCategory)
        (coconeMap : target ⟶ cofiber)
        (boundary : cofiber ⟶ source⟦(1 : ℤ)⟧),
        Pretriangulated.Triangle.mk morphism coconeMap boundary ∈
          distinguishedTriangles
  contractibleTriangle_distinguished :
    ∀ object : StableInfinityOwner.PresentedCategory,
      Pretriangulated.contractibleTriangle object ∈
        distinguishedTriangles
  rotate_distinguishedTriangle :
    ∀ triangle : StableInfinityOwner.PresentedTriangle,
      triangle ∈ distinguishedTriangles ↔
        triangle.rotate ∈ distinguishedTriangles
  complete_distinguishedTriangleMorphism :
    ∀ (first second : StableInfinityOwner.PresentedTriangle)
      (_ : first ∈ distinguishedTriangles)
      (_ : second ∈ distinguishedTriangles)
      (map₁ : first.obj₁ ⟶ second.obj₁)
      (map₂ : first.obj₂ ⟶ second.obj₂)
      (_ : first.mor₁ ≫ map₂ = map₁ ≫ second.mor₁),
      ∃ map₃ : first.obj₃ ⟶ second.obj₃,
        first.mor₂ ≫ map₃ = map₂ ≫ second.mor₂ ∧
          first.mor₃ ≫ map₁⟦(1 : ℤ)⟧' = map₃ ≫ second.mor₃
  triangleFirstProjection :
    TraceAnalyticStableMotiveQuasicategory.triangleCategory ⥤
      StableInfinityOwner.PresentedCategory
  triangleSecondProjection :
    TraceAnalyticStableMotiveQuasicategory.triangleCategory ⥤
      StableInfinityOwner.PresentedCategory
  triangleThirdProjection :
    TraceAnalyticStableMotiveQuasicategory.triangleCategory ⥤
      StableInfinityOwner.PresentedCategory
  triangleRotateFunctor :
    TraceAnalyticStableMotiveQuasicategory.triangleCategory ⥤
      TraceAnalyticStableMotiveQuasicategory.triangleCategory
  triangleInvRotateFunctor :
    TraceAnalyticStableMotiveQuasicategory.triangleCategory ⥤
      TraceAnalyticStableMotiveQuasicategory.triangleCategory
  triangleRotationEquivalence :
    TraceAnalyticStableMotiveQuasicategory.triangleCategory ≌
      TraceAnalyticStableMotiveQuasicategory.triangleCategory
  triangleShiftFunctor :
    ℤ →
      TraceAnalyticStableMotiveQuasicategory.triangleCategory ⥤
        TraceAnalyticStableMotiveQuasicategory.triangleCategory
  triangleShiftZeroIso :
    triangleShiftFunctor 0 ≅
      𝟭 TraceAnalyticStableMotiveQuasicategory.triangleCategory
  triangleShiftAddIso :
    ∀ (left right total : ℤ) (_ : left + right = total),
      triangleShiftFunctor total ≅
        triangleShiftFunctor left ⋙ triangleShiftFunctor right
  rotateRotateRotateIso :
    triangleRotateFunctor ⋙ triangleRotateFunctor ⋙
        triangleRotateFunctor ≅
      triangleShiftFunctor 1
  invRotateInvRotateInvRotateIso :
    triangleInvRotateFunctor ⋙ triangleInvRotateFunctor ⋙
        triangleInvRotateFunctor ≅
      triangleShiftFunctor (-1)
  identityMapTriangle :
    TraceAnalyticStableMotiveQuasicategory.triangleCategory ⥤
      TraceAnalyticStableMotiveQuasicategory.triangleCategory
  identityMapTriangleIso :
    identityMapTriangle ≅
      𝟭 TraceAnalyticStableMotiveQuasicategory.triangleCategory
  identityMapTriangle_obj_distinguished :
    ∀ (triangle : StableInfinityOwner.PresentedTriangle),
      triangle ∈ distinguishedTriangles →
        identityMapTriangle.obj triangle ∈ distinguishedTriangles
  triangleShift_obj_distinguished :
    ∀ (degree : ℤ) (triangle : StableInfinityOwner.PresentedTriangle),
      triangle ∈ distinguishedTriangles →
        (triangleShiftFunctor degree).obj triangle ∈ distinguishedTriangles
  binaryBiproductTriangle :
    StableInfinityOwner.PresentedCategory →
      StableInfinityOwner.PresentedCategory →
        StableInfinityOwner.PresentedTriangle
  binaryProductTriangle :
    StableInfinityOwner.PresentedCategory →
      StableInfinityOwner.PresentedCategory →
        StableInfinityOwner.PresentedTriangle
  binaryBiproductTriangle_distinguished :
    ∀ (left right : StableInfinityOwner.PresentedCategory),
      binaryBiproductTriangle left right ∈ distinguishedTriangles
  binaryProductTriangle_distinguished :
    ∀ (left right : StableInfinityOwner.PresentedCategory),
      binaryProductTriangle left right ∈ distinguishedTriangles
  binaryProductTriangleIsoBinaryBiproductTriangle :
    ∀ (left right : StableInfinityOwner.PresentedCategory),
      binaryProductTriangle left right ≅
        binaryBiproductTriangle left right
  contractibleTriangleFunctor :
    StableInfinityOwner.PresentedCategory ⥤
      TraceAnalyticStableMotiveQuasicategory.triangleCategory
  contractibleTriangleFunctor_obj_distinguished :
    ∀ object : StableInfinityOwner.PresentedCategory,
      contractibleTriangleFunctor.obj object ∈
        distinguishedTriangles
  cofiberObject :
    ∀ {source target : StableInfinityOwner.PresentedCategory},
      (source ⟶ target) → StableInfinityOwner.PresentedCategory
  cofiberCoconeMap :
    ∀ {source target : StableInfinityOwner.PresentedCategory}
      (morphism : source ⟶ target),
      target ⟶ cofiberObject morphism
  cofiberBoundary :
    ∀ {source target : StableInfinityOwner.PresentedCategory}
      (morphism : source ⟶ target),
      cofiberObject morphism ⟶ source⟦(1 : ℤ)⟧
  cofiberTriangle :
    ∀ {source target : StableInfinityOwner.PresentedCategory},
      (source ⟶ target) → StableInfinityOwner.PresentedTriangle
  cofiberTriangle_distinguished :
    ∀ {source target : StableInfinityOwner.PresentedCategory}
      (morphism : source ⟶ target),
      cofiberTriangle morphism ∈ distinguishedTriangles
  rotatedCofiberTriangle :
    ∀ {source target : StableInfinityOwner.PresentedCategory},
      (source ⟶ target) → StableInfinityOwner.PresentedTriangle
  rotatedCofiberTriangle_distinguished :
    ∀ {source target : StableInfinityOwner.PresentedCategory}
      (morphism : source ⟶ target),
      rotatedCofiberTriangle morphism ∈ distinguishedTriangles
  invRotatedCofiberTriangle :
    ∀ {source target : StableInfinityOwner.PresentedCategory},
      (source ⟶ target) → StableInfinityOwner.PresentedTriangle
  invRotatedCofiberTriangle_distinguished :
    ∀ {source target : StableInfinityOwner.PresentedCategory}
      (morphism : source ⟶ target),
      invRotatedCofiberTriangle morphism ∈ distinguishedTriangles
  fiberObject :
    ∀ {source target : StableInfinityOwner.PresentedCategory},
      (source ⟶ target) → StableInfinityOwner.PresentedCategory
  fiberMap :
    ∀ {source target : StableInfinityOwner.PresentedCategory}
      (morphism : source ⟶ target),
      fiberObject morphism ⟶ source
  fiberTriangle :
    ∀ {source target : StableInfinityOwner.PresentedCategory},
      (source ⟶ target) → StableInfinityOwner.PresentedTriangle
  fiberTriangle_distinguished :
    ∀ {source target : StableInfinityOwner.PresentedCategory}
      (morphism : source ⟶ target),
      fiberTriangle morphism ∈ distinguishedTriangles
  fiberObject_eq_cofiber_shift_neg :
    ∀ {source target : StableInfinityOwner.PresentedCategory}
      (morphism : source ⟶ target),
      fiberObject morphism =
        (cofiberObject morphism)⟦(-1 : ℤ)⟧
  fiberMap_eq_cofiberBoundary_shift :
    ∀ {source target : StableInfinityOwner.PresentedCategory}
      (morphism : source ⟶ target),
      fiberMap morphism =
        -((cofiberBoundary morphism)⟦(-1 : ℤ)⟧') ≫
          (shiftEquiv StableInfinityOwner.PresentedCategory
            (1 : ℤ)).unitIso.inv.app _
  fiberConnectingMap_eq_cofiberCocone :
    ∀ {source target : StableInfinityOwner.PresentedCategory}
      (morphism : source ⟶ target),
      (fiberTriangle morphism).mor₃ =
        cofiberCoconeMap morphism ≫
          (shiftEquiv StableInfinityOwner.PresentedCategory
            (1 : ℤ)).counitIso.inv.app _
  fiberTriangle_eq_invRotate_cofiber :
    ∀ {source target : StableInfinityOwner.PresentedCategory}
      (morphism : source ⟶ target),
      fiberTriangle morphism =
        (cofiberTriangle morphism).invRotate
  distinguished_iff_of_triangleIso :
    ∀ {first second : StableInfinityOwner.PresentedTriangle},
      (first ≅ second) →
        (first ∈ distinguishedTriangles ↔
          second ∈ distinguishedTriangles)
  completedTriangleMap₃ :
    ∀ (first second : StableInfinityOwner.PresentedTriangle)
      (_ : first ∈ distinguishedTriangles)
      (_ : second ∈ distinguishedTriangles)
      (map₁ : first.obj₁ ⟶ second.obj₁)
      (map₂ : first.obj₂ ⟶ second.obj₂)
      (_ : first.mor₁ ≫ map₂ = map₁ ≫ second.mor₁),
      first.obj₃ ⟶ second.obj₃
  completedTriangleMap₃_mor₂ :
    ∀ (first second : StableInfinityOwner.PresentedTriangle)
      (first_distinguished : first ∈ distinguishedTriangles)
      (second_distinguished : second ∈ distinguishedTriangles)
      (map₁ : first.obj₁ ⟶ second.obj₁)
      (map₂ : first.obj₂ ⟶ second.obj₂)
      (square : first.mor₁ ≫ map₂ = map₁ ≫ second.mor₁),
      first.mor₂ ≫
          completedTriangleMap₃
            first
            second
            first_distinguished
            second_distinguished
            map₁
            map₂
            square =
        map₂ ≫ second.mor₂
  completedTriangleMap₃_mor₃ :
    ∀ (first second : StableInfinityOwner.PresentedTriangle)
      (first_distinguished : first ∈ distinguishedTriangles)
      (second_distinguished : second ∈ distinguishedTriangles)
      (map₁ : first.obj₁ ⟶ second.obj₁)
      (map₂ : first.obj₂ ⟶ second.obj₂)
      (square : first.mor₁ ≫ map₂ = map₁ ≫ second.mor₁),
      first.mor₃ ≫ map₁⟦(1 : ℤ)⟧' =
        completedTriangleMap₃
            first
            second
            first_distinguished
            second_distinguished
            map₁
            map₂
            square ≫
          second.mor₃
  cofiberComparisonMap :
    ∀ {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
      (morphism₁ : source₁ ⟶ target₁)
      (morphism₂ : source₂ ⟶ target₂)
      (sourceMap : source₁ ⟶ source₂)
      (targetMap : target₁ ⟶ target₂)
      (_ : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂),
      cofiberObject morphism₁ ⟶ cofiberObject morphism₂
  cofiberComparisonMap_cocone :
    ∀ {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
      (morphism₁ : source₁ ⟶ target₁)
      (morphism₂ : source₂ ⟶ target₂)
      (sourceMap : source₁ ⟶ source₂)
      (targetMap : target₁ ⟶ target₂)
      (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂),
      cofiberCoconeMap morphism₁ ≫
          cofiberComparisonMap
            morphism₁
            morphism₂
            sourceMap
            targetMap
            square =
        targetMap ≫ cofiberCoconeMap morphism₂
  cofiberComparisonMap_boundary :
    ∀ {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
      (morphism₁ : source₁ ⟶ target₁)
      (morphism₂ : source₂ ⟶ target₂)
      (sourceMap : source₁ ⟶ source₂)
      (targetMap : target₁ ⟶ target₂)
      (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂),
      cofiberBoundary morphism₁ ≫ sourceMap⟦(1 : ℤ)⟧' =
        cofiberComparisonMap
            morphism₁
            morphism₂
            sourceMap
            targetMap
            square ≫
          cofiberBoundary morphism₂
  cofiberTriangleComparisonMap :
    ∀ {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
      (morphism₁ : source₁ ⟶ target₁)
      (morphism₂ : source₂ ⟶ target₂)
      (sourceMap : source₁ ⟶ source₂)
      (targetMap : target₁ ⟶ target₂)
      (_ : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂),
      cofiberTriangle morphism₁ ⟶ cofiberTriangle morphism₂
  rotatedCofiberTriangleComparisonMap :
    ∀ {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
      (morphism₁ : source₁ ⟶ target₁)
      (morphism₂ : source₂ ⟶ target₂)
      (sourceMap : source₁ ⟶ source₂)
      (targetMap : target₁ ⟶ target₂)
      (_ : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂),
      rotatedCofiberTriangle morphism₁ ⟶
        rotatedCofiberTriangle morphism₂
  invRotatedCofiberTriangleComparisonMap :
    ∀ {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
      (morphism₁ : source₁ ⟶ target₁)
      (morphism₂ : source₂ ⟶ target₂)
      (sourceMap : source₁ ⟶ source₂)
      (targetMap : target₁ ⟶ target₂)
      (_ : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂),
      invRotatedCofiberTriangle morphism₁ ⟶
        invRotatedCofiberTriangle morphism₂
  fiberTriangleComparisonMap :
    ∀ {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
      (morphism₁ : source₁ ⟶ target₁)
      (morphism₂ : source₂ ⟶ target₂)
      (sourceMap : source₁ ⟶ source₂)
      (targetMap : target₁ ⟶ target₂)
      (_ : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂),
      fiberTriangle morphism₁ ⟶ fiberTriangle morphism₂
  shortComplexOfDistinguishedTriangle :
    ∀ (triangle : StableInfinityOwner.PresentedTriangle),
      triangle ∈ distinguishedTriangles →
        ShortComplex StableInfinityOwner.PresentedCategory
  cofiberShortComplex :
    ∀ {source target : StableInfinityOwner.PresentedCategory},
      (source ⟶ target) →
        ShortComplex StableInfinityOwner.PresentedCategory
  cofiberShortComplexComparisonMap :
    ∀ {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
      (morphism₁ : source₁ ⟶ target₁)
      (morphism₂ : source₂ ⟶ target₂)
      (sourceMap : source₁ ⟶ source₂)
      (targetMap : target₁ ⟶ target₂)
      (_ : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂),
      cofiberShortComplex morphism₁ ⟶ cofiberShortComplex morphism₂
  rotatedCofiberShortComplex :
    ∀ {source target : StableInfinityOwner.PresentedCategory},
      (source ⟶ target) →
        ShortComplex StableInfinityOwner.PresentedCategory
  invRotatedCofiberShortComplex :
    ∀ {source target : StableInfinityOwner.PresentedCategory},
      (source ⟶ target) →
        ShortComplex StableInfinityOwner.PresentedCategory
  rotatedCofiberShortComplexComparisonMap :
    ∀ {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
      (morphism₁ : source₁ ⟶ target₁)
      (morphism₂ : source₂ ⟶ target₂)
      (sourceMap : source₁ ⟶ source₂)
      (targetMap : target₁ ⟶ target₂)
      (_ : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂),
      rotatedCofiberShortComplex morphism₁ ⟶
        rotatedCofiberShortComplex morphism₂
  invRotatedCofiberShortComplexComparisonMap :
    ∀ {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
      (morphism₁ : source₁ ⟶ target₁)
      (morphism₂ : source₂ ⟶ target₂)
      (sourceMap : source₁ ⟶ source₂)
      (targetMap : target₁ ⟶ target₂)
      (_ : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂),
      invRotatedCofiberShortComplex morphism₁ ⟶
        invRotatedCofiberShortComplex morphism₂
  fiberShortComplex :
    ∀ {source target : StableInfinityOwner.PresentedCategory},
      (source ⟶ target) →
        ShortComplex StableInfinityOwner.PresentedCategory
  fiberShortComplexComparisonMap :
    ∀ {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
      (morphism₁ : source₁ ⟶ target₁)
      (morphism₂ : source₂ ⟶ target₂)
      (sourceMap : source₁ ⟶ source₂)
      (targetMap : target₁ ⟶ target₂)
      (_ : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂),
      fiberShortComplex morphism₁ ⟶ fiberShortComplex morphism₂
  shortComplexIsoOfTriangleIso :
    ∀ {first second : StableInfinityOwner.PresentedTriangle}
      (triangleIso : first ≅ second)
      (first_distinguished : first ∈ distinguishedTriangles),
      shortComplexOfDistinguishedTriangle first first_distinguished ≅
        shortComplexOfDistinguishedTriangle
          second
          ((distinguished_iff_of_triangleIso triangleIso).1
            first_distinguished)
  coyonedaShortComplex_exact :
    ∀ (triangle : StableInfinityOwner.PresentedTriangle)
      (distinguished : triangle ∈ distinguishedTriangles)
      (probe : StableInfinityOwner.PresentedCategoryᵒᵖ),
      ((shortComplexOfDistinguishedTriangle
        triangle
        distinguished).map
          (preadditiveCoyoneda.obj probe)).Exact
  yonedaShortComplex_exact :
    ∀ (triangle : StableInfinityOwner.PresentedTriangle)
      (distinguished : triangle ∈ distinguishedTriangles)
      (probe : StableInfinityOwner.PresentedCategory),
      ((shortComplexOfDistinguishedTriangle
        triangle
        distinguished).op.map
          (preadditiveYoneda.obj probe)).Exact
  cofiberCoyonedaShortComplex_exact :
    ∀ {source target : StableInfinityOwner.PresentedCategory}
      (morphism : source ⟶ target)
      (probe : StableInfinityOwner.PresentedCategoryᵒᵖ),
      ((cofiberShortComplex morphism).map
        (preadditiveCoyoneda.obj probe)).Exact
  cofiberYonedaShortComplex_exact :
    ∀ {source target : StableInfinityOwner.PresentedCategory}
      (morphism : source ⟶ target)
      (probe : StableInfinityOwner.PresentedCategory),
      ((cofiberShortComplex morphism).op.map
        (preadditiveYoneda.obj probe)).Exact
  rotatedCofiberCoyonedaShortComplex_exact :
    ∀ {source target : StableInfinityOwner.PresentedCategory}
      (morphism : source ⟶ target)
      (probe : StableInfinityOwner.PresentedCategoryᵒᵖ),
      ((rotatedCofiberShortComplex morphism).map
        (preadditiveCoyoneda.obj probe)).Exact
  rotatedCofiberYonedaShortComplex_exact :
    ∀ {source target : StableInfinityOwner.PresentedCategory}
      (morphism : source ⟶ target)
      (probe : StableInfinityOwner.PresentedCategory),
      ((rotatedCofiberShortComplex morphism).op.map
        (preadditiveYoneda.obj probe)).Exact
  invRotatedCofiberCoyonedaShortComplex_exact :
    ∀ {source target : StableInfinityOwner.PresentedCategory}
      (morphism : source ⟶ target)
      (probe : StableInfinityOwner.PresentedCategoryᵒᵖ),
      ((invRotatedCofiberShortComplex morphism).map
        (preadditiveCoyoneda.obj probe)).Exact
  invRotatedCofiberYonedaShortComplex_exact :
    ∀ {source target : StableInfinityOwner.PresentedCategory}
      (morphism : source ⟶ target)
      (probe : StableInfinityOwner.PresentedCategory),
      ((invRotatedCofiberShortComplex morphism).op.map
        (preadditiveYoneda.obj probe)).Exact
  fiberCoyonedaShortComplex_exact :
    ∀ {source target : StableInfinityOwner.PresentedCategory}
      (morphism : source ⟶ target)
      (probe : StableInfinityOwner.PresentedCategoryᵒᵖ),
      ((fiberShortComplex morphism).map
        (preadditiveCoyoneda.obj probe)).Exact
  fiberYonedaShortComplex_exact :
    ∀ {source target : StableInfinityOwner.PresentedCategory}
      (morphism : source ⟶ target)
      (probe : StableInfinityOwner.PresentedCategory),
      ((fiberShortComplex morphism).op.map
        (preadditiveYoneda.obj probe)).Exact
  binaryBiproductShortComplex :
    StableInfinityOwner.PresentedCategory →
      StableInfinityOwner.PresentedCategory →
        ShortComplex StableInfinityOwner.PresentedCategory
  binaryProductShortComplex :
    StableInfinityOwner.PresentedCategory →
      StableInfinityOwner.PresentedCategory →
        ShortComplex StableInfinityOwner.PresentedCategory
  binaryBiproductCoyonedaShortComplex_exact :
    ∀ (left right : StableInfinityOwner.PresentedCategory)
      (probe : StableInfinityOwner.PresentedCategoryᵒᵖ),
      ((binaryBiproductShortComplex left right).map
          (preadditiveCoyoneda.obj probe)).Exact
  binaryBiproductYonedaShortComplex_exact :
    ∀ (left right : StableInfinityOwner.PresentedCategory)
      (probe : StableInfinityOwner.PresentedCategory),
      ((binaryBiproductShortComplex left right).op.map
          (preadditiveYoneda.obj probe)).Exact
  binaryProductCoyonedaShortComplex_exact :
    ∀ (left right : StableInfinityOwner.PresentedCategory)
      (probe : StableInfinityOwner.PresentedCategoryᵒᵖ),
      ((binaryProductShortComplex left right).map
          (preadditiveCoyoneda.obj probe)).Exact
  binaryProductYonedaShortComplex_exact :
    ∀ (left right : StableInfinityOwner.PresentedCategory)
      (probe : StableInfinityOwner.PresentedCategory),
      ((binaryProductShortComplex left right).op.map
          (preadditiveYoneda.obj probe)).Exact
  distinguishedTriangle_mor₁_comp_mor₂ :
    ∀ (triangle : StableInfinityOwner.PresentedTriangle),
      triangle ∈ distinguishedTriangles →
        triangle.mor₁ ≫ triangle.mor₂ = 0
  distinguishedTriangle_mor₂_comp_mor₃ :
    ∀ (triangle : StableInfinityOwner.PresentedTriangle),
      triangle ∈ distinguishedTriangles →
        triangle.mor₂ ≫ triangle.mor₃ = 0
  distinguishedTriangle_mor₃_comp_shift_mor₁ :
    ∀ (triangle : StableInfinityOwner.PresentedTriangle),
      triangle ∈ distinguishedTriangles →
        triangle.mor₃ ≫ triangle.mor₁⟦(1 : ℤ)⟧' = 0
  cofiber_morphism_comp_cocone :
    ∀ {source target : StableInfinityOwner.PresentedCategory}
      (morphism : source ⟶ target),
      morphism ≫ cofiberCoconeMap morphism = 0
  cofiber_cocone_comp_boundary :
    ∀ {source target : StableInfinityOwner.PresentedCategory}
      (morphism : source ⟶ target),
      cofiberCoconeMap morphism ≫ cofiberBoundary morphism = 0
  cofiber_boundary_comp_shift_morphism :
    ∀ {source target : StableInfinityOwner.PresentedCategory}
      (morphism : source ⟶ target),
      cofiberBoundary morphism ≫ morphism⟦(1 : ℤ)⟧' = 0
  fiberMap_comp_morphism :
    ∀ {source target : StableInfinityOwner.PresentedCategory}
      (morphism : source ⟶ target),
      fiberMap morphism ≫ morphism = 0

end AnalyticMotives
end LFunctions
end Boundary
