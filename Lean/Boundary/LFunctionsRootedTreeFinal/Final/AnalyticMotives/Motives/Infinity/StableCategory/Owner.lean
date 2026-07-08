import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.Construction.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.HomotopyCategory.Summary.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.StableInfinityStructure.Summary.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.CategoricalStrength.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Geometry.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Certificate.Summary.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Projections.Summary.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.VerdierQuotient.Preadditive.Owner

/-!
# Stable infinity category projection theorems

This file exposes projection theorems for the concrete stable-infinity package
of analytic motives.  The package structure lives in
`StableCategory/Core/Owner.lean`, and its concrete constructor lives in
`StableCategory/Core/Construction/Owner.lean`; structure and cofiber
and exact-triangle projection files keep the theorem surface below the line
cap while preserving the public import path.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory


/-- The owner-level stable infinity category has the analytic stable motive
quasicategory as its quasicategory field. -/
theorem traceAnalyticStableInfinityCategory_quasicategory :
    traceAnalyticStableInfinityCategory.quasicategory =
      TraceAnalyticStableMotiveQuasicategory.quasicategory :=
  rfl

/-- The owner-level stable infinity category localizes the additive homotopy
category at the analytic stable null morphisms. -/
theorem traceAnalyticStableInfinityCategory_localization :
    traceAnalyticStableInfinityCategory.localization =
      TraceAnalyticStableMotiveQuasicategory.isLocalization :=
  rfl

/-- The owner-level stable infinity category carries the preadditive structure
on the analytic Verdier quotient. -/
theorem traceAnalyticStableInfinityCategory_preadditive :
    traceAnalyticStableInfinityCategory.preadditive =
      TraceAnalyticStableMotiveCategory.preadditiveStructure :=
  rfl

/-- The owner-level stable infinity category carries the zero object structure
on the analytic Verdier quotient. -/
theorem traceAnalyticStableInfinityCategory_zeroObject :
    traceAnalyticStableInfinityCategory.zeroObject =
      traceAnalyticStableInfinityCategory_isPointed :=
  rfl

/-- The owner-level stable infinity category carries the Verdier quotient
integer shift structure. -/
theorem traceAnalyticStableInfinityCategory_shift :
    traceAnalyticStableInfinityCategory.shift =
      TraceAnalyticStableMotiveQuasicategory.hasShiftStructure :=
  rfl

/-- The owner-level stable infinity category records suspension as the
positive unit shift on the analytic Verdier quotient. -/
theorem traceAnalyticStableInfinityCategory_suspension :
    traceAnalyticStableInfinityCategory.suspension =
      TraceAnalyticStableMotiveQuasicategory.suspensionFunctor :=
  rfl

/-- The owner-level stable infinity category records loop as the negative unit
shift on the analytic Verdier quotient. -/
theorem traceAnalyticStableInfinityCategory_loop :
    traceAnalyticStableInfinityCategory.loop =
      TraceAnalyticStableMotiveQuasicategory.loopFunctor :=
  rfl

/-- The owner-level stable infinity category records the suspension-loop
equivalence supplied by the integer shift structure. -/
theorem traceAnalyticStableInfinityCategory_suspensionLoopEquivalence :
    traceAnalyticStableInfinityCategory.suspensionLoopEquivalence =
      TraceAnalyticStableMotiveQuasicategory.suspensionLoopEquivalence :=
  rfl

/-- The suspension field is definitionally the positive unit shift functor. -/
theorem traceAnalyticStableInfinityCategory_suspension_eq_shift :
    traceAnalyticStableInfinityCategory.suspension_eq_shift =
      rfl :=
  rfl

/-- The loop field is definitionally the negative unit shift functor. -/
theorem traceAnalyticStableInfinityCategory_loop_eq_shift :
    traceAnalyticStableInfinityCategory.loop_eq_shift =
      rfl :=
  rfl

/-- The suspension-loop equivalence field is definitionally the unit
shift-equivalence. -/
theorem
    traceAnalyticStableInfinityCategory_suspensionLoopEquivalence_eq_shiftEquiv :
    traceAnalyticStableInfinityCategory.suspensionLoopEquivalence_eq_shiftEquiv =
      rfl :=
  rfl

/-- The owner-level stable infinity category records compatibility of the
quotient functor with integer shifts. -/
theorem traceAnalyticStableInfinityCategory_quotientCommShift :
    traceAnalyticStableInfinityCategory.quotientCommShift =
      TraceAnalyticStableMotiveCategory.quotientFunctorCommShift :=
  rfl

/-- The owner-level stable infinity category carries the Verdier quotient
pretriangulated structure. -/
theorem traceAnalyticStableInfinityCategory_pretriangulated :
    traceAnalyticStableInfinityCategory.pretriangulated =
      TraceAnalyticStableMotiveQuasicategory.pretriangulatedStructure :=
  rfl

/-- The owner-level stable infinity category carries the Verdier quotient
triangulated structure. -/
theorem traceAnalyticStableInfinityCategory_triangulated :
    traceAnalyticStableInfinityCategory.triangulated =
      TraceAnalyticStableMotiveQuasicategory.triangulatedStructure :=
  rfl

/-- The owner-level stable infinity category has the stable motive
distinguished triangles. -/
theorem traceAnalyticStableInfinityCategory_distinguishedTriangles :
    traceAnalyticStableInfinityCategory.distinguishedTriangles =
      TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles :=
  rfl

/-- The distinguished-triangle field of the stable infinity category is
definitionally the stable-presentation distinguished-triangle set. -/
theorem traceAnalyticStableInfinityCategory_distinguishedTriangles_eq :
    traceAnalyticStableInfinityCategory.distinguishedTriangles_eq =
      rfl :=
  rfl

/-- Every morphism in the owner-level stable infinity category has a
distinguished cofiber triangle. -/
theorem traceAnalyticStableInfinityCategory_distinguishedCofiberTriangle
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    ∃ (cofiber : StableInfinityOwner.PresentedCategory)
      (coconeMap : target ⟶ cofiber)
      (boundary : cofiber ⟶ source⟦(1 : ℤ)⟧),
      Pretriangulated.Triangle.mk morphism coconeMap boundary ∈
        traceAnalyticStableInfinityCategory.distinguishedTriangles :=
  traceAnalyticStableInfinityCategory.distinguishedCofiberTriangle morphism

/-- The owner-level stable infinity category records that contractible
triangles are distinguished. -/
theorem
    traceAnalyticStableInfinityCategory_contractibleTriangle_distinguished
    (object : StableInfinityOwner.PresentedCategory) :
    Pretriangulated.contractibleTriangle object ∈
      traceAnalyticStableInfinityCategory.distinguishedTriangles :=
  traceAnalyticStableInfinityCategory.contractibleTriangle_distinguished object

/-- The owner-level stable infinity category records rotation closure for
distinguished triangles. -/
theorem traceAnalyticStableInfinityCategory_rotate_distinguishedTriangle
    (triangle : StableInfinityOwner.PresentedTriangle) :
    triangle ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles ↔
      triangle.rotate ∈
        traceAnalyticStableInfinityCategory.distinguishedTriangles :=
  traceAnalyticStableInfinityCategory.rotate_distinguishedTriangle triangle

/-- The owner-level stable infinity category records completion of morphisms
between distinguished triangles. -/
theorem
    traceAnalyticStableInfinityCategory_complete_distinguishedTriangleMorphism
    (first second : StableInfinityOwner.PresentedTriangle)
    (first_distinguished :
      first ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles)
    (second_distinguished :
      second ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles)
    (map₁ : first.obj₁ ⟶ second.obj₁)
    (map₂ : first.obj₂ ⟶ second.obj₂)
    (square : first.mor₁ ≫ map₂ = map₁ ≫ second.mor₁) :
    ∃ map₃ : first.obj₃ ⟶ second.obj₃,
      first.mor₂ ≫ map₃ = map₂ ≫ second.mor₂ ∧
        first.mor₃ ≫ map₁⟦(1 : ℤ)⟧' = map₃ ≫ second.mor₃ :=
  traceAnalyticStableInfinityCategory.complete_distinguishedTriangleMorphism
    first
    second
    first_distinguished
    second_distinguished
    map₁
    map₂
    square

/-- The owner-level stable infinity category records the first-vertex
projection from its triangle category. -/
theorem traceAnalyticStableInfinityCategory_triangleFirstProjection :
    traceAnalyticStableInfinityCategory.triangleFirstProjection =
      TraceAnalyticStableMotiveQuasicategory.triangleFirstProjection :=
  rfl

/-- The owner-level stable infinity category records the second-vertex
projection from its triangle category. -/
theorem traceAnalyticStableInfinityCategory_triangleSecondProjection :
    traceAnalyticStableInfinityCategory.triangleSecondProjection =
      TraceAnalyticStableMotiveQuasicategory.triangleSecondProjection :=
  rfl

/-- The owner-level stable infinity category records the third-vertex
projection from its triangle category. -/
theorem traceAnalyticStableInfinityCategory_triangleThirdProjection :
    traceAnalyticStableInfinityCategory.triangleThirdProjection =
      TraceAnalyticStableMotiveQuasicategory.triangleThirdProjection :=
  rfl

/-- The owner-level stable infinity category records the triangle-rotation
functor. -/
theorem traceAnalyticStableInfinityCategory_triangleRotateFunctor :
    traceAnalyticStableInfinityCategory.triangleRotateFunctor =
      TraceAnalyticStableMotiveQuasicategory.triangleRotateFunctor :=
  rfl

/-- The owner-level stable infinity category records the inverse
triangle-rotation functor. -/
theorem traceAnalyticStableInfinityCategory_triangleInvRotateFunctor :
    traceAnalyticStableInfinityCategory.triangleInvRotateFunctor =
      TraceAnalyticStableMotiveQuasicategory.triangleInvRotateFunctor :=
  rfl

/-- The owner-level stable infinity category records the triangle-rotation
autoequivalence. -/
theorem traceAnalyticStableInfinityCategory_triangleRotationEquivalence :
    traceAnalyticStableInfinityCategory.triangleRotationEquivalence =
      TraceAnalyticStableMotiveQuasicategory.triangleRotationEquivalence :=
  rfl

/-- The owner-level stable infinity category records the triangle-shift
functor. -/
theorem traceAnalyticStableInfinityCategory_triangleShiftFunctor
    (degree : ℤ) :
    traceAnalyticStableInfinityCategory.triangleShiftFunctor degree =
      TraceAnalyticStableMotiveQuasicategory.triangleShiftFunctor degree :=
  rfl

/-- The owner-level stable infinity category records the triangle zero-shift
isomorphism. -/
theorem traceAnalyticStableInfinityCategory_triangleShiftZeroIso :
    traceAnalyticStableInfinityCategory.triangleShiftZeroIso =
      TraceAnalyticStableMotiveQuasicategory.triangleShiftZeroIso :=
  rfl

/-- The owner-level stable infinity category records the triangle-shift
additivity isomorphism. -/
theorem traceAnalyticStableInfinityCategory_triangleShiftAddIso
    (left right total : ℤ) (sum : left + right = total) :
    traceAnalyticStableInfinityCategory.triangleShiftAddIso
        left
        right
        total
        sum =
      TraceAnalyticStableMotiveQuasicategory.triangleShiftAddIso
        left
        right
        total
        sum :=
  rfl

/-- The owner-level stable infinity category records the triple-rotation
coherence isomorphism. -/
theorem traceAnalyticStableInfinityCategory_rotateRotateRotateIso :
    traceAnalyticStableInfinityCategory.rotateRotateRotateIso =
      TraceAnalyticStableMotiveQuasicategory.rotateRotateRotateIso :=
  rfl

/-- The owner-level stable infinity category records the triple
inverse-rotation coherence isomorphism. -/
theorem
    traceAnalyticStableInfinityCategory_invRotateInvRotateInvRotateIso :
    traceAnalyticStableInfinityCategory.invRotateInvRotateInvRotateIso =
      TraceAnalyticStableMotiveQuasicategory
        .invRotateInvRotateInvRotateIso :=
  rfl

/-- The owner-level stable infinity category records the identity triangle
functor. -/
theorem traceAnalyticStableInfinityCategory_identityMapTriangle :
    traceAnalyticStableInfinityCategory.identityMapTriangle =
      TraceAnalyticStableMotiveQuasicategory.identityMapTriangle :=
  rfl

/-- The owner-level stable infinity category records the identity triangle
isomorphism. -/
theorem traceAnalyticStableInfinityCategory_identityMapTriangleIso :
    traceAnalyticStableInfinityCategory.identityMapTriangleIso =
      TraceAnalyticStableMotiveQuasicategory.identityMapTriangleIso :=
  rfl

/-- The owner-level identity triangle functor preserves distinguished
triangles. -/
theorem
    traceAnalyticStableInfinityCategory_identityMapTriangle_obj_distinguished
    (triangle : StableInfinityOwner.PresentedTriangle)
    (distinguished :
      triangle ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles) :
    traceAnalyticStableInfinityCategory.identityMapTriangle.obj triangle ∈
      traceAnalyticStableInfinityCategory.distinguishedTriangles :=
  traceAnalyticStableInfinityCategory
    .identityMapTriangle_obj_distinguished
    triangle
    distinguished

/-- Owner-level triangle shifts preserve distinguished triangles. -/
theorem traceAnalyticStableInfinityCategory_triangleShift_obj_distinguished
    (degree : ℤ)
    (triangle : StableInfinityOwner.PresentedTriangle)
    (distinguished :
      triangle ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles) :
    (traceAnalyticStableInfinityCategory
        .triangleShiftFunctor degree).obj triangle ∈
      traceAnalyticStableInfinityCategory.distinguishedTriangles :=
  traceAnalyticStableInfinityCategory
    .triangleShift_obj_distinguished
    degree
    triangle
    distinguished

/-- The owner-level stable infinity category records the
contractible-triangle functor. -/
theorem traceAnalyticStableInfinityCategory_contractibleTriangleFunctor :
    traceAnalyticStableInfinityCategory.contractibleTriangleFunctor =
      TraceAnalyticStableMotiveQuasicategory.contractibleTriangleFunctor :=
  rfl

/-- Objects in the image of the owner-level contractible-triangle functor are
distinguished triangles. -/
theorem
    traceAnalyticStableInfinityCategory_contractibleTriangleFunctor_obj_distinguished
    (object : StableInfinityOwner.PresentedCategory) :
    traceAnalyticStableInfinityCategory
        .contractibleTriangleFunctor.obj object ∈
      traceAnalyticStableInfinityCategory.distinguishedTriangles :=
  traceAnalyticStableInfinityCategory
    .contractibleTriangleFunctor_obj_distinguished
    object

/-- The owner-level stable infinity category records isomorphism-invariance
of distinguished triangles. -/
theorem traceAnalyticStableInfinityCategory_distinguished_iff_of_triangleIso
    {first second : StableInfinityOwner.PresentedTriangle}
    (iso : first ≅ second) :
    first ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles ↔
      second ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles :=
  traceAnalyticStableInfinityCategory
    .distinguished_iff_of_triangleIso
    iso

/-- The owner-level stable infinity category records the chosen third map
completing a morphism between distinguished triangles. -/
theorem traceAnalyticStableInfinityCategory_completedTriangleMap₃
    (first second : StableInfinityOwner.PresentedTriangle)
    (first_distinguished :
      first ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles)
    (second_distinguished :
      second ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles)
    (map₁ : first.obj₁ ⟶ second.obj₁)
    (map₂ : first.obj₂ ⟶ second.obj₂)
    (square : first.mor₁ ≫ map₂ = map₁ ≫ second.mor₁) :
    traceAnalyticStableInfinityCategory.completedTriangleMap₃
        first
        second
        first_distinguished
        second_distinguished
        map₁
        map₂
        square =
      TraceAnalyticStableMotiveQuasicategory.completedTriangleMap₃
        first
        second
        first_distinguished
        second_distinguished
        map₁
        map₂
        square :=
  rfl

/-- The owner-level chosen third map satisfies the second-square
compatibility. -/
theorem traceAnalyticStableInfinityCategory_completedTriangleMap₃_mor₂
    (first second : StableInfinityOwner.PresentedTriangle)
    (first_distinguished :
      first ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles)
    (second_distinguished :
      second ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles)
    (map₁ : first.obj₁ ⟶ second.obj₁)
    (map₂ : first.obj₂ ⟶ second.obj₂)
    (square : first.mor₁ ≫ map₂ = map₁ ≫ second.mor₁) :
    first.mor₂ ≫
        traceAnalyticStableInfinityCategory.completedTriangleMap₃
          first
          second
          first_distinguished
          second_distinguished
          map₁
          map₂
          square =
      map₂ ≫ second.mor₂ :=
  traceAnalyticStableInfinityCategory
    .completedTriangleMap₃_mor₂
    first
    second
    first_distinguished
    second_distinguished
    map₁
    map₂
    square

/-- The owner-level chosen third map satisfies the boundary-square
compatibility. -/
theorem traceAnalyticStableInfinityCategory_completedTriangleMap₃_mor₃
    (first second : StableInfinityOwner.PresentedTriangle)
    (first_distinguished :
      first ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles)
    (second_distinguished :
      second ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles)
    (map₁ : first.obj₁ ⟶ second.obj₁)
    (map₂ : first.obj₂ ⟶ second.obj₂)
    (square : first.mor₁ ≫ map₂ = map₁ ≫ second.mor₁) :
    first.mor₃ ≫ map₁⟦(1 : ℤ)⟧' =
      traceAnalyticStableInfinityCategory.completedTriangleMap₃
          first
          second
          first_distinguished
          second_distinguished
          map₁
          map₂
          square ≫
        second.mor₃ :=
  traceAnalyticStableInfinityCategory
    .completedTriangleMap₃_mor₃
    first
    second
    first_distinguished
    second_distinguished
    map₁
    map₂
    square

/-- The owner-level stable infinity category records the cofiber comparison
map induced by a commutative square. -/
theorem traceAnalyticStableInfinityCategory_cofiberComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.cofiberComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square =
      TraceAnalyticStableMotiveQuasicategory.cofiberComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square :=
  rfl

/-- The owner-level cofiber comparison map satisfies the cocone square. -/
theorem traceAnalyticStableInfinityCategory_cofiberComparisonMap_cocone'
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.cofiberCoconeMap morphism₁ ≫
        traceAnalyticStableInfinityCategory.cofiberComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square =
      targetMap ≫
        traceAnalyticStableInfinityCategory.cofiberCoconeMap
          morphism₂ :=
  traceAnalyticStableInfinityCategory
    .cofiberComparisonMap_cocone
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square

/-- The owner-level cofiber comparison map satisfies the boundary square. -/
theorem traceAnalyticStableInfinityCategory_cofiberComparisonMap_boundary'
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.cofiberBoundary morphism₁ ≫
        sourceMap⟦(1 : ℤ)⟧' =
      traceAnalyticStableInfinityCategory.cofiberComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square ≫
        traceAnalyticStableInfinityCategory.cofiberBoundary
          morphism₂ :=
  traceAnalyticStableInfinityCategory
    .cofiberComparisonMap_boundary
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square

/-- The owner-level stable infinity category records the cofiber triangle
comparison morphism induced by a commutative square. -/
theorem traceAnalyticStableInfinityCategory_cofiberTriangleComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.cofiberTriangleComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square =
      TraceAnalyticStableMotiveQuasicategory.cofiberTriangleComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square :=
  rfl

/-- The owner-level stable infinity category records the fiber triangle
comparison morphism induced by a commutative square. -/
theorem traceAnalyticStableInfinityCategory_fiberTriangleComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.fiberTriangleComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square =
      TraceAnalyticStableMotiveQuasicategory.fiberTriangleComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square :=
  rfl

/-- The owner-level stable infinity category records the short complex
attached to a distinguished triangle. -/
theorem
    traceAnalyticStableInfinityCategory_shortComplexOfDistinguishedTriangle
    (triangle : StableInfinityOwner.PresentedTriangle)
    (distinguished :
      triangle ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles) :
    traceAnalyticStableInfinityCategory
        .shortComplexOfDistinguishedTriangle
        triangle
        distinguished =
      TraceAnalyticStableMotiveQuasicategory
        .shortComplexOfDistinguishedTriangle
        triangle
        distinguished :=
  rfl

/-- The owner-level stable infinity category records the short complex
attached to the chosen cofiber triangle of a morphism. -/
theorem traceAnalyticStableInfinityCategory_cofiberShortComplex
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    traceAnalyticStableInfinityCategory.cofiberShortComplex morphism =
      TraceAnalyticStableMotiveQuasicategory.cofiberShortComplex
        morphism :=
  rfl

/-- The owner-level stable infinity category records the cofiber
short-complex comparison morphism induced by a commutative square. -/
theorem traceAnalyticStableInfinityCategory_cofiberShortComplexComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.cofiberShortComplexComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square =
      TraceAnalyticStableMotiveQuasicategory
        .cofiberShortComplexComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square :=
  rfl

/-- The owner-level stable infinity category records the short complex
attached to the rotated chosen cofiber triangle of a morphism. -/
theorem traceAnalyticStableInfinityCategory_rotatedCofiberShortComplex
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    traceAnalyticStableInfinityCategory.rotatedCofiberShortComplex
        morphism =
      TraceAnalyticStableMotiveQuasicategory.rotatedCofiberShortComplex
        morphism :=
  rfl

/-- The owner-level stable infinity category records the short complex
attached to the inverse-rotated chosen cofiber triangle of a morphism. -/
theorem traceAnalyticStableInfinityCategory_invRotatedCofiberShortComplex
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    traceAnalyticStableInfinityCategory.invRotatedCofiberShortComplex
        morphism =
      TraceAnalyticStableMotiveQuasicategory
        .invRotatedCofiberShortComplex morphism :=
  rfl

/-- The owner-level stable infinity category records the rotated cofiber
short-complex comparison morphism induced by a commutative square. -/
theorem
    traceAnalyticStableInfinityCategory_rotatedCofiberShortComplexComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory
        .rotatedCofiberShortComplexComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square =
      TraceAnalyticStableMotiveQuasicategory
        .rotatedCofiberShortComplexComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square :=
  rfl

/-- The owner-level stable infinity category records the inverse-rotated
cofiber short-complex comparison morphism induced by a commutative square. -/
theorem
    traceAnalyticStableInfinityCategory_invRotatedCofiberShortComplexComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory
        .invRotatedCofiberShortComplexComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square =
      TraceAnalyticStableMotiveQuasicategory
        .invRotatedCofiberShortComplexComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square :=
  rfl

/-- The owner-level stable infinity category records the short complex
attached to the chosen fiber triangle of a morphism. -/
theorem traceAnalyticStableInfinityCategory_fiberShortComplex
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    traceAnalyticStableInfinityCategory.fiberShortComplex morphism =
      TraceAnalyticStableMotiveQuasicategory.fiberShortComplex
        morphism :=
  rfl

/-- The owner-level stable infinity category records the fiber
short-complex comparison morphism induced by a commutative square. -/
theorem traceAnalyticStableInfinityCategory_fiberShortComplexComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.fiberShortComplexComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square =
      TraceAnalyticStableMotiveQuasicategory
        .fiberShortComplexComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square :=
  rfl

/-- The owner-level stable infinity category records the isomorphism between
short complexes attached to isomorphic distinguished triangles. -/
theorem traceAnalyticStableInfinityCategory_shortComplexIsoOfTriangleIso
    {first second : StableInfinityOwner.PresentedTriangle}
    (triangleIso : first ≅ second)
    (first_distinguished :
      first ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles) :
    traceAnalyticStableInfinityCategory.shortComplexIsoOfTriangleIso
        triangleIso
        first_distinguished =
      TraceAnalyticStableMotiveQuasicategory.shortComplexIsoOfTriangleIso
        triangleIso
        first_distinguished :=
  rfl

/-- In an owner-level distinguished analytic stable triangle, the first two
maps compose to zero. -/
theorem traceAnalyticStableInfinityCategory_distinguishedTriangle_mor₁_comp_mor₂
    (triangle : StableInfinityOwner.PresentedTriangle)
    (distinguished :
      triangle ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles) :
    triangle.mor₁ ≫ triangle.mor₂ = 0 :=
  traceAnalyticStableInfinityCategory
    .distinguishedTriangle_mor₁_comp_mor₂ triangle distinguished

/-- In an owner-level distinguished analytic stable triangle, the second and
third maps compose to zero. -/
theorem traceAnalyticStableInfinityCategory_distinguishedTriangle_mor₂_comp_mor₃
    (triangle : StableInfinityOwner.PresentedTriangle)
    (distinguished :
      triangle ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles) :
    triangle.mor₂ ≫ triangle.mor₃ = 0 :=
  traceAnalyticStableInfinityCategory
    .distinguishedTriangle_mor₂_comp_mor₃ triangle distinguished

/-- In an owner-level distinguished analytic stable triangle, the third map
followed by the shifted first map is zero. -/
theorem
    traceAnalyticStableInfinityCategory_distinguishedTriangle_mor₃_comp_shift_mor₁
    (triangle : StableInfinityOwner.PresentedTriangle)
    (distinguished :
      triangle ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles) :
    triangle.mor₃ ≫ triangle.mor₁⟦(1 : ℤ)⟧' = 0 :=
  traceAnalyticStableInfinityCategory
    .distinguishedTriangle_mor₃_comp_shift_mor₁ triangle distinguished

/-- In the owner-level chosen cofiber triangle, the original morphism
followed by the chosen cocone map is zero. -/
theorem traceAnalyticStableInfinityCategory_cofiber_morphism_comp_cocone
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    morphism ≫
        traceAnalyticStableInfinityCategory.cofiberCoconeMap morphism =
      0 :=
  traceAnalyticStableInfinityCategory
    .cofiber_morphism_comp_cocone morphism

/-- In the owner-level chosen cofiber triangle, the chosen cocone map
followed by the chosen boundary map is zero. -/
theorem traceAnalyticStableInfinityCategory_cofiber_cocone_comp_boundary
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    traceAnalyticStableInfinityCategory.cofiberCoconeMap morphism ≫
        traceAnalyticStableInfinityCategory.cofiberBoundary morphism =
      0 :=
  traceAnalyticStableInfinityCategory
    .cofiber_cocone_comp_boundary morphism

/-- In the owner-level chosen cofiber triangle, the chosen boundary map
followed by the shifted original morphism is zero. -/
theorem
    traceAnalyticStableInfinityCategory_cofiber_boundary_comp_shift_morphism
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    traceAnalyticStableInfinityCategory.cofiberBoundary morphism ≫
        morphism⟦(1 : ℤ)⟧' =
      0 :=
  traceAnalyticStableInfinityCategory
    .cofiber_boundary_comp_shift_morphism morphism

end AnalyticMotives
end LFunctions
end Boundary
