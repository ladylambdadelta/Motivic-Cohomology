import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Mathlib.Assembly.Heart.Owner

/-!
# Equivalence between homological and assembled categorical hearts

This file upgrades the two heart transport functors for the assembled
orthogonality/truncation t-structure to a categorical equivalence.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

/-- Transport from the homological heart to the assembled categorical heart
and back is the identity functor. -/
theorem HomologicalHeart.toTStructureHeartFunctorOfOrthogonalityAndTruncation_comp_toHomologicalHeartFunctor
    (zeroField :
      ∀ {source target : TraceAnalyticDerivedMotiveCategory},
        ∀ (morphism : source ⟶ target),
          TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source →
            TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target →
              morphism = 0)
    (existsTriangleZeroOne :
      ∀ object : TraceAnalyticDerivedMotiveCategory,
        ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
          (_ : TraceAnalyticDerivedMotiveCategory.tStructureLE 0 lower)
          (_ : TraceAnalyticDerivedMotiveCategory.tStructureGE 1 upper)
          (firstMap : lower ⟶ object)
          (secondMap : object ⟶ upper)
          (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
          Triangle.mk firstMap secondMap connectingMap ∈
            distTriang TraceAnalyticDerivedMotiveCategory)
    (cut : ℤ) :
    TraceAnalyticDerivedMotiveCategory.HomologicalHeart.toTStructureHeartFunctorOfOrthogonalityAndTruncation
          zeroField
          existsTriangleZeroOne
          cut ⋙
      TraceAnalyticDerivedMotiveCategory.TStructureHeart.toHomologicalHeartFunctorOfOrthogonalityAndTruncation
        zeroField
        existsTriangleZeroOne
        cut =
      𝟭 (TraceAnalyticDerivedMotiveCategory.HomologicalHeart cut) :=
  rfl

/-- Transport from the assembled categorical heart to the homological heart
and back is the identity functor. -/
theorem TStructureHeart.toHomologicalHeartFunctorOfOrthogonalityAndTruncation_comp_toTStructureHeartFunctor
    (zeroField :
      ∀ {source target : TraceAnalyticDerivedMotiveCategory},
        ∀ (morphism : source ⟶ target),
          TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source →
            TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target →
              morphism = 0)
    (existsTriangleZeroOne :
      ∀ object : TraceAnalyticDerivedMotiveCategory,
        ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
          (_ : TraceAnalyticDerivedMotiveCategory.tStructureLE 0 lower)
          (_ : TraceAnalyticDerivedMotiveCategory.tStructureGE 1 upper)
          (firstMap : lower ⟶ object)
          (secondMap : object ⟶ upper)
          (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
          Triangle.mk firstMap secondMap connectingMap ∈
            distTriang TraceAnalyticDerivedMotiveCategory)
    (cut : ℤ) :
    TraceAnalyticDerivedMotiveCategory.TStructureHeart.toHomologicalHeartFunctorOfOrthogonalityAndTruncation
          zeroField
          existsTriangleZeroOne
          cut ⋙
      TraceAnalyticDerivedMotiveCategory.HomologicalHeart.toTStructureHeartFunctorOfOrthogonalityAndTruncation
        zeroField
        existsTriangleZeroOne
        cut =
      𝟭
        (TraceAnalyticDerivedMotiveCategory.TStructureHeart
          (TraceAnalyticDerivedMotiveCategory
            .tStructureOfOrthogonalityAndTruncation
              zeroField
              existsTriangleZeroOne)
          cut) :=
  rfl

/-- The equivalence between the existing homological heart and the
categorical heart of the assembled orthogonality/truncation t-structure. -/
def HomologicalHeart.equivalenceTStructureHeartOfOrthogonalityAndTruncation
    (zeroField :
      ∀ {source target : TraceAnalyticDerivedMotiveCategory},
        ∀ (morphism : source ⟶ target),
          TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source →
            TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target →
              morphism = 0)
    (existsTriangleZeroOne :
      ∀ object : TraceAnalyticDerivedMotiveCategory,
        ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
          (_ : TraceAnalyticDerivedMotiveCategory.tStructureLE 0 lower)
          (_ : TraceAnalyticDerivedMotiveCategory.tStructureGE 1 upper)
          (firstMap : lower ⟶ object)
          (secondMap : object ⟶ upper)
          (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
          Triangle.mk firstMap secondMap connectingMap ∈
            distTriang TraceAnalyticDerivedMotiveCategory)
    (cut : ℤ) :
    TraceAnalyticDerivedMotiveCategory.HomologicalHeart cut ≌
      TraceAnalyticDerivedMotiveCategory.TStructureHeart
        (TraceAnalyticDerivedMotiveCategory
          .tStructureOfOrthogonalityAndTruncation
            zeroField
            existsTriangleZeroOne)
        cut :=
  CategoryTheory.Equivalence.mk
    (TraceAnalyticDerivedMotiveCategory.HomologicalHeart.toTStructureHeartFunctorOfOrthogonalityAndTruncation
      zeroField
      existsTriangleZeroOne
      cut)
    (TraceAnalyticDerivedMotiveCategory.TStructureHeart.toHomologicalHeartFunctorOfOrthogonalityAndTruncation
      zeroField
      existsTriangleZeroOne
      cut)
    (eqToIso
      (Eq.symm
        (TraceAnalyticDerivedMotiveCategory.HomologicalHeart.toTStructureHeartFunctorOfOrthogonalityAndTruncation_comp_toHomologicalHeartFunctor
            zeroField
            existsTriangleZeroOne
            cut)))
    (eqToIso
      (TraceAnalyticDerivedMotiveCategory.TStructureHeart.toHomologicalHeartFunctorOfOrthogonalityAndTruncation_comp_toTStructureHeartFunctor
          zeroField
          existsTriangleZeroOne
          cut))

/-- The functor of the heart equivalence is the homological-to-categorical
heart transport functor. -/
theorem HomologicalHeart.equivalenceTStructureHeartOfOrthogonalityAndTruncation_functor
    (zeroField :
      ∀ {source target : TraceAnalyticDerivedMotiveCategory},
        ∀ (morphism : source ⟶ target),
          TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source →
            TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target →
              morphism = 0)
    (existsTriangleZeroOne :
      ∀ object : TraceAnalyticDerivedMotiveCategory,
        ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
          (_ : TraceAnalyticDerivedMotiveCategory.tStructureLE 0 lower)
          (_ : TraceAnalyticDerivedMotiveCategory.tStructureGE 1 upper)
          (firstMap : lower ⟶ object)
          (secondMap : object ⟶ upper)
          (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
          Triangle.mk firstMap secondMap connectingMap ∈
            distTriang TraceAnalyticDerivedMotiveCategory)
    (cut : ℤ) :
    (TraceAnalyticDerivedMotiveCategory.HomologicalHeart.equivalenceTStructureHeartOfOrthogonalityAndTruncation
        zeroField
        existsTriangleZeroOne
        cut).functor =
      TraceAnalyticDerivedMotiveCategory.HomologicalHeart.toTStructureHeartFunctorOfOrthogonalityAndTruncation
        zeroField
        existsTriangleZeroOne
        cut :=
  rfl

/-- The inverse of the heart equivalence is the categorical-to-homological
heart transport functor. -/
theorem HomologicalHeart.equivalenceTStructureHeartOfOrthogonalityAndTruncation_inverse
    (zeroField :
      ∀ {source target : TraceAnalyticDerivedMotiveCategory},
        ∀ (morphism : source ⟶ target),
          TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source →
            TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target →
              morphism = 0)
    (existsTriangleZeroOne :
      ∀ object : TraceAnalyticDerivedMotiveCategory,
        ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
          (_ : TraceAnalyticDerivedMotiveCategory.tStructureLE 0 lower)
          (_ : TraceAnalyticDerivedMotiveCategory.tStructureGE 1 upper)
          (firstMap : lower ⟶ object)
          (secondMap : object ⟶ upper)
          (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
          Triangle.mk firstMap secondMap connectingMap ∈
            distTriang TraceAnalyticDerivedMotiveCategory)
    (cut : ℤ) :
    (TraceAnalyticDerivedMotiveCategory.HomologicalHeart.equivalenceTStructureHeartOfOrthogonalityAndTruncation
        zeroField
        existsTriangleZeroOne
        cut).inverse =
      TraceAnalyticDerivedMotiveCategory.TStructureHeart.toHomologicalHeartFunctorOfOrthogonalityAndTruncation
        zeroField
        existsTriangleZeroOne
        cut :=
  rfl

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
