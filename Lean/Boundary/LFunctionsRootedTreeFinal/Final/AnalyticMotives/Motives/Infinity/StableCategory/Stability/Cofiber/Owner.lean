import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Owner

/-!
# Cofiber triangles in the analytic stable motive category

This owner file chooses the cofiber object and structure maps supplied by the
pretriangulated cofiber-triangle theorem for each morphism in the analytic
stable motive category.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The chosen cofiber object of a morphism in the analytic stable motive
category. -/
def TraceAnalyticStableMotiveQuasicategory.cofiberObject
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    StableInfinityOwner.PresentedCategory :=
  Classical.choose
    (TraceAnalyticStableMotiveQuasicategory
      .distinguishedCofiberTriangle morphism)

/-- The chosen map from the target to the cofiber object. -/
def TraceAnalyticStableMotiveQuasicategory.cofiberCoconeMap
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    target ⟶
      TraceAnalyticStableMotiveQuasicategory.cofiberObject morphism :=
  Classical.choose
    (Classical.choose_spec
      (TraceAnalyticStableMotiveQuasicategory
        .distinguishedCofiberTriangle morphism))

/-- The chosen boundary map from the cofiber object to the suspension of the
source. -/
def TraceAnalyticStableMotiveQuasicategory.cofiberBoundary
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    TraceAnalyticStableMotiveQuasicategory.cofiberObject morphism ⟶
      source⟦(1 : ℤ)⟧ :=
  Classical.choose
    (Classical.choose_spec
      (Classical.choose_spec
        (TraceAnalyticStableMotiveQuasicategory
          .distinguishedCofiberTriangle morphism)))

/-- The chosen cofiber triangle of a morphism in the analytic stable motive
category. -/
def TraceAnalyticStableMotiveQuasicategory.cofiberTriangle
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    StableInfinityOwner.PresentedTriangle :=
  Pretriangulated.Triangle.mk
    morphism
    (TraceAnalyticStableMotiveQuasicategory.cofiberCoconeMap morphism)
    (TraceAnalyticStableMotiveQuasicategory.cofiberBoundary morphism)

/-- The chosen cofiber triangle is distinguished. -/
theorem TraceAnalyticStableMotiveQuasicategory.cofiberTriangle_distinguished
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    TraceAnalyticStableMotiveQuasicategory.cofiberTriangle morphism ∈
      TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles :=
  Classical.choose_spec
    (Classical.choose_spec
      (Classical.choose_spec
        (TraceAnalyticStableMotiveQuasicategory
          .distinguishedCofiberTriangle morphism)))

/-- The chosen cofiber triangle has the original morphism as its first map. -/
theorem TraceAnalyticStableMotiveQuasicategory.cofiberTriangle_mor₁
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (TraceAnalyticStableMotiveQuasicategory
      .cofiberTriangle morphism).mor₁ =
      morphism :=
  rfl

/-- The chosen cofiber triangle has the chosen cocone map as its second map. -/
theorem TraceAnalyticStableMotiveQuasicategory.cofiberTriangle_mor₂
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (TraceAnalyticStableMotiveQuasicategory
      .cofiberTriangle morphism).mor₂ =
      TraceAnalyticStableMotiveQuasicategory.cofiberCoconeMap morphism :=
  rfl

/-- The chosen cofiber triangle has the chosen boundary map as its third map. -/
theorem TraceAnalyticStableMotiveQuasicategory.cofiberTriangle_mor₃
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (TraceAnalyticStableMotiveQuasicategory
      .cofiberTriangle morphism).mor₃ =
      TraceAnalyticStableMotiveQuasicategory.cofiberBoundary morphism :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
