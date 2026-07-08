import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Aisles.Subcategories.Owner

/-!
# Monotone inclusions between analytic motivic aisle subcategories

This file upgrades cut monotonicity of concrete aisle and coaisle predicates to
functors between the corresponding full subcategories.
-/

noncomputable section

open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Enlarging the cut gives a functor from the lower aisle into the upper
aisle. -/
abbrev TraceAnalyticMotivicTStructure.Aisle.inclusionOfLE
    {lower upper : ℤ}
    (cut_le : lower ≤ upper) :
    TraceAnalyticMotivicTStructure.Aisle lower ⥤
      TraceAnalyticMotivicTStructure.Aisle upper :=
  CategoryTheory.FullSubcategory.lift
    (TraceAnalyticMotivicTStructure.aisleLE upper)
    (TraceAnalyticMotivicTStructure.Aisle.inclusion lower)
    (fun object =>
      TraceAnalyticMotivicTStructure.aisleLE_mono
        cut_le
        object.property)

/-- Lowering the cut gives a functor from the upper coaisle into the lower
coaisle. -/
abbrev TraceAnalyticMotivicTStructure.Coaisle.inclusionOfLE
    {lower upper : ℤ}
    (cut_le : lower ≤ upper) :
    TraceAnalyticMotivicTStructure.Coaisle upper ⥤
      TraceAnalyticMotivicTStructure.Coaisle lower :=
  CategoryTheory.FullSubcategory.lift
    (TraceAnalyticMotivicTStructure.coaisleGE lower)
    (TraceAnalyticMotivicTStructure.Coaisle.inclusion upper)
    (fun object =>
      TraceAnalyticMotivicTStructure.coaisleGE_mono
        cut_le
        object.property)

/-- The monotone aisle inclusion preserves the ambient object. -/
theorem TraceAnalyticMotivicTStructure.Aisle.inclusionOfLE_obj
    {lower upper : ℤ}
    (cut_le : lower ≤ upper)
    (object : TraceAnalyticMotivicTStructure.Aisle lower) :
    (TraceAnalyticMotivicTStructure.Aisle.inclusionOfLE cut_le).obj object =
      ⟨
        object.object,
        TraceAnalyticMotivicTStructure.aisleLE_mono
          cut_le
          object.property
      ⟩ :=
  rfl

/-- The monotone coaisle inclusion preserves the ambient object. -/
theorem TraceAnalyticMotivicTStructure.Coaisle.inclusionOfLE_obj
    {lower upper : ℤ}
    (cut_le : lower ≤ upper)
    (object : TraceAnalyticMotivicTStructure.Coaisle upper) :
    (TraceAnalyticMotivicTStructure.Coaisle.inclusionOfLE cut_le).obj object =
      ⟨
        object.object,
        TraceAnalyticMotivicTStructure.coaisleGE_mono
          cut_le
          object.property
      ⟩ :=
  rfl

/-- Monotone aisle inclusion followed by ambient inclusion is the lower aisle
ambient inclusion. -/
theorem TraceAnalyticMotivicTStructure.Aisle.inclusionOfLE_comp_inclusion
    {lower upper : ℤ}
    (cut_le : lower ≤ upper) :
    TraceAnalyticMotivicTStructure.Aisle.inclusionOfLE cut_le ⋙
        TraceAnalyticMotivicTStructure.Aisle.inclusion upper =
      TraceAnalyticMotivicTStructure.Aisle.inclusion lower :=
  rfl

/-- Monotone coaisle inclusion followed by ambient inclusion is the upper
coaisle ambient inclusion. -/
theorem TraceAnalyticMotivicTStructure.Coaisle.inclusionOfLE_comp_inclusion
    {lower upper : ℤ}
    (cut_le : lower ≤ upper) :
    TraceAnalyticMotivicTStructure.Coaisle.inclusionOfLE cut_le ⋙
        TraceAnalyticMotivicTStructure.Coaisle.inclusion lower =
      TraceAnalyticMotivicTStructure.Coaisle.inclusion upper :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
