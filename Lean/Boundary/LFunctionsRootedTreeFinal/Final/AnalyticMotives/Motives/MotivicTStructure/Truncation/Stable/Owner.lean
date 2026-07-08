import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Homotopy.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Owner

/-!
# Stable images of analytic truncations

This file sends the additive-homotopy truncation objects through the Verdier
quotient to the stable analytic comparison source.  These are the stable
objects that will appear as the two truncation vertices in the decomposition
triangle, together with the projection and inclusion morphisms needed for that
triangle.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The stable comparison-source object represented by the upper analytic
truncation of a concrete additive complex. -/
def TraceAnalyticMotivicTStructure.stableTruncGE
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex) :
    TraceAnalyticDMgmComparisonSource :=
  TraceAnalyticDMgmComparisonSource.objectOf
    (TraceAnalyticMotivicTStructure.homotopyTruncGE cut complex)

/-- The stable comparison-source object represented by the lower analytic
truncation of a concrete additive complex. -/
def TraceAnalyticMotivicTStructure.stableTruncLE
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex) :
    TraceAnalyticDMgmComparisonSource :=
  TraceAnalyticDMgmComparisonSource.objectOf
    (TraceAnalyticMotivicTStructure.homotopyTruncLE cut complex)

/-- The stable comparison-source map induced by upper analytic truncation. -/
def TraceAnalyticMotivicTStructure.stableTruncGEMap
    (cut : ℤ)
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target) :
    TraceAnalyticMotivicTStructure.stableTruncGE cut source ⟶
      TraceAnalyticMotivicTStructure.stableTruncGE cut target :=
  TraceAnalyticDMgmComparisonSource.mapOf
    (TraceAnalyticMotivicTStructure.homotopyTruncGEMap cut hom)

/-- The stable comparison-source map induced by lower analytic truncation. -/
def TraceAnalyticMotivicTStructure.stableTruncLEMap
    (cut : ℤ)
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target) :
    TraceAnalyticMotivicTStructure.stableTruncLE cut source ⟶
      TraceAnalyticMotivicTStructure.stableTruncLE cut target :=
  TraceAnalyticDMgmComparisonSource.mapOf
    (TraceAnalyticMotivicTStructure.homotopyTruncLEMap cut hom)

/-- The stable comparison-source image of the upper truncation projection. -/
def TraceAnalyticMotivicTStructure.stableTruncGEProjectionMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticDMgmComparisonSource.objectOf
        (TraceAnalyticAdditiveHomotopyCategory.objectOf complex) ⟶
      TraceAnalyticMotivicTStructure.stableTruncGE cut complex :=
  TraceAnalyticDMgmComparisonSource.mapOf
    (TraceAnalyticMotivicTStructure.homotopyTruncGEProjectionMap cut complex)

/-- The stable comparison-source image of the lower truncation inclusion. -/
def TraceAnalyticMotivicTStructure.stableTruncLEInclusionMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.stableTruncLE cut complex ⟶
      TraceAnalyticDMgmComparisonSource.objectOf
        (TraceAnalyticAdditiveHomotopyCategory.objectOf complex) :=
  TraceAnalyticDMgmComparisonSource.mapOf
    (TraceAnalyticMotivicTStructure.homotopyTruncLEInclusionMap cut complex)

/-- Upper stable truncation is the Verdier quotient image of upper homotopy
truncation. -/
theorem TraceAnalyticMotivicTStructure.stableTruncGE_eq_objectOf
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex) :
    TraceAnalyticMotivicTStructure.stableTruncGE cut complex =
      TraceAnalyticDMgmComparisonSource.objectOf
        (TraceAnalyticMotivicTStructure.homotopyTruncGE cut complex) :=
  rfl

/-- Lower stable truncation is the Verdier quotient image of lower homotopy
truncation. -/
theorem TraceAnalyticMotivicTStructure.stableTruncLE_eq_objectOf
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex) :
    TraceAnalyticMotivicTStructure.stableTruncLE cut complex =
      TraceAnalyticDMgmComparisonSource.objectOf
        (TraceAnalyticMotivicTStructure.homotopyTruncLE cut complex) :=
  rfl

/-- The stable upper projection is the Verdier quotient image of the homotopy
upper projection. -/
theorem TraceAnalyticMotivicTStructure.stableTruncGEProjectionMap_eq_mapOf
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.stableTruncGEProjectionMap cut complex =
      TraceAnalyticDMgmComparisonSource.mapOf
        (TraceAnalyticMotivicTStructure.homotopyTruncGEProjectionMap
          cut
          complex) :=
  rfl

/-- The stable lower inclusion is the Verdier quotient image of the homotopy
lower inclusion. -/
theorem TraceAnalyticMotivicTStructure.stableTruncLEInclusionMap_eq_mapOf
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.stableTruncLEInclusionMap cut complex =
      TraceAnalyticDMgmComparisonSource.mapOf
        (TraceAnalyticMotivicTStructure.homotopyTruncLEInclusionMap
          cut
          complex) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
