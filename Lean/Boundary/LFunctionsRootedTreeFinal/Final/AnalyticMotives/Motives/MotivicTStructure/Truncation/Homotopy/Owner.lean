import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.Owner

/-!
# Homotopy images of analytic truncations

This file lifts the concrete additive-complex truncations above and below a
cut to the additive analytic homotopy category by applying the homotopy
quotient functor to the truncated complexes, truncated maps, and concrete
projection/inclusion maps.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The additive homotopy object represented by the upper analytic truncation
of a concrete additive complex. -/
def TraceAnalyticMotivicTStructure.homotopyTruncGE
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex) :
    TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticAdditiveHomotopyCategory.objectOf
    (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex)

/-- The additive homotopy object represented by the lower analytic truncation
of a concrete additive complex. -/
def TraceAnalyticMotivicTStructure.homotopyTruncLE
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex) :
    TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticAdditiveHomotopyCategory.objectOf
    (TraceAnalyticMotivicTStructure.additiveTruncLE cut complex)

/-- The additive homotopy map induced by the upper analytic truncation of a
chain map. -/
def TraceAnalyticMotivicTStructure.homotopyTruncGEMap
    (cut : ℤ)
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target) :
    TraceAnalyticMotivicTStructure.homotopyTruncGE cut source ⟶
      TraceAnalyticMotivicTStructure.homotopyTruncGE cut target :=
  TraceAnalyticAdditiveHomotopyCategory.mapOf
    (TraceAnalyticMotivicTStructure.additiveTruncGEMap cut hom)

/-- The additive homotopy map induced by the lower analytic truncation of a
chain map. -/
def TraceAnalyticMotivicTStructure.homotopyTruncLEMap
    (cut : ℤ)
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target) :
    TraceAnalyticMotivicTStructure.homotopyTruncLE cut source ⟶
      TraceAnalyticMotivicTStructure.homotopyTruncLE cut target :=
  TraceAnalyticAdditiveHomotopyCategory.mapOf
    (TraceAnalyticMotivicTStructure.additiveTruncLEMap cut hom)

/-- The additive homotopy image of the concrete upper truncation projection
`K ⟶ truncGE(cut, K)`. -/
def TraceAnalyticMotivicTStructure.homotopyTruncGEProjectionMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticAdditiveHomotopyCategory.objectOf complex ⟶
      TraceAnalyticMotivicTStructure.homotopyTruncGE cut complex :=
  TraceAnalyticAdditiveHomotopyCategory.mapOf
    (TraceAnalyticMotivicTStructure.additiveTruncGEProjectionMap cut complex)

/-- The additive homotopy image of the concrete lower truncation inclusion
`truncLE(cut, K) ⟶ K`. -/
def TraceAnalyticMotivicTStructure.homotopyTruncLEInclusionMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.homotopyTruncLE cut complex ⟶
      TraceAnalyticAdditiveHomotopyCategory.objectOf complex :=
  TraceAnalyticAdditiveHomotopyCategory.mapOf
    (TraceAnalyticMotivicTStructure.additiveTruncLEInclusionMap cut complex)

/-- Upper homotopy truncation is the homotopy quotient image of the concrete
upper additive truncation. -/
theorem TraceAnalyticMotivicTStructure.homotopyTruncGE_eq_objectOf
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex) :
    TraceAnalyticMotivicTStructure.homotopyTruncGE cut complex =
      TraceAnalyticAdditiveHomotopyCategory.objectOf
        (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex) :=
  rfl

/-- Lower homotopy truncation is the homotopy quotient image of the concrete
lower additive truncation. -/
theorem TraceAnalyticMotivicTStructure.homotopyTruncLE_eq_objectOf
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex) :
    TraceAnalyticMotivicTStructure.homotopyTruncLE cut complex =
      TraceAnalyticAdditiveHomotopyCategory.objectOf
        (TraceAnalyticMotivicTStructure.additiveTruncLE cut complex) :=
  rfl

/-- The upper homotopy projection is the homotopy quotient image of the
concrete upper projection chain map. -/
theorem TraceAnalyticMotivicTStructure.homotopyTruncGEProjectionMap_eq_mapOf
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.homotopyTruncGEProjectionMap cut complex =
      TraceAnalyticAdditiveHomotopyCategory.mapOf
        (TraceAnalyticMotivicTStructure.additiveTruncGEProjectionMap
          cut
          complex) :=
  rfl

/-- The lower homotopy inclusion is the homotopy quotient image of the
concrete lower inclusion chain map. -/
theorem TraceAnalyticMotivicTStructure.homotopyTruncLEInclusionMap_eq_mapOf
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.homotopyTruncLEInclusionMap cut complex =
      TraceAnalyticAdditiveHomotopyCategory.mapOf
        (TraceAnalyticMotivicTStructure.additiveTruncLEInclusionMap
          cut
          complex) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
