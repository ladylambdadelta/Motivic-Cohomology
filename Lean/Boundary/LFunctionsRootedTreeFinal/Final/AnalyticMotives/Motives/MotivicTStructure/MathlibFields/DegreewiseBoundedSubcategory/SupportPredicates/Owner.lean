import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Bounds.IsoClosure.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Support.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.LE.Bounds.IsoClosure.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.LE.Support.Owner

/-!
# Support predicates for the degreewise bounded t-structure

The degreewise bounded stable source is larger than the literally bounded
source, so its t-structure predicates are expressed by concrete one-sided
analytic cochain representatives: degreewise iso-closure bounded complexes
strictly supported on the lower or upper analytic tail.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- Ambient stable objects represented by a degreewise bounded complex
strictly supported on the lower analytic tail at `cut`. -/
def supportedLEAmbient
    (cut : ℤ)
    (object : TraceAnalyticDMgmComparisonSource) :
    Prop :=
  ∃ (bound : Nat),
    ∃ (complex : TraceAnalyticAdditiveCochainComplex),
      TraceAnalyticAdditiveCochainComplex.DegreewiseIsoClosureBoundedBy
          complex
          bound ∧
        Nonempty
          (complex.IsStrictlySupported
            (TraceAnalyticMotivicTStructure.truncLEEmbedding cut)) ∧
          object =
            TraceAnalyticDMgmComparisonSource.objectOf
              (TraceAnalyticAdditiveHomotopyCategory.objectOf complex)

/-- Ambient stable objects represented by a degreewise bounded complex
strictly supported on the upper analytic tail at `cut`. -/
def supportedGEAmbient
    (cut : ℤ)
    (object : TraceAnalyticDMgmComparisonSource) :
    Prop :=
  ∃ (bound : Nat),
    ∃ (complex : TraceAnalyticAdditiveCochainComplex),
      TraceAnalyticAdditiveCochainComplex.DegreewiseIsoClosureBoundedBy
          complex
          bound ∧
        Nonempty
          (complex.IsStrictlySupported
            (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)) ∧
          object =
            TraceAnalyticDMgmComparisonSource.objectOf
              (TraceAnalyticAdditiveHomotopyCategory.objectOf complex)

/-- Degreewise bounded nonpositive predicate at `cut`, using concrete lower
tail support. -/
abbrev supportedLE
    (cut : ℤ)
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable) :
    Prop :=
  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportedLEAmbient cut object.object

/-- Degreewise bounded nonnegative predicate at `cut`, using concrete upper
tail support. -/
abbrev supportedGE
    (cut : ℤ)
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable) :
    Prop :=
  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportedGEAmbient cut object.object

/-- The lower stable truncation vertex satisfies the degreewise support-based
`LE` predicate. -/
theorem stableTruncLE_mem_supportedLEAmbient
    (cut : ℤ)
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex)
    (bounded :
      TraceAnalyticAdditiveCochainComplex.DegreewiseIsoClosureBoundedBy
        complex
        bound)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportedLEAmbient
        cut
        (TraceAnalyticMotivicTStructure.stableTruncLE cut complex) :=
  Exists.intro
    (TraceAnalyticMotivicTStructure.additiveTruncLEIsoClosureBound
      cut
      bound
      complex)
    (Exists.intro
      (TraceAnalyticMotivicTStructure.additiveTruncLE cut complex)
      (And.intro
        (TraceAnalyticMotivicTStructure
          .additiveTruncLE_sourceComplexDegreewiseIsoClosureBoundedBy
            cut
            complex
            bounded)
        (And.intro
          (Nonempty.intro
            (TraceAnalyticMotivicTStructure
              .additiveTruncLE_isStrictlySupported cut complex))
          (TraceAnalyticMotivicTStructure.stableTruncLE_eq_objectOf
            cut
            complex))))

/-- The upper stable truncation vertex satisfies the degreewise support-based
`GE` predicate. -/
theorem stableTruncGE_mem_supportedGEAmbient
    (cut : ℤ)
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex)
    (bounded :
      TraceAnalyticAdditiveCochainComplex.DegreewiseIsoClosureBoundedBy
        complex
        bound)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportedGEAmbient
        cut
        (TraceAnalyticMotivicTStructure.stableTruncGE cut complex) :=
  Exists.intro
    (TraceAnalyticMotivicTStructure.additiveTruncGEIsoClosureBound
      cut
      bound
      complex)
    (Exists.intro
      (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex)
      (And.intro
        (TraceAnalyticMotivicTStructure
          .additiveTruncGE_sourceComplexDegreewiseIsoClosureBoundedBy
            cut
            complex
            bounded)
        (And.intro
          (Nonempty.intro
            (TraceAnalyticMotivicTStructure
              .additiveTruncGE_isStrictlySupported cut complex))
          (TraceAnalyticMotivicTStructure.stableTruncGE_eq_objectOf
            cut
            complex))))

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
