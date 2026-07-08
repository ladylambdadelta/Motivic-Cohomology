import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Shift.Homotopy.Owner

/-!
# Functoriality of shifts on bounded-weight homotopy objects

The integer shift functors preserve identity and composition for morphisms
represented by bounded additive analytic complexes.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Shifting the identity map of a bounded representative gives the identity on the shift. -/
theorem TraceAnalyticAdditiveHomotopyCategory.shiftedWeightBoundedMap_id
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound)
    (degree : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.shiftedWeightBoundedMap
        (TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.id complex)
        degree =
      𝟙
        (TraceAnalyticAdditiveHomotopyCategory.shiftedWeightBoundedObject
          complex
          degree) :=
  Eq.trans
    (congrArg
      (fun hom =>
        TraceAnalyticAdditiveHomotopyCategory.shiftedMap
          hom
          degree)
      (TraceAnalyticAdditiveHomotopyCategory.weightBoundedMap_id
        complex))
    (TraceAnalyticAdditiveHomotopyCategory.shiftedMap_id
      (TraceAnalyticAdditiveHomotopyCategory.weightBoundedObject complex)
      degree)

/-- Shifting a composite of bounded-representative maps gives the composite of shifts. -/
theorem TraceAnalyticAdditiveHomotopyCategory.shiftedWeightBoundedMap_comp
    {bound : Nat}
    {first second third :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (left :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom first second)
    (right :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom second third)
    (degree : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.shiftedWeightBoundedMap
        (TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.comp left right)
        degree =
      TraceAnalyticAdditiveHomotopyCategory.shiftedWeightBoundedMap left degree ≫
        TraceAnalyticAdditiveHomotopyCategory.shiftedWeightBoundedMap right degree :=
  Eq.trans
    (congrArg
      (fun hom =>
        TraceAnalyticAdditiveHomotopyCategory.shiftedMap
          hom
          degree)
      (TraceAnalyticAdditiveHomotopyCategory.weightBoundedMap_comp
        left
        right))
    (TraceAnalyticAdditiveHomotopyCategory.shiftedMap_comp
      (TraceAnalyticAdditiveHomotopyCategory.weightBoundedMap left)
      (TraceAnalyticAdditiveHomotopyCategory.weightBoundedMap right)
      degree)

end AnalyticMotives
end LFunctions
end Boundary
