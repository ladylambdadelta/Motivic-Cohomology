import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Preparation.Algebra.Owner

/-!
# Payload accounting for quotient-input composition

This file owns derived imported-payload facts for composition of raw quotient
inputs.  The base preparation owner defines the operation and primary
certificate split; this file keeps secondary composition payload accounting in
a nested owner.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Composition with the empty input on the right exposes only imported ledger payload. -/
theorem TraceCorQQuotientInput.comp_empty_importedRectangleCount
    (input : TraceCorQQuotientInput) :
    (TraceCorQQuotientInput.comp
      input
      TraceCorQQuotientInput.empty).importedRectangleCount =
      0 +
        (input.ledger.importedRectangleCount +
          TraceCorQRelationLedger.empty.importedRectangleCount) :=
  Eq.trans
    (TraceCorQQuotientInput.comp_importedRectangleCount
      input
      TraceCorQQuotientInput.empty)
    (congrArg
      (fun count =>
        count +
          (input.ledger.importedRectangleCount +
            TraceCorQRelationLedger.empty.importedRectangleCount))
      (TraceCorQFormalSum.comp_zero_importedRectangleCount input.formalSum))

/-- Composition with the empty input on the right exposes only imported ledger rectangles. -/
theorem TraceCorQQuotientInput.comp_empty_importedRectangles
    (input : TraceCorQQuotientInput) :
    (TraceCorQQuotientInput.comp
      input
      TraceCorQQuotientInput.empty).importedRectangles =
      [] ++
        (input.ledger.importedRectangles ++
          TraceCorQRelationLedger.empty.importedRectangles) :=
  Eq.trans
    (TraceCorQQuotientInput.comp_importedRectangles
      input
      TraceCorQQuotientInput.empty)
    (congrArg
      (fun rectangles =>
        rectangles ++
          (input.ledger.importedRectangles ++
            TraceCorQRelationLedger.empty.importedRectangles))
      (TraceCorQFormalSum.comp_zero_importedRectangles input.formalSum))

/-- Scaling the left side of quotient-input composition preserves imported payload. -/
theorem TraceCorQQuotientInput.smul_comp_importedRectangleCount
    (coefficient : Rat)
    (left right : TraceCorQQuotientInput) :
    (TraceCorQQuotientInput.comp
      (TraceCorQQuotientInput.smul coefficient left)
      right).importedRectangleCount =
      (TraceCorQQuotientInput.comp left right).importedRectangleCount :=
  Eq.trans
    (congrArg
      TraceCorQQuotientInput.importedRectangleCount
      (TraceCorQQuotientInput.smul_comp coefficient left right))
    (TraceCorQQuotientInput.smul_importedRectangleCount
      coefficient
      (TraceCorQQuotientInput.comp left right))

/-- Scaling the left side of quotient-input composition preserves imported rectangles. -/
theorem TraceCorQQuotientInput.smul_comp_importedRectangles
    (coefficient : Rat)
    (left right : TraceCorQQuotientInput) :
    (TraceCorQQuotientInput.comp
      (TraceCorQQuotientInput.smul coefficient left)
      right).importedRectangles =
      (TraceCorQQuotientInput.comp left right).importedRectangles :=
  Eq.trans
    (congrArg
      TraceCorQQuotientInput.importedRectangles
      (TraceCorQQuotientInput.smul_comp coefficient left right))
    (TraceCorQQuotientInput.smul_importedRectangles
      coefficient
      (TraceCorQQuotientInput.comp left right))

/-- Scaling the right side of quotient-input composition preserves imported payload. -/
theorem TraceCorQQuotientInput.comp_smul_importedRectangleCount
    (coefficient : Rat)
    (left right : TraceCorQQuotientInput) :
    (TraceCorQQuotientInput.comp
      left
      (TraceCorQQuotientInput.smul coefficient right)).importedRectangleCount =
      (TraceCorQQuotientInput.comp left right).importedRectangleCount :=
  Eq.trans
    (congrArg
      TraceCorQQuotientInput.importedRectangleCount
      (TraceCorQQuotientInput.comp_smul coefficient left right))
    (TraceCorQQuotientInput.smul_importedRectangleCount
      coefficient
      (TraceCorQQuotientInput.comp left right))

/-- Scaling the right side of quotient-input composition preserves imported rectangles. -/
theorem TraceCorQQuotientInput.comp_smul_importedRectangles
    (coefficient : Rat)
    (left right : TraceCorQQuotientInput) :
    (TraceCorQQuotientInput.comp
      left
      (TraceCorQQuotientInput.smul coefficient right)).importedRectangles =
      (TraceCorQQuotientInput.comp left right).importedRectangles :=
  Eq.trans
    (congrArg
      TraceCorQQuotientInput.importedRectangles
      (TraceCorQQuotientInput.comp_smul coefficient left right))
    (TraceCorQQuotientInput.smul_importedRectangles
      coefficient
      (TraceCorQQuotientInput.comp left right))

end AnalyticMotives
end LFunctions
end Boundary
