import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Linearity.Smul.Normalization.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Linearity.Smul.Sign.Owner

/-!
# Public scalar and sign normalization for TraceCorQ composition

This file exposes scalar and sign movement laws for typed
trace-correspondence composition through the public analytic-motives root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: a scalar on the composite may be moved to the left input. -/
theorem AnalyticMotivesRoot.traceCorQHom_smul_comp_eq_comp_smul_left
    {source middle target : TraceCorQObject}
    (coefficient : Rat)
    (left : TraceCorQHom source middle)
    (right : TraceCorQHom middle target) :
    TraceCorQHom.smul
      coefficient
      (TraceCorQHom.comp left right) =
      TraceCorQHom.comp
        (TraceCorQHom.smul coefficient left)
        right :=
  TraceCorQHom.smul_comp_eq_comp_smul_left
    coefficient
    left
    right

/-- Public wrapper: a scalar on the composite may be moved to the right input. -/
theorem AnalyticMotivesRoot.traceCorQHom_smul_comp_eq_comp_smul_right
    {source middle target : TraceCorQObject}
    (coefficient : Rat)
    (left : TraceCorQHom source middle)
    (right : TraceCorQHom middle target) :
    TraceCorQHom.smul
      coefficient
      (TraceCorQHom.comp left right) =
      TraceCorQHom.comp
        left
        (TraceCorQHom.smul coefficient right) :=
  TraceCorQHom.smul_comp_eq_comp_smul_right
    coefficient
    left
    right

/-- Public wrapper: a scalar can be moved between the two inputs of composition. -/
theorem AnalyticMotivesRoot.traceCorQHom_smul_left_comp_eq_comp_smul_right
    {source middle target : TraceCorQObject}
    (coefficient : Rat)
    (left : TraceCorQHom source middle)
    (right : TraceCorQHom middle target) :
    TraceCorQHom.comp
      (TraceCorQHom.smul coefficient left)
      right =
      TraceCorQHom.comp
        left
        (TraceCorQHom.smul coefficient right) :=
  TraceCorQHom.smul_left_comp_eq_comp_smul_right
    coefficient
    left
    right

/-- Public wrapper: scaling both inputs folds into one scalar on the composite. -/
theorem AnalyticMotivesRoot.traceCorQHom_comp_smul_smul_eq_smul_comp
    {source middle target : TraceCorQObject}
    (leftCoefficient rightCoefficient : Rat)
    (left : TraceCorQHom source middle)
    (right : TraceCorQHom middle target) :
    TraceCorQHom.comp
      (TraceCorQHom.smul leftCoefficient left)
      (TraceCorQHom.smul rightCoefficient right) =
      TraceCorQHom.smul
        (leftCoefficient * rightCoefficient)
        (TraceCorQHom.comp left right) :=
  TraceCorQHom.comp_smul_smul_eq_smul_comp
    leftCoefficient
    rightCoefficient
    left
    right

/-- Public wrapper: a negation on the composite may be moved to the left input. -/
theorem AnalyticMotivesRoot.traceCorQHom_neg_comp_eq_comp_neg_left
    {source middle target : TraceCorQObject}
    (left : TraceCorQHom source middle)
    (right : TraceCorQHom middle target) :
    TraceCorQHom.neg
      (TraceCorQHom.comp left right) =
      TraceCorQHom.comp (TraceCorQHom.neg left) right :=
  TraceCorQHom.neg_comp_eq_comp_neg_left
    left
    right

/-- Public wrapper: a negation on the composite may be moved to the right input. -/
theorem AnalyticMotivesRoot.traceCorQHom_neg_comp_eq_comp_neg_right
    {source middle target : TraceCorQObject}
    (left : TraceCorQHom source middle)
    (right : TraceCorQHom middle target) :
    TraceCorQHom.neg
      (TraceCorQHom.comp left right) =
      TraceCorQHom.comp left (TraceCorQHom.neg right) :=
  TraceCorQHom.neg_comp_eq_comp_neg_right
    left
    right

/-- Public wrapper: a sign can be moved between the two inputs of composition. -/
theorem AnalyticMotivesRoot.traceCorQHom_neg_left_comp_eq_comp_neg_right
    {source middle target : TraceCorQObject}
    (left : TraceCorQHom source middle)
    (right : TraceCorQHom middle target) :
    TraceCorQHom.comp (TraceCorQHom.neg left) right =
      TraceCorQHom.comp left (TraceCorQHom.neg right) :=
  TraceCorQHom.neg_left_comp_eq_comp_neg_right
    left
    right

/-- Public wrapper: negating the composite of two negative inputs gives the negative composite. -/
theorem AnalyticMotivesRoot.traceCorQHom_neg_neg_comp_neg
    {source middle target : TraceCorQObject}
    (left : TraceCorQHom source middle)
    (right : TraceCorQHom middle target) :
    TraceCorQHom.neg
      (TraceCorQHom.comp (TraceCorQHom.neg left) (TraceCorQHom.neg right)) =
      TraceCorQHom.neg (TraceCorQHom.comp left right) :=
  TraceCorQHom.neg_neg_comp_neg
    left
    right

end AnalyticMotives
end LFunctions
end Boundary
