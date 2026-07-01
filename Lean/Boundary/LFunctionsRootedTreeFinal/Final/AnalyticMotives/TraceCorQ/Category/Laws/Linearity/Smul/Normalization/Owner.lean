import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Linearity.Smul.Owner

/-!
# Scalar normalization for typed composition

This file collects derived scalar-normalization laws for typed composition.
The primitive scalar-linearity laws live in `Linearity.Smul.Owner`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Scaling a typed composite may be moved to the left input. -/
theorem TraceCorQHom.smul_comp_eq_comp_smul_left
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
  Eq.symm
    (TraceCorQHom.smul_comp coefficient left right)

/-- Scaling a typed composite may be moved to the right input. -/
theorem TraceCorQHom.smul_comp_eq_comp_smul_right
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
  Eq.symm
    (TraceCorQHom.comp_smul coefficient left right)

/-- Moving a scalar between the two inputs of typed composition preserves the composite. -/
theorem TraceCorQHom.smul_left_comp_eq_comp_smul_right
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
  Eq.trans
    (TraceCorQHom.smul_comp coefficient left right)
    (Eq.symm
      (TraceCorQHom.comp_smul coefficient left right))

/-- Scaling both inputs can be folded into a single scalar on the composite. -/
theorem TraceCorQHom.comp_smul_smul_eq_smul_comp
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
  TraceCorQHom.smul_comp_smul
    leftCoefficient
    rightCoefficient
    left
    right

end AnalyticMotives
end LFunctions
end Boundary
