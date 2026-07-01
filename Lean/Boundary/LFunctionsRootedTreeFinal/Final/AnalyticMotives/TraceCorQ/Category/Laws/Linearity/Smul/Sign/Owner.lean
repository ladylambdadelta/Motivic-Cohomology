import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Neg.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Linearity.Smul.Owner

/-!
# Sign normalization for typed composition

This file collects derived sign-normalization laws for typed composition.
The primitive scalar-linearity and negation interaction laws live in
`Linearity.Smul.Owner`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Negation of a typed composite may be moved to the left input. -/
theorem TraceCorQHom.neg_comp_eq_comp_neg_left
    {source middle target : TraceCorQObject}
    (left : TraceCorQHom source middle)
    (right : TraceCorQHom middle target) :
    TraceCorQHom.neg
      (TraceCorQHom.comp left right) =
      TraceCorQHom.comp (TraceCorQHom.neg left) right :=
  Eq.symm (TraceCorQHom.neg_comp left right)

/-- Negation of a typed composite may be moved to the right input. -/
theorem TraceCorQHom.neg_comp_eq_comp_neg_right
    {source middle target : TraceCorQObject}
    (left : TraceCorQHom source middle)
    (right : TraceCorQHom middle target) :
    TraceCorQHom.neg
      (TraceCorQHom.comp left right) =
      TraceCorQHom.comp left (TraceCorQHom.neg right) :=
  Eq.symm (TraceCorQHom.comp_neg left right)

/-- Moving a sign between the two inputs of typed composition preserves the composite. -/
theorem TraceCorQHom.neg_left_comp_eq_comp_neg_right
    {source middle target : TraceCorQObject}
    (left : TraceCorQHom source middle)
    (right : TraceCorQHom middle target) :
    TraceCorQHom.comp (TraceCorQHom.neg left) right =
      TraceCorQHom.comp left (TraceCorQHom.neg right) :=
  Eq.trans
    (TraceCorQHom.neg_comp left right)
    (Eq.symm (TraceCorQHom.comp_neg left right))

/-- Negating the composite of two negative inputs gives the negative composite. -/
theorem TraceCorQHom.neg_neg_comp_neg
    {source middle target : TraceCorQObject}
    (left : TraceCorQHom source middle)
    (right : TraceCorQHom middle target) :
    TraceCorQHom.neg
      (TraceCorQHom.comp (TraceCorQHom.neg left) (TraceCorQHom.neg right)) =
      TraceCorQHom.neg (TraceCorQHom.comp left right) :=
  congrArg
    TraceCorQHom.neg
    (TraceCorQHom.neg_comp_neg left right)

end AnalyticMotives
end LFunctions
end Boundary
