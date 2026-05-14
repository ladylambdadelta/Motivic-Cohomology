import Mathlib.CategoryTheory.Category.Basic

universe u v

namespace TraceCalc
namespace CategoryInfra

/-- Minimal abstract dg-style interface for the stable-completion lane. -/
structure DGCategoryLike where
  Obj : Type u
  HomComplex : Obj → Obj → Type v
  differential : {X Y : Obj} → HomComplex X Y → HomComplex X Y
  idClosed : Prop
  compClosed : Prop
  differentialSquaredZero : Prop
  idClosed_holds : idClosed
  compClosed_holds : compClosed
  differentialSquaredZero_holds : differentialSquaredZero

namespace DGCategoryLike

end DGCategoryLike

/-- Abstract free-dg-envelope package for a presentation type. -/
structure FreeDGEnvelope (presentation : Type u) where
  envelope : DGCategoryLike.{u, v}
  includeObj : presentation → envelope.Obj
  universalProperty : Prop
  universalProperty_holds : universalProperty

namespace FreeDGEnvelope

end FreeDGEnvelope

end CategoryInfra
end TraceCalc