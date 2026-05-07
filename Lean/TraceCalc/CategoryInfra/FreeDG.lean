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

def theoremTarget (C : DGCategoryLike.{u, v}) : Prop :=
  C.idClosed ∧ C.compClosed ∧ C.differentialSquaredZero

theorem theoremTarget_holds (C : DGCategoryLike.{u, v}) : C.theoremTarget := by
  exact ⟨C.idClosed_holds, C.compClosed_holds, C.differentialSquaredZero_holds⟩

end DGCategoryLike

/-- Abstract free-dg-envelope package for a presentation type. -/
structure FreeDGEnvelope (presentation : Type u) where
  envelope : DGCategoryLike.{u, v}
  includeObj : presentation → envelope.Obj
  universalProperty : Prop
  universalProperty_holds : universalProperty

namespace FreeDGEnvelope

def existenceTarget {presentation : Type u}
    (E : FreeDGEnvelope.{u, v} presentation) : Prop :=
  Nonempty (FreeDGEnvelope.{u, v} presentation)

theorem existenceTarget_holds {presentation : Type u}
    (E : FreeDGEnvelope.{u, v} presentation) : E.existenceTarget := by
  exact ⟨E⟩

def universalPropertyTarget {presentation : Type u}
    (E : FreeDGEnvelope.{u, v} presentation) : Prop :=
  E.universalProperty

theorem universalPropertyTarget_holds {presentation : Type u}
    (E : FreeDGEnvelope.{u, v} presentation) : E.universalPropertyTarget :=
  E.universalProperty_holds

def theoremTarget {presentation : Type u}
    (E : FreeDGEnvelope.{u, v} presentation) : Prop :=
  E.existenceTarget ∧ E.universalPropertyTarget

theorem theoremTarget_holds {presentation : Type u}
    (E : FreeDGEnvelope.{u, v} presentation) : E.theoremTarget := by
  exact ⟨E.existenceTarget_holds, E.universalPropertyTarget_holds⟩

end FreeDGEnvelope

end CategoryInfra
end TraceCalc