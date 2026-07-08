import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Opposites
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Owner

open scoped CategoryTheory

/-!
# Trace presheaves

This file owns presheaves on the Q-linear trace-correspondence category.

The motive category is built from this analytic correspondence category by
localization and stabilization, not by aliasing an existing geometric-motive
definition.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Q-module-valued presheaves on the analytic trace-correspondence category. -/
abbrev TraceCorQPresheaf :=
  (Opposite TraceCorQObject) ⥤ (ModuleCat Rat)

/-- The opposite arrow associated to a concrete trace correspondence. -/
def TraceCorQPresheaf.opHom
    {source target : TraceCorQObject}
    (morphism : TraceCorQHom source target) :
    Opposite.op target ⟶ Opposite.op source :=
  Quiver.Hom.op (show source ⟶ target from morphism)

/-- The Q-module of sections of a trace presheaf on an object. -/
def TraceCorQPresheaf.sections
    (presheaf : TraceCorQPresheaf)
    (object : TraceCorQObject) :
    ModuleCat Rat :=
  presheaf.obj (Opposite.op object)

/-- Pull back sections contravariantly along a trace correspondence. -/
def TraceCorQPresheaf.pullback
    (presheaf : TraceCorQPresheaf)
    {source target : TraceCorQObject}
    (morphism : TraceCorQHom source target) :
    presheaf.sections target ⟶ presheaf.sections source :=
  presheaf.map (TraceCorQPresheaf.opHom morphism)

/-- Sections are evaluation at the opposite object. -/
theorem TraceCorQPresheaf.sections_eq_obj_op
    (presheaf : TraceCorQPresheaf)
    (object : TraceCorQObject) :
    presheaf.sections object =
      presheaf.obj (Opposite.op object) :=
  rfl

/-- Pullback is functorial action on the opposite morphism. -/
theorem TraceCorQPresheaf.pullback_eq_map_op
    (presheaf : TraceCorQPresheaf)
    {source target : TraceCorQObject}
    (morphism : TraceCorQHom source target) :
    presheaf.pullback morphism =
      presheaf.map (TraceCorQPresheaf.opHom morphism) :=
  rfl

/-- Pullback along the identity trace correspondence is the identity on sections. -/
theorem TraceCorQPresheaf.pullback_id
    (presheaf : TraceCorQPresheaf)
    (object : TraceCorQObject) :
    presheaf.pullback (TraceCorQHom.id object) =
      𝟙 (presheaf.sections object) :=
  presheaf.map_id (Opposite.op object)

/-- Pullback is contravariantly functorial for trace-correspondence composition. -/
theorem TraceCorQPresheaf.pullback_comp
    (presheaf : TraceCorQPresheaf)
    {first second third : TraceCorQObject}
    (left : TraceCorQHom first second)
    (right : TraceCorQHom second third) :
    presheaf.pullback (TraceCorQHom.comp left right) =
      presheaf.pullback right ≫ presheaf.pullback left :=
  presheaf.map_comp
    (TraceCorQPresheaf.opHom right)
    (TraceCorQPresheaf.opHom left)

/-- A morphism of Q-module-valued trace presheaves. -/
abbrev TraceCorQPresheafHom
    (source target : TraceCorQPresheaf) :=
  source ⟶ target

/-- The component of a presheaf morphism on sections over one trace object. -/
def TraceCorQPresheafHom.component
    {source target : TraceCorQPresheaf}
    (morphism : TraceCorQPresheafHom source target)
    (object : TraceCorQObject) :
    source.sections object ⟶ target.sections object :=
  morphism.app (Opposite.op object)

/-- Presheaf morphism components are natural-transformation components. -/
theorem TraceCorQPresheafHom.component_eq_app_op
    {source target : TraceCorQPresheaf}
    (morphism : TraceCorQPresheafHom source target)
    (object : TraceCorQObject) :
    morphism.component object =
      morphism.app (Opposite.op object) :=
  rfl

/-- Presheaf morphism components commute with trace-correspondence pullback. -/
theorem TraceCorQPresheafHom.pullback_naturality
    {sourcePresheaf targetPresheaf : TraceCorQPresheaf}
    (presheafMorphism :
      TraceCorQPresheafHom sourcePresheaf targetPresheaf)
    {source target : TraceCorQObject}
    (traceMorphism : TraceCorQHom source target) :
    sourcePresheaf.pullback traceMorphism ≫
        presheafMorphism.component source =
      presheafMorphism.component target ≫
        targetPresheaf.pullback traceMorphism :=
  presheafMorphism.naturality
    (TraceCorQPresheaf.opHom traceMorphism)

/-- An isomorphism of Q-module-valued trace presheaves. -/
abbrev TraceCorQPresheafIso
    (source target : TraceCorQPresheaf) :=
  source ≅ target

/-- The section-level component isomorphism of a presheaf isomorphism. -/
def TraceCorQPresheafIso.component
    {source target : TraceCorQPresheaf}
    (isomorphism : TraceCorQPresheafIso source target)
    (object : TraceCorQObject) :
    source.sections object ≅ target.sections object :=
  isomorphism.app (Opposite.op object)

/-- Presheaf isomorphism components are natural-isomorphism components. -/
theorem TraceCorQPresheafIso.component_eq_app_op
    {source target : TraceCorQPresheaf}
    (isomorphism : TraceCorQPresheafIso source target)
    (object : TraceCorQObject) :
    isomorphism.component object =
      isomorphism.app (Opposite.op object) :=
  rfl

/-- Evaluation of trace presheaves on one trace object. -/
def TraceCorQPresheaf.evaluation
    (object : TraceCorQObject) :
    TraceCorQPresheaf ⥤ (ModuleCat Rat) where
  obj := fun presheaf => presheaf.sections object
  map := fun morphism => TraceCorQPresheafHom.component morphism object
  map_id := fun presheaf => rfl
  map_comp := fun left right => rfl

/-- Evaluation sends a presheaf to its sections on the object. -/
theorem TraceCorQPresheaf.evaluation_obj
    (object : TraceCorQObject)
    (presheaf : TraceCorQPresheaf) :
    (TraceCorQPresheaf.evaluation object).obj presheaf =
      presheaf.sections object :=
  rfl

/-- Evaluation sends a presheaf morphism to its section component. -/
theorem TraceCorQPresheaf.evaluation_map
    (object : TraceCorQObject)
    {source target : TraceCorQPresheaf}
    (morphism : TraceCorQPresheafHom source target) :
    (TraceCorQPresheaf.evaluation object).map morphism =
      morphism.component object :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
