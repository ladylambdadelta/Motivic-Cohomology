import Mathlib.CategoryTheory.Category.Basic

universe u v

open CategoryTheory

namespace TraceCalc
namespace LayerA

/-- Minimal interface for a category presented by a designated generator family. -/
structure GeneratorPresentation where
  C : Type u
  [cat : Category.{v} C]
  G : Type u
  i : G → C

attribute [instance] GeneratorPresentation.cat

/-- A conservative placeholder for "stable-like" properties required downstream.
Each field is a named requirement that can later be replaced by concrete mathlib structures.
This is a `Type`-level bundle of `Prop`-valued obligations, not a `Prop` itself. -/
structure StableLike (C : Type u) [Category.{v} C] where
  hasFiniteLimits : Prop
  hasFiniteColimits : Prop
  hasSuspensionData : Prop
  exactTrianglesAvailable : Prop

end LayerA
end TraceCalc
