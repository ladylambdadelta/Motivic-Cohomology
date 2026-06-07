import Boundary.SmOver
import Geometry.Schemes.Basic
import Mathlib.CategoryTheory.Sites.Spaces

/-!
# Realization site for a smooth scheme

For a smooth scheme `X`, the canonical site for global Betti/de Rham realization is the
Grothendieck site of open subsets of the underlying topological space of `X.scheme`.

This is the stable long-term site object for sheafification and derived global sections.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace Boundary
namespace Realization

universe u

variable {k : Type u} [Field k] [PerfectField k]

/-- The realization site attached to a smooth scheme: the open-subset site of its underlying
topological space. -/
abbrev realizationSite (X : Geometry.SmSchemeOver k) :
    GrothendieckTopology (Opens X.scheme.toTopCat) :=
  Opens.grothendieckTopology X.scheme.toTopCat

@[simp]
theorem realizationSite_eq (X : Geometry.SmSchemeOver k) :
    realizationSite X = Opens.grothendieckTopology X.scheme.toTopCat :=
  rfl

/-- The canonical pretopology on the realization site. -/
abbrev realizationPretopology (X : Geometry.SmSchemeOver k) :
    Pretopology (Opens X.scheme.toTopCat) :=
  Opens.pretopology X.scheme.toTopCat

@[simp]
theorem realizationPretopology_toGrothendieck (X : Geometry.SmSchemeOver k) :
    (realizationPretopology X).toGrothendieck = realizationSite X :=
  Opens.pretopology_toGrothendieck X.scheme.toTopCat

end Realization
end Boundary
