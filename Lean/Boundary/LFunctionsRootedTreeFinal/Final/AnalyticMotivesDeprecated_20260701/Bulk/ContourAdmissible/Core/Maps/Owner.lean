import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.Core.Carrier.Owner

/-!
# Maps of analytic bulk cores

This file owns maps between analytic bulk cores once the compatibility between
the arithmetic shadow and analytic carrier has been stated.  Correspondence
morphisms are downstream and are not reduced to ordinary maps.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/--
A paired map of analytic bulk cores.  It records the algebraic-shadow map and
the analytic-carrier map separately.  Contour-compatible correspondences are
defined downstream from supports, transports, and residue compatibility, not
from this ordinary paired-map layer.
-/
structure AnalyticBulkCoreHom (X Y : AnalyticBulkCore) where
  baseMap : X.base ⟶ Y.base
  carrierMap : X.carrier ⟶ Y.carrier

namespace AnalyticBulkCoreHom

/-- Identity paired map of an analytic bulk core. -/
def id (X : AnalyticBulkCore) : AnalyticBulkCoreHom X X where
  baseMap := 𝟙 X.base
  carrierMap := 𝟙 X.carrier

/-- Composition of paired maps of analytic bulk cores. -/
def comp {X Y Z : AnalyticBulkCore}
    (f : AnalyticBulkCoreHom X Y) (g : AnalyticBulkCoreHom Y Z) :
    AnalyticBulkCoreHom X Z where
  baseMap := f.baseMap ≫ g.baseMap
  carrierMap := f.carrierMap ≫ g.carrierMap

/-- Left identity for paired maps of analytic bulk cores. -/
theorem id_comp {X Y : AnalyticBulkCore} (f : AnalyticBulkCoreHom X Y) :
    comp (id X) f = f :=
  match f with
  | ⟨_, _⟩ => rfl

/-- Right identity for paired maps of analytic bulk cores. -/
theorem comp_id {X Y : AnalyticBulkCore} (f : AnalyticBulkCoreHom X Y) :
    comp f (id Y) = f :=
  match f with
  | ⟨_, _⟩ => rfl

/-- Associativity for paired maps of analytic bulk cores. -/
theorem comp_assoc {W X Y Z : AnalyticBulkCore}
    (f : AnalyticBulkCoreHom W X)
    (g : AnalyticBulkCoreHom X Y)
    (h : AnalyticBulkCoreHom Y Z) :
    comp (comp f g) h = comp f (comp g h) :=
  match f, g, h with
  | ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩ => rfl

end AnalyticBulkCoreHom

end AnalyticMotives
end LFunctions
end Boundary
