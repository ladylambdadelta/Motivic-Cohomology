import TraceCalc.ClassicalPeriods.AGBase
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

noncomputable section

open CategoryTheory

namespace TraceCalc
namespace ClassicalPeriods
namespace Wall10A

namespace SchemeOverQ

structure IsFiniteType (X : SchemeOverQ) where
  morphism : X.X ⟶ SpecQ
  morphism_eq_structureMap : morphism = X.structureMap

structure IsSeparated (X : SchemeOverQ) : Prop where
  diagonal_is_closed : AlgebraicGeometry.IsClosedImmersion
    (prod_universal (id X) (id X) : Hom X (prod X X)).f

structure IsSmooth (X : SchemeOverQ) : Prop where
  structureMap_smooth : AlgebraicGeometry.IsSmooth X.structureMap

structure IsProper (X : SchemeOverQ) : Prop where
  structureMap_proper : AlgebraicGeometry.IsProper X.structureMap

structure IsFiniteMorphism {X Y : SchemeOverQ} (f : Hom X Y) : Prop where
  finite : AlgebraicGeometry.IsFinite f.f

structure IsClosedImmersionMorphism {X Y : SchemeOverQ} (f : Hom X Y) : Prop where
  closedImmersion : AlgebraicGeometry.IsClosedImmersion f.f

structure IsOpenImmersionMorphism {X Y : SchemeOverQ} (f : Hom X Y) : Prop where
  openImmersion : AlgebraicGeometry.IsOpenImmersion f.f

structure SmoothSchemeOverQ (X : SchemeOverQ) where
  finiteType : IsFiniteType X
  separated : IsSeparated X
  smooth : IsSmooth X

structure ProperSmoothSchemeOverQ (X : SchemeOverQ) where
  smooth : SmoothSchemeOverQ X
  proper : IsProper X

structure ClosedIntegralSubscheme (X : SchemeOverQ) where
  carrier : SchemeOverQ
  inclusion : Hom carrier X
  closedImmersion : IsClosedImmersionMorphism inclusion
  irreducible : Prop
  reduced : Prop

structure ClosedIntegralSubscheme.IsFiniteOver {X Y : SchemeOverQ}
    (Z : ClosedIntegralSubscheme (prod X Y)) where
  projection : Hom Z.carrier X
  agrees_with_first_projection :
    comp Z.inclusion (prod_fst X Y) = projection
  finite : IsFiniteMorphism projection

end SchemeOverQ
end Wall10A
end ClassicalPeriods
end TraceCalc
