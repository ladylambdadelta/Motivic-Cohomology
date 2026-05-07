import TraceCalc.ClassicalPeriods.RationalEquivalence

noncomputable section

namespace TraceCalc
namespace ClassicalPeriods
namespace Wall10A

namespace SchemeOverQ

structure CycleMap (X Y : SchemeOverQ) where
  toFun : AlgebraicCycle X → AlgebraicCycle Y
  map_zero : toFun 0 = 0
  map_add : ∀ a b, toFun (a + b) = toFun a + toFun b
  respects_rational_equivalence :
    ∀ {a b}, RationalEquivalence X a b → RationalEquivalence Y (toFun a) (toFun b)

def CycleMap.id (X : SchemeOverQ) : CycleMap X X where
  toFun := fun a => a
  map_zero := rfl
  map_add := by intro a b; rfl
  respects_rational_equivalence := by intro a b h; exact h

def CycleMap.comp {X Y Z : SchemeOverQ} (f : CycleMap X Y) (g : CycleMap Y Z) : CycleMap X Z where
  toFun := fun a => g.toFun (f.toFun a)
  map_zero := by
    change g.toFun (f.toFun 0) = 0
    rw [f.map_zero]
    exact g.map_zero
  map_add := by
    intro a b
    change g.toFun (f.toFun (a + b)) = g.toFun (f.toFun a) + g.toFun (f.toFun b)
    rw [f.map_add, g.map_add]
  respects_rational_equivalence := by
    intro a b h
    exact g.respects_rational_equivalence (f.respects_rational_equivalence h)

structure ProperPushforwardData {X Y : SchemeOverQ} (f : Hom X Y) where
  map : CycleMap X Y
  maps_generator_to_image_cycle : ∀ Z : CycleGenerator X, Prop

structure FlatPullbackData {X Y : SchemeOverQ} (f : Hom X Y) where
  map : CycleMap Y X
  maps_generator_to_fiber_cycle : ∀ Z : CycleGenerator Y, Prop

structure IntersectionProductData (X : SchemeOverQ) where
  product : AlgebraicCycle X → AlgebraicCycle X → AlgebraicCycle X
  product_zero_left : ∀ a, product 0 a = 0
  product_zero_right : ∀ a, product a 0 = 0
  product_add_left : ∀ a b c, product (a + b) c = product a c + product b c
  product_add_right : ∀ a b c, product a (b + c) = product a b + product a c
  respects_rational_equivalence_left :
    ∀ {a b c}, RationalEquivalence X a b → RationalEquivalence X (product a c) (product b c)
  respects_rational_equivalence_right :
    ∀ {a b c}, RationalEquivalence X a b → RationalEquivalence X (product c a) (product c b)

end SchemeOverQ
end Wall10A
end ClassicalPeriods
end TraceCalc
