import TraceCalc.ClassicalPeriods.CycleOperations

noncomputable section

namespace TraceCalc
namespace ClassicalPeriods
namespace Wall10A

namespace SchemeOverQ

structure CycleOperationLawData where
  pushforward_comp :
    ∀ {X Y Z : SchemeOverQ} (f : Hom X Y) (g : Hom Y Z)
      (F : ProperPushforwardData f) (G : ProperPushforwardData g)
      (GF : ProperPushforwardData (comp f g)),
      GF.map.toFun = (CycleMap.comp F.map G.map).toFun
  pullback_comp :
    ∀ {X Y Z : SchemeOverQ} (f : Hom X Y) (g : Hom Y Z)
      (F : FlatPullbackData f) (G : FlatPullbackData g)
      (GF : FlatPullbackData (comp f g)),
      GF.map.toFun = (CycleMap.comp G.map F.map).toFun
  projection_formula :
    ∀ {X Y : SchemeOverQ} (f : Hom X Y)
      (F : ProperPushforwardData f) (P : FlatPullbackData f)
      (IX : IntersectionProductData X) (IY : IntersectionProductData Y), Prop
  base_change :
    ∀ {X Y X' Y' : SchemeOverQ} (f : Hom X Y) (g : Hom X' Y')
      (square_top : Hom X' X) (square_bottom : Hom Y' Y), Prop

namespace CycleOperationLawData

theorem pushforward_comp_apply (laws : CycleOperationLawData)
  {X Y Z : SchemeOverQ} (f : Hom X Y) (g : Hom Y Z)
    (F : ProperPushforwardData f) (G : ProperPushforwardData g)
    (GF : ProperPushforwardData (comp f g)) (a : AlgebraicCycle X) :
    GF.map.toFun a = G.map.toFun (F.map.toFun a) := by
  have h := CycleOperationLawData.pushforward_comp laws f g F G GF
  exact congrFun h a

theorem pullback_comp_apply (laws : CycleOperationLawData)
  {X Y Z : SchemeOverQ} (f : Hom X Y) (g : Hom Y Z)
    (F : FlatPullbackData f) (G : FlatPullbackData g)
    (GF : FlatPullbackData (comp f g)) (a : AlgebraicCycle Z) :
    GF.map.toFun a = F.map.toFun (G.map.toFun a) := by
  have h := CycleOperationLawData.pullback_comp laws f g F G GF
  exact congrFun h a

end CycleOperationLawData
end SchemeOverQ
end Wall10A
end ClassicalPeriods
end TraceCalc
