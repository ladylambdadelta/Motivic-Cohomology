import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.LinearTransfers.ContourCorQInput.Presheaves.LinearValues.Owner

/-!
# Rational-linear pullback laws for `ContourCor_Q` presheaves

This owner records that transfer pullbacks preserve the rational-linear
operations on presheaf values.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Pullbacks preserve rational-linear value operations. -/
structure ContourCorQPresheafLinearPullback
    {F : ContourCorQPresheaf}
    (L : ContourCorQPresheafLinearValues F) where
  map_zero :
    {X Y : ContourCorQPresheafObject} →
      (f : ContourCorQPresheafHom X Y) →
        F.pullbackAlong f (L.zeroAt Y) = L.zeroAt X
  map_add :
    {X Y : ContourCorQPresheafObject} →
      (f : ContourCorQPresheafHom X Y) →
        (a b : F.valueAt Y) →
          F.pullbackAlong f (L.addAt Y a b) =
            L.addAt X (F.pullbackAlong f a) (F.pullbackAlong f b)
  map_neg :
    {X Y : ContourCorQPresheafObject} →
      (f : ContourCorQPresheafHom X Y) →
        (a : F.valueAt Y) →
          F.pullbackAlong f (L.neg Y a) =
            L.neg X (F.pullbackAlong f a)
  map_scale :
    {X Y : ContourCorQPresheafObject} →
      (f : ContourCorQPresheafHom X Y) →
        (q : Rat) →
          (a : F.valueAt Y) →
            F.pullbackAlong f (L.scaleAt Y q a) =
              L.scaleAt X q (F.pullbackAlong f a)

namespace ContourCorQPresheafLinearPullback

/-- Pullback preserves zero values. -/
theorem map_zero_eq {F : ContourCorQPresheaf}
    {L : ContourCorQPresheafLinearValues F}
    (P : ContourCorQPresheafLinearPullback L)
    {X Y : ContourCorQPresheafObject}
    (f : ContourCorQPresheafHom X Y) :
    F.pullbackAlong f (L.zeroAt Y) = L.zeroAt X :=
  P.map_zero f

/-- Pullback preserves value addition. -/
theorem map_add_eq {F : ContourCorQPresheaf}
    {L : ContourCorQPresheafLinearValues F}
    (P : ContourCorQPresheafLinearPullback L)
    {X Y : ContourCorQPresheafObject}
    (f : ContourCorQPresheafHom X Y)
    (a b : F.valueAt Y) :
    F.pullbackAlong f (L.addAt Y a b) =
      L.addAt X (F.pullbackAlong f a) (F.pullbackAlong f b) :=
  P.map_add f a b

/-- Pullback preserves rational scaling. -/
theorem map_scale_eq {F : ContourCorQPresheaf}
    {L : ContourCorQPresheafLinearValues F}
    (P : ContourCorQPresheafLinearPullback L)
    {X Y : ContourCorQPresheafObject}
    (f : ContourCorQPresheafHom X Y)
    (q : Rat) (a : F.valueAt Y) :
    F.pullbackAlong f (L.scaleAt Y q a) =
      L.scaleAt X q (F.pullbackAlong f a) :=
  P.map_scale f q a

end ContourCorQPresheafLinearPullback

end AnalyticMotives
end LFunctions
end Boundary
