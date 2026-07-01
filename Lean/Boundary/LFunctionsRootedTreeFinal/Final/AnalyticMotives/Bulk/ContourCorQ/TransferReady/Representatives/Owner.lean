import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.TransferReady.Homs.Owner

/-!
# Representative reductions for transfer-ready homs

This owner records how public `ContourCorQHom` operations reduce on explicit
balanced representatives.  These reductions keep downstream category and
presheaf files from reaching into the balancing implementation.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The public zero hom is the balanced class of the empty formal sum. -/
theorem ContourCorQHom.zero_eq_balancedClass
    (X Y : ContourCorQObject) :
    ContourCorQHom.zero X Y =
      ContourCorQFormalSum.balancedClass
        (ContourCorQFormalSum.zero X Y) :=
  rfl

/-- The public single hom is the balanced class of the single formal sum. -/
theorem ContourCorQHom.single_eq_balancedClass {X Y : ContourCorQObject}
    (f : ContourCorQRawHom X Y) :
    ContourCorQHom.single f =
      ContourCorQFormalSum.balancedClass
        (ContourCorQFormalSum.single f) :=
  rfl

/-- The public term hom is the balanced class of the one-term formal sum. -/
theorem ContourCorQHom.term_eq_balancedClass {X Y : ContourCorQObject}
    (q : Rat) (f : ContourCorQRawHom X Y) :
    ContourCorQHom.term q f =
      ContourCorQFormalSum.balancedClass
        (ContourCorQFormalSum.term q f) :=
  rfl

/-- Public addition reduces to balanced quotient addition. -/
theorem ContourCorQHom.add_eq_balancedAddClass {X Y : ContourCorQObject}
    (F G : ContourCorQHom X Y) :
    ContourCorQHom.add F G =
      ContourCorQFormalSum.balancedAddClass F G :=
  rfl

/-- Public scaling reduces to balanced quotient scaling. -/
theorem ContourCorQHom.scale_eq_balancedScaleClass {X Y : ContourCorQObject}
    (q : Rat) (F : ContourCorQHom X Y) :
    ContourCorQHom.scale q F =
      ContourCorQFormalSum.balancedScaleClass q F :=
  rfl

/-- Public negation reduces to balanced quotient negation. -/
theorem ContourCorQHom.neg_eq_balancedNegClass {X Y : ContourCorQObject}
    (F : ContourCorQHom X Y) :
    ContourCorQHom.neg F =
      ContourCorQFormalSum.balancedNegClass F :=
  rfl

/-- Public subtraction reduces to balanced quotient subtraction. -/
theorem ContourCorQHom.sub_eq_balancedSubClass {X Y : ContourCorQObject}
    (F G : ContourCorQHom X Y) :
    ContourCorQHom.sub F G =
      ContourCorQFormalSum.balancedSubClass F G :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
