import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.LinearTransfers.ContourCorQInput.Presheaves.Accessors.Owner

/-!
# Rational-linear value data for `ContourCor_Q` presheaves

This owner records explicit rational-linear operations on each value of a
`ContourCor_Q` presheaf.  It is value-level data; transfer preservation belongs
downstream.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Rational-linear operations and laws on the values of a `ContourCor_Q` presheaf. -/
structure ContourCorQPresheafLinearValues
    (F : ContourCorQPresheaf) where
  zero :
    (X : ContourCorQPresheafObject) → F.valueAt X
  add :
    (X : ContourCorQPresheafObject) →
      F.valueAt X → F.valueAt X → F.valueAt X
  neg :
    (X : ContourCorQPresheafObject) →
      F.valueAt X → F.valueAt X
  scale :
    (X : ContourCorQPresheafObject) →
      Rat → F.valueAt X → F.valueAt X
  add_comm :
    (X : ContourCorQPresheafObject) →
      (a b : F.valueAt X) →
        add X a b = add X b a
  add_assoc :
    (X : ContourCorQPresheafObject) →
      (a b c : F.valueAt X) →
        add X (add X a b) c = add X a (add X b c)
  zero_add :
    (X : ContourCorQPresheafObject) →
      (a : F.valueAt X) →
        add X (zero X) a = a
  add_zero :
    (X : ContourCorQPresheafObject) →
      (a : F.valueAt X) →
        add X a (zero X) = a
  add_left_neg :
    (X : ContourCorQPresheafObject) →
      (a : F.valueAt X) →
        add X (neg X a) a = zero X
  one_scale :
    (X : ContourCorQPresheafObject) →
      (a : F.valueAt X) →
        scale X 1 a = a
  scale_add :
    (X : ContourCorQPresheafObject) →
      (q : Rat) →
        (a b : F.valueAt X) →
          scale X q (add X a b) = add X (scale X q a) (scale X q b)

namespace ContourCorQPresheafLinearValues

/-- The zero value at an object. -/
def zeroAt {F : ContourCorQPresheaf}
    (L : ContourCorQPresheafLinearValues F)
    (X : ContourCorQPresheafObject) :
    F.valueAt X :=
  L.zero X

/-- Addition in the value over an object. -/
def addAt {F : ContourCorQPresheaf}
    (L : ContourCorQPresheafLinearValues F)
    (X : ContourCorQPresheafObject)
    (a b : F.valueAt X) :
    F.valueAt X :=
  L.add X a b

/-- Rational scaling in the value over an object. -/
def scaleAt {F : ContourCorQPresheaf}
    (L : ContourCorQPresheafLinearValues F)
    (X : ContourCorQPresheafObject)
    (q : Rat) (a : F.valueAt X) :
    F.valueAt X :=
  L.scale X q a

/-- Additive commutativity in one value. -/
theorem add_comm_eq {F : ContourCorQPresheaf}
    (L : ContourCorQPresheafLinearValues F)
    (X : ContourCorQPresheafObject)
    (a b : F.valueAt X) :
    L.addAt X a b = L.addAt X b a :=
  L.add_comm X a b

/-- Rational scaling distributes over addition in one value. -/
theorem scale_add_eq {F : ContourCorQPresheaf}
    (L : ContourCorQPresheafLinearValues F)
    (X : ContourCorQPresheafObject)
    (q : Rat) (a b : F.valueAt X) :
    L.scaleAt X q (L.addAt X a b) =
      L.addAt X (L.scaleAt X q a) (L.scaleAt X q b) :=
  L.scale_add X q a b

end ContourCorQPresheafLinearValues

end AnalyticMotives
end LFunctions
end Boundary
