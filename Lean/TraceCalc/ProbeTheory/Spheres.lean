import TraceCalc.ProbeTheory.Basic

universe u v w

namespace TraceCalc
namespace ProbeTheory

/-- Bigraded motivic sphere index S^{topologicalDegree, weightDegree}. -/
structure MotivicSphereIndex where
  topologicalDegree : Int
  weightDegree : Int
  deriving DecidableEq, Repr

namespace MotivicSphereIndex

def shift (n : Int) (idx : MotivicSphereIndex) : MotivicSphereIndex where
  topologicalDegree := idx.topologicalDegree + n
  weightDegree := idx.weightDegree

def twist (n : Int) (idx : MotivicSphereIndex) : MotivicSphereIndex where
  topologicalDegree := idx.topologicalDegree
  weightDegree := idx.weightDegree + n

def tensorDegree (left right : MotivicSphereIndex) : MotivicSphereIndex where
  topologicalDegree := left.topologicalDegree + right.topologicalDegree
  weightDegree := left.weightDegree + right.weightDegree

end MotivicSphereIndex

/-- Sphere objects and proof-relevant compatibility morphisms.  The laws are
kept as data because this package is an abstract probe-theoretic layer. -/
structure TateSphereData (C : CategoryLike.{u, v}) where
  sphere : MotivicSphereIndex -> C.Obj
  shiftMap : (idx : MotivicSphereIndex) -> (n : Int) ->
    C.Hom (sphere idx) (sphere (MotivicSphereIndex.shift n idx))
  tensorMap : (left right : MotivicSphereIndex) ->
    C.Hom (sphere left) (sphere (MotivicSphereIndex.tensorDegree left right))
  tateTwistMap : (idx : MotivicSphereIndex) -> (n : Int) ->
    C.Hom (sphere idx) (sphere (MotivicSphereIndex.twist n idx))
  ShiftCompatibilityRelation :
    (idx : MotivicSphereIndex) -> (m n : Int) ->
      C.Hom (sphere idx) (sphere (MotivicSphereIndex.shift n (MotivicSphereIndex.shift m idx))) -> Prop
  shiftCompatibility :
    (idx : MotivicSphereIndex) -> (m n : Int) ->
      ShiftCompatibilityRelation idx m n
        (C.comp (shiftMap idx m) (shiftMap (MotivicSphereIndex.shift m idx) n))
  TensorCompatibilityRelation :
    (left right : MotivicSphereIndex) ->
      C.Hom (sphere left) (sphere (MotivicSphereIndex.shift 0 (MotivicSphereIndex.tensorDegree left right))) -> Prop
  tensorCompatibility :
    (left right : MotivicSphereIndex) ->
      TensorCompatibilityRelation left right
        (C.comp (tensorMap left right)
          (shiftMap (MotivicSphereIndex.tensorDegree left right) 0))
  TateTwistCompatibilityRelation :
    (idx : MotivicSphereIndex) -> (m n : Int) ->
      C.Hom (sphere idx) (sphere (MotivicSphereIndex.twist n (MotivicSphereIndex.twist m idx))) -> Prop
  tateTwistCompatibility :
    (idx : MotivicSphereIndex) -> (m n : Int) ->
      TateTwistCompatibilityRelation idx m n
        (C.comp (tateTwistMap idx m) (tateTwistMap (MotivicSphereIndex.twist m idx) n))

/-- The probe family represented by all Tate spheres. -/
def TateSphereProbeFamily
    (C : CategoryLike.{u, v})
    (S : TateSphereData C) :
    ProbeFamily.{u, v, 0} C where
  ProbeIndex := MotivicSphereIndex
  probe := S.sphere

namespace TateSphereData

variable {C : CategoryLike.{u, v}}
variable (S : TateSphereData C)

theorem tensor_shift_zero_compatible (left right : MotivicSphereIndex) :
    S.TensorCompatibilityRelation left right
      (C.comp (S.tensorMap left right)
        (S.shiftMap (MotivicSphereIndex.tensorDegree left right) 0)) :=
  S.tensorCompatibility left right

end TateSphereData

end ProbeTheory
end TraceCalc
