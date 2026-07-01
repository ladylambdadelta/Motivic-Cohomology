import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.LinearTransfers.ContourCorQInput.Operations.Owner

/-!
# Laws for the `ContourCor_Q` presheaf input

This owner exposes additive and rational-term laws for presheaf-input homs.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Presheaf-input hom addition is commutative. -/
theorem ContourCorQPresheafHom.add_comm
    {X Y : ContourCorQPresheafObject}
    (F G : ContourCorQPresheafHom X Y) :
    ContourCorQPresheafHom.add F G =
      ContourCorQPresheafHom.add G F :=
  ContourCorQHom.add_comm F G

/-- Presheaf-input hom addition is associative. -/
theorem ContourCorQPresheafHom.add_assoc
    {X Y : ContourCorQPresheafObject}
    (F G H : ContourCorQPresheafHom X Y) :
    ContourCorQPresheafHom.add (ContourCorQPresheafHom.add F G) H =
      ContourCorQPresheafHom.add F (ContourCorQPresheafHom.add G H) :=
  ContourCorQHom.add_assoc F G H

/-- The zero presheaf-input hom is a left identity for addition. -/
theorem ContourCorQPresheafHom.zero_add
    {X Y : ContourCorQPresheafObject}
    (F : ContourCorQPresheafHom X Y) :
    ContourCorQPresheafHom.add (ContourCorQPresheafHom.zero X Y) F = F :=
  ContourCorQHom.zero_add F

/-- The zero presheaf-input hom is a right identity for addition. -/
theorem ContourCorQPresheafHom.add_zero
    {X Y : ContourCorQPresheafObject}
    (F : ContourCorQPresheafHom X Y) :
    ContourCorQPresheafHom.add F (ContourCorQPresheafHom.zero X Y) = F :=
  ContourCorQHom.add_zero F

/-- A zero coefficient presheaf-input term is the zero hom. -/
theorem ContourCorQPresheafHom.term_zero_coeff
    {X Y : ContourCorQPresheafObject}
    (f : ContourCorQRawHom X Y) :
    ContourCorQPresheafHom.term 0 f =
      ContourCorQPresheafHom.zero X Y :=
  ContourCorQHom.term_zero_coeff f

/-- Equal raw correspondences collect coefficients in presheaf-input homs. -/
theorem ContourCorQPresheafHom.term_collect
    {X Y : ContourCorQPresheafObject}
    (q r : Rat) (f : ContourCorQRawHom X Y) :
    ContourCorQPresheafHom.add
        (ContourCorQPresheafHom.term q f)
        (ContourCorQPresheafHom.term r f) =
      ContourCorQPresheafHom.term (q + r) f :=
  ContourCorQHom.term_collect q r f

/-- Scaling a one-term presheaf-input hom scales its coefficient. -/
theorem ContourCorQPresheafHom.scale_term
    {X Y : ContourCorQPresheafObject}
    (p q : Rat) (f : ContourCorQRawHom X Y) :
    ContourCorQPresheafHom.scale p (ContourCorQPresheafHom.term q f) =
      ContourCorQPresheafHom.term (p * q) f :=
  ContourCorQHom.scale_term p q f

end AnalyticMotives
end LFunctions
end Boundary
