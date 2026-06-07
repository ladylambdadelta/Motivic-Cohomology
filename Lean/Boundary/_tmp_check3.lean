import Boundary.PolynomialSmoothness.StandardSmoothDimensionZero

universe u
namespace Boundary
namespace _root_.Algebra

variable (A : Type u) [CommRing A]
#check (inferInstance : Algebra.IsStandardSmoothOfRelativeDimension 1 A (MvPolynomial (Fin 1) A))
#check (inferInstance : Algebra.IsStandardSmoothOfRelativeDimension 2 A (MvPolynomial (Fin 2) A))

end _root_.Algebra
end Boundary
