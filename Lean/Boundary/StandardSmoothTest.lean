import Boundary.PolynomialSmoothness.StandardSmoothPolynomial

universe u
namespace Boundary

#check (inferInstance : RingHom.IsStandardSmoothOfRelativeDimension 0 (algebraMap ℤ (MvPolynomial (Fin 0) ℤ))
)
#check (inferInstance : RingHom.IsStandardSmoothOfRelativeDimension 1 (algebraMap ℤ (MvPolynomial (Fin 1) ℤ)))
#check (inferInstance : RingHom.IsStandardSmoothOfRelativeDimension 2 (algebraMap ℤ (MvPolynomial (Fin 2) ℤ)))
#check (inferInstance : Algebra.IsStandardSmoothOfRelativeDimension 1 ℤ (Polynomial ℤ))

end Boundary
