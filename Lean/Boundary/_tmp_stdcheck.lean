import Boundary.PolynomialSmoothness.StandardSmoothDimensionZero
import Mathlib.RingTheory.Smooth.StandardSmooth
import Boundary.PolynomialSmoothness.JacobianTransport

#check (inferInstance : Algebra.IsStandardSmoothOfRelativeDimension 1 (MvPolynomial (Fin 1) ℤ) (MvPolynomial (Fin 1) ℤ))
#check (inferInstance : Algebra.IsStandardSmoothOfRelativeDimension 2 (MvPolynomial (Fin 1) ℤ) (MvPolynomial (Fin 2) (MvPolynomial (Fin 1) ℤ)))
#check (inferInstance : Algebra.IsStandardSmoothOfRelativeDimension 3 ℤ (MvPolynomial (Fin 3) ℤ))
#check (inferInstance : Algebra.IsStandardSmooth ℤ (MvPolynomial (Fin 4) ℤ))
#check (inferInstance : RingHom.IsStandardSmoothOfRelativeDimension 1 (algebraMap ℤ (MvPolynomial (Fin 1) ℤ)))
#check (inferInstance : RingHom.IsStandardSmooth (algebraMap ℤ (MvPolynomial (Fin 1) ℤ)))
#check (inferInstance : Algebra.IsStandardSmoothOfRelativeDimension 1 ℤ (Polynomial ℤ))
#check (inferInstance : RingHom.IsStandardSmoothOfRelativeDimension 1 (algebraMap ℤ (Polynomial ℤ)))
