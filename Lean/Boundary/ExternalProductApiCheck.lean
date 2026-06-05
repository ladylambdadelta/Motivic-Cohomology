import Boundary.CompositionCategory
import Boundary.PrimeSupport
import Boundary.ExternalProduct
import Geometry.Cycles.Components

universe u

variable {k : Type u} [Field k] [PerfectField k]

open AlgebraicGeometry CategoryTheory Limits

namespace Boundary

#check RepresentedPrimeSupport
#check PrimeFiniteCorrespondenceSupport.sourceComponent
#check PrimeFiniteCorrespondenceSupport.toSourceComponent

#check SourceIrreducibleComponent
#check SourceIrreducibleComponent.diagonalRepresentedPrimeSupport
#check SourceIrreducibleComponent.IsoOverAmbient
#check SourceIrreducibleComponent.toAmbient
#check SourceIrreducibleComponent.toAmbient_overBase

#check product_of_integral_diagonal_source_is_integral
#check product_diagonal_sourceImage_is_diagonal_sourceImage
#check sourceComponent_product_diagonal

end Boundary
