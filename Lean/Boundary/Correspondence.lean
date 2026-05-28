import Boundary.Basic
import Boundary.SmOver
import Boundary.PrimeSupport
import Boundary.SupportEquivalence
import Boundary.CorrespondenceSums
import Boundary.CorrespondenceRationalization
import Boundary.RationalCompositionCategory
import Boundary.PresheavesWithTransfers
import Boundary.Localization
import Boundary.NisnevichDescent
import Boundary.A1Invariance
import Boundary.MinimalPresentationPackage
import Boundary.OpenClosedLocalization
import Boundary.TateStabilization
import Boundary.InternalPresentationPackage
import Boundary.GeometricRecognition
import Boundary.Diagonal
import Boundary.DiagonalDecomposition
import Boundary.CompositionCategory
import Boundary.CompositionGeometry
import Boundary.RepresentedPrimeComposition
import Boundary.BoundaryFormula
import Boundary.NormalizationBoundaryStratum
import Boundary.NormalizationBoundaryModel
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Data.Finsupp.Basic
import Mathlib.Topology.Irreducible

/-!
# Boundary Correspondence Umbrella

This file is the umbrella import for the boundary-correspondence layer. The
actual owners now live in the split modules for raw prime supports,
support-equivalence, correspondence sums, diagonals, diagonal decompositions,
composition data, and the downstream boundary formulas.
-/

universe u

variable {k : Type u} [Field k] [PerfectField k]

open AlgebraicGeometry CategoryTheory Limits

namespace Boundary

noncomputable section




end

end Boundary
