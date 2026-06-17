import Boundary.LFunctions.ZetaCompletedFinitePart

/-!
# Completed boundary weight streams

This file owns the finite completed boundary weight stream and its positive-cone
bookkeeping. Downstream GNS and ordered-heart layers consume this API.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- A completed boundary weight stream is a stream of finite weight objects together with the
real scalar realized by its finite-part representatives. -/
structure CompletedBoundaryWeightStream where
  source : ZetaAdmissibleFunction
  object : ℕ → FiniteBoundaryWeightObject
  scalar : ℝ
  scalar_eq_completedBoundaryChannel :
    scalar =
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation source))
  finitePart_tendsto_scalar :
    Tendsto
      (fun N : ℕ =>
        FiniteBoundaryWeightObject.finitePartRepresentative (object N))
      atTop
      (𝓝 scalar)

namespace CompletedBoundaryWeightStream

/-- A completed boundary weight stream has pointwise nonnegative square representatives. -/
def SquareRepresentativesNonnegative
    (X : CompletedBoundaryWeightStream) : Prop :=
  ∀ N : ℕ, 0 ≤ FiniteBoundaryWeightObject.squareRepresentative (X.object N)

/-- A completed boundary weight stream has pointwise lower-weight absorption certificates. -/
def HasLowerWeightAbsorption
    (X : CompletedBoundaryWeightStream) : Prop :=
  ∀ N : ℕ, FiniteBoundaryLowerWeightAbsorptionCert (X.object N)

/-- The completed positive cone in the ordered heart: positivity means having square-positive
finite representatives together with lower-weight absorption certificates. -/
def InPositiveCone
    (X : CompletedBoundaryWeightStream) : Prop :=
  SquareRepresentativesNonnegative X ∧ HasLowerWeightAbsorption X

/-- Positive-cone membership supplies pointwise lower-weight exactness. -/
theorem lowerWeightExactRepresentative_eq_zero_of_inPositiveCone
    {X : CompletedBoundaryWeightStream}
    (hX : InPositiveCone X)
    (N : ℕ) :
    FiniteBoundaryWeightObject.lowerWeightExactRepresentative (X.object N) = 0 := by
  exact
    FiniteBoundaryLowerWeightAbsorptionCert.lowerWeightExactRepresentative_eq_zero
      (hX.2 N)

/-- Positive-cone membership supplies the pointwise weight-triangular transport identity. -/
theorem weightTriangularTransport_of_inPositiveCone
    {X : CompletedBoundaryWeightStream}
    (hX : InPositiveCone X)
    (N : ℕ) :
    FiniteBoundaryWeightObject.squareRepresentative (X.object N) +
        (X.object N).debtAbsorption =
      FiniteBoundaryWeightObject.finitePartRepresentative (X.object N) := by
  exact
    FiniteBoundaryLowerWeightAbsorptionCert.weightTriangularTransport
      (hX.2 N)

end CompletedBoundaryWeightStream

/-- The completed boundary weight stream attached to an admissible seed. -/
def completedBoundaryWeightStream
    (f : ZetaAdmissibleFunction) : CompletedBoundaryWeightStream :=
  { source := f
    object := fun N : ℕ => finiteBoundaryWeightObject N f
    scalar := Complex.re (completedBoundaryChannel (convolutionAutocorrelation f))
    scalar_eq_completedBoundaryChannel := rfl
    finitePart_tendsto_scalar := by
      have hfinite :
          Tendsto
            (fun N : ℕ => finitePartBoundaryWindow N f)
            atTop
            (𝓝 (Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)))) :=
        finitePartBoundaryWindow_tendsto_boundaryChannel f
      have hobject :
          (fun N : ℕ =>
            FiniteBoundaryWeightObject.finitePartRepresentative
              (finiteBoundaryWeightObject N f)) =
            (fun N : ℕ => finitePartBoundaryWindow N f) := by
        funext N
        exact finiteBoundaryWeightObject_finitePartRepresentative_eq_finitePartBoundaryWindow
          N f
      exact Eq.subst
        (motive := fun u : ℕ → ℝ =>
          Tendsto u atTop
            (𝓝 (Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)))))
        hobject.symm
        hfinite }

/-- The completed boundary weight stream has nonnegative square representatives. -/
theorem completedBoundaryWeightStream_squareRepresentatives_nonnegative
    (f : ZetaAdmissibleFunction) :
    CompletedBoundaryWeightStream.SquareRepresentativesNonnegative
      (completedBoundaryWeightStream f) := by
  intro N
  exact finiteBoundaryWeightObject_squareRepresentative_nonnegative N f

/-- The completed boundary weight stream has the pointwise lower-weight absorption
certificates. -/
theorem completedBoundaryWeightStream_hasLowerWeightAbsorption
    (f : ZetaAdmissibleFunction) :
    CompletedBoundaryWeightStream.HasLowerWeightAbsorption
      (completedBoundaryWeightStream f) := by
  intro N
  exact finiteBoundaryWeightObject_lowerWeightAbsorptionCert N f

/-- The completed boundary weight stream lies in the completed positive cone. -/
theorem completedBoundaryWeightStream_mem_positiveCone
    (f : ZetaAdmissibleFunction) :
    CompletedBoundaryWeightStream.InPositiveCone
      (completedBoundaryWeightStream f) := by
  exact
    ⟨completedBoundaryWeightStream_squareRepresentatives_nonnegative f,
      completedBoundaryWeightStream_hasLowerWeightAbsorption f⟩

/-- The concrete completed boundary weight stream has pointwise lower-weight exact
representatives. -/
theorem completedBoundaryWeightStream_lowerWeightExactRepresentative_eq_zero
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    FiniteBoundaryWeightObject.lowerWeightExactRepresentative
        ((completedBoundaryWeightStream f).object N) =
      0 := by
  exact
    CompletedBoundaryWeightStream.lowerWeightExactRepresentative_eq_zero_of_inPositiveCone
      (completedBoundaryWeightStream_mem_positiveCone f)
      N

/-- The concrete completed boundary weight stream satisfies weight-triangular transport
pointwise. -/
theorem completedBoundaryWeightStream_weightTriangularTransport
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    FiniteBoundaryWeightObject.squareRepresentative
        ((completedBoundaryWeightStream f).object N) +
      ((completedBoundaryWeightStream f).object N).debtAbsorption =
    FiniteBoundaryWeightObject.finitePartRepresentative
        ((completedBoundaryWeightStream f).object N) := by
  exact
    CompletedBoundaryWeightStream.weightTriangularTransport_of_inPositiveCone
      (completedBoundaryWeightStream_mem_positiveCone f)
      N

/-- The scalar of the completed boundary weight stream is the real completed boundary channel. -/
theorem completedBoundaryWeightStream_scalar_eq_boundaryChannel_re
    (f : ZetaAdmissibleFunction) :
    (completedBoundaryWeightStream f).scalar =
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) := by
  rfl

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
