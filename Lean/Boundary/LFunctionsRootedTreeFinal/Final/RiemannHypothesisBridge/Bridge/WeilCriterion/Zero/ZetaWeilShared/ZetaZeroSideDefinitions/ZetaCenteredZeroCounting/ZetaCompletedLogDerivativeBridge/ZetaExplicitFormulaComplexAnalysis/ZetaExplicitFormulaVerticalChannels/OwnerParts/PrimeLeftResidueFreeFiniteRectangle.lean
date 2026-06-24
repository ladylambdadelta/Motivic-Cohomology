import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part34
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffineVerticalKernels
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.OrientationAlgebra
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeScheduledChannels

/-!
# Prime-left residue-free finite rectangle bridge

This file owns the first finite-height input to the left prime residue-free
contour proof.  It deliberately stops at the finite punctured-rectangle
Cauchy-Goursat identity; horizontal decay, excision decay, and whole-line
exhaustion are separate owner steps.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Finite-hole Cauchy-Goursat zero value for the tangent punctured rectangle,
renamed at the prime-left residue-free owner level.

This theorem is the exact finite-rectangle input for the later left-prime
boundary decomposition.  It does not identify the boundary pieces with the
left affine logarithmic-derivative kernel and does not assert any limiting
decay. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_tangentPuncturedRectangleIntegral_eq_zero_ownerFiniteRectangle
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) {T : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z) :
    ∀ ε : ℝ,
      0 < ε →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            ∀ b : ℂ,
              b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a ≠ b → ε + ε < dist a b) →
          explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral
            f F T ε = 0 :=
  explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_ownerGridSubdivision
    f F h hT hinterior hboundary

/-- Finite-radius prime-left residue-free rectangle identity after unfolding
the punctured boundary into the outer tangent rectangle and deleted-circle
excision boundary.

This is the finite-height source for the later scheduled identity
`left + horizontal + excision = 0`; it still deliberately stops before any
horizontal or excision decay theorem. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_tangentContour_sub_rawDeletedCircleBoundarySum_eq_zero_ownerFiniteRectangle
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) {T : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z) :
    ∀ ε : ℝ,
      0 < ε →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            ∀ b : ℂ,
              b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a ≠ b → ε + ε < dist a b) →
          zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
            explicitFormulaRectangleRawDeletedCircleBoundarySum f T ε = 0 := by
  intro ε hε hclosed hsep
  have hpunctured :
      explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral
        f F T ε = 0 :=
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_tangentPuncturedRectangleIntegral_eq_zero_ownerFiniteRectangle
      f F h hT hinterior hboundary ε hε hclosed hsep
  have hunfold :
      explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral
        f F T ε =
        zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
          explicitFormulaRectangleRawDeletedCircleBoundarySum f T ε :=
    explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_tangentContour_sub_rawDeletedCircleBoundarySum
      f F T ε
  exact Eq.trans hunfold.symm hpunctured

/-- The finite horizontal/right completed-log-derivative boundary error left
after isolating the left tangent side of the residue-free rectangle. -/
noncomputable def zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteHorizontalRightError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    ℂ :=
  (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) *
      Complex.I) +
    (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
      zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T))

/-- The finite deleted-circle excision error with the sign used by the
left-window boundary sum. -/
noncomputable def zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteExcisionError
    (f : ZetaAdmissibleFunction) (T ε : ℝ) : ℂ :=
  -explicitFormulaRectangleRawDeletedCircleBoundarySum f T ε

/-- Finite-radius prime-left residue-free rectangle identity with the
tangent-oriented left vertical side isolated first.

This is the finite algebraic precursor to the scheduled identity consumed by
`PrimeLeftResidueFreeContourIdentity`: the remaining analytic steps identify
`-(left * I)` with the left prime affine window and prove decay for the
grouped horizontal/right/excision terms. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_leftTangent_add_horizontalRight_sub_excision_eq_zero_ownerFiniteRectangle
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) {T : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z) :
    ∀ ε : ℝ,
      0 < ε →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            ∀ b : ℂ,
              b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a ≠ b → ε + ε < dist a b) →
          (-(zetaCompletedExplicitFormulaLeftLineIntegral
                f (F.rectangle T) * Complex.I)) +
              ((zetaCompletedExplicitFormulaRightLineIntegral
                  f (F.rectangle T) * Complex.I) +
                (zetaCompletedExplicitFormulaTopLineIntegral
                    f (F.rectangle T) -
                  zetaCompletedExplicitFormulaBottomLineIntegral
                    f (F.rectangle T))) -
            explicitFormulaRectangleRawDeletedCircleBoundarySum f T ε = 0 := by
  intro ε hε hclosed hsep
  have hboundary_zero :
      zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
        explicitFormulaRectangleRawDeletedCircleBoundarySum f T ε = 0 :=
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_tangentContour_sub_rawDeletedCircleBoundarySum_eq_zero_ownerFiniteRectangle
      f F h hT hinterior hboundary ε hε hclosed hsep
  have htangent :
      (zetaCompletedExplicitFormulaRightLineIntegral
          f (F.rectangle T) * Complex.I -
          zetaCompletedExplicitFormulaLeftLineIntegral
            f (F.rectangle T) * Complex.I +
          (zetaCompletedExplicitFormulaTopLineIntegral
              f (F.rectangle T) -
            zetaCompletedExplicitFormulaBottomLineIntegral
              f (F.rectangle T))) -
        explicitFormulaRectangleRawDeletedCircleBoundarySum f T ε = 0 := by
    have hunfold :
        zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) =
          zetaCompletedExplicitFormulaRightLineIntegral
              f (F.rectangle T) * Complex.I -
            zetaCompletedExplicitFormulaLeftLineIntegral
              f (F.rectangle T) * Complex.I +
            zetaCompletedExplicitFormulaTopLineIntegral
              f (F.rectangle T) -
            zetaCompletedExplicitFormulaBottomLineIntegral
              f (F.rectangle T) :=
      zetaCompletedExplicitFormulaTangentContourIntegral_eq f (F.rectangle T)
    have hsplit :
        zetaCompletedExplicitFormulaRightLineIntegral
              f (F.rectangle T) * Complex.I -
            zetaCompletedExplicitFormulaLeftLineIntegral
              f (F.rectangle T) * Complex.I +
            zetaCompletedExplicitFormulaTopLineIntegral
              f (F.rectangle T) -
            zetaCompletedExplicitFormulaBottomLineIntegral
              f (F.rectangle T) =
          zetaCompletedExplicitFormulaRightLineIntegral
              f (F.rectangle T) * Complex.I -
            zetaCompletedExplicitFormulaLeftLineIntegral
              f (F.rectangle T) * Complex.I +
            (zetaCompletedExplicitFormulaTopLineIntegral
                f (F.rectangle T) -
              zetaCompletedExplicitFormulaBottomLineIntegral
                f (F.rectangle T)) := by
      exact explicitFormula_tangent_four_side_split
        (zetaCompletedExplicitFormulaRightLineIntegral
          f (F.rectangle T) * Complex.I)
        (zetaCompletedExplicitFormulaLeftLineIntegral
          f (F.rectangle T) * Complex.I)
        (zetaCompletedExplicitFormulaTopLineIntegral
          f (F.rectangle T))
        (zetaCompletedExplicitFormulaBottomLineIntegral
          f (F.rectangle T))
    have hreplace :
        zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) =
          zetaCompletedExplicitFormulaRightLineIntegral
              f (F.rectangle T) * Complex.I -
            zetaCompletedExplicitFormulaLeftLineIntegral
              f (F.rectangle T) * Complex.I +
            (zetaCompletedExplicitFormulaTopLineIntegral
                f (F.rectangle T) -
              zetaCompletedExplicitFormulaBottomLineIntegral
                f (F.rectangle T)) :=
      Eq.trans hunfold hsplit
    exact Eq.trans
      (congrArg
        (fun z : ℂ =>
          z - explicitFormulaRectangleRawDeletedCircleBoundarySum f T ε)
        hreplace.symm)
      hboundary_zero
  exact
    explicitFormula_tangentBoundary_leftFirst_eq_zero_of_boundary_sub_excision_eq_zero
      (zetaCompletedExplicitFormulaRightLineIntegral
        f (F.rectangle T) * Complex.I)
      (zetaCompletedExplicitFormulaLeftLineIntegral
        f (F.rectangle T) * Complex.I)
      (zetaCompletedExplicitFormulaTopLineIntegral
          f (F.rectangle T) -
        zetaCompletedExplicitFormulaBottomLineIntegral
          f (F.rectangle T))
      (explicitFormulaRectangleRawDeletedCircleBoundarySum f T ε)
      htangent

/-- Finite-radius prime-left residue-free rectangle identity in the boundary
sum orientation consumed by the scheduled decay assembly: left tangent side
plus horizontal/right error plus deleted-circle excision error is zero. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_leftTangent_add_finiteErrors_eq_zero_ownerFiniteRectangle
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) {T : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z) :
    ∀ ε : ℝ,
      0 < ε →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            ∀ b : ℂ,
              b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a ≠ b → ε + ε < dist a b) →
          (-(zetaCompletedExplicitFormulaLeftLineIntegral
                f (F.rectangle T) * Complex.I)) +
            zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteHorizontalRightError
              f F T +
            zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteExcisionError
              f T ε = 0 := by
  intro ε hε hclosed hsep
  have hsub :
      (-(zetaCompletedExplicitFormulaLeftLineIntegral
            f (F.rectangle T) * Complex.I)) +
          ((zetaCompletedExplicitFormulaRightLineIntegral
              f (F.rectangle T) * Complex.I) +
            (zetaCompletedExplicitFormulaTopLineIntegral
                f (F.rectangle T) -
              zetaCompletedExplicitFormulaBottomLineIntegral
                f (F.rectangle T))) -
        explicitFormulaRectangleRawDeletedCircleBoundarySum f T ε = 0 :=
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_leftTangent_add_horizontalRight_sub_excision_eq_zero_ownerFiniteRectangle
      f F h hT hinterior hboundary ε hε hclosed hsep
  have hconvert :
      (-(zetaCompletedExplicitFormulaLeftLineIntegral
            f (F.rectangle T) * Complex.I)) +
          ((zetaCompletedExplicitFormulaRightLineIntegral
              f (F.rectangle T) * Complex.I) +
            (zetaCompletedExplicitFormulaTopLineIntegral
                f (F.rectangle T) -
              zetaCompletedExplicitFormulaBottomLineIntegral
                f (F.rectangle T))) +
        (-explicitFormulaRectangleRawDeletedCircleBoundarySum f T ε) =
      (-(zetaCompletedExplicitFormulaLeftLineIntegral
            f (F.rectangle T) * Complex.I)) +
          ((zetaCompletedExplicitFormulaRightLineIntegral
              f (F.rectangle T) * Complex.I) +
            (zetaCompletedExplicitFormulaTopLineIntegral
                f (F.rectangle T) -
              zetaCompletedExplicitFormulaBottomLineIntegral
                f (F.rectangle T))) -
        explicitFormulaRectangleRawDeletedCircleBoundarySum f T ε :=
    (sub_eq_add_neg
      ((-(zetaCompletedExplicitFormulaLeftLineIntegral
            f (F.rectangle T) * Complex.I)) +
          ((zetaCompletedExplicitFormulaRightLineIntegral
              f (F.rectangle T) * Complex.I) +
            (zetaCompletedExplicitFormulaTopLineIntegral
                f (F.rectangle T) -
              zetaCompletedExplicitFormulaBottomLineIntegral
                f (F.rectangle T))))
      (explicitFormulaRectangleRawDeletedCircleBoundarySum f T ε)).symm
  exact Eq.trans hconvert hsub

/-- Finite left completed-log-derivative line integral decomposes into the
left prime logarithmic-derivative window plus the left inverse-Gamma window,
assuming the two summands are integrable on the finite interval. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_leftIntegral_eq_prime_add_inverseGamma_of_integrableOn
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hprime :
      IntegrableOn
        (zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F)
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T))
    (hinverseGamma :
      IntegrableOn
        (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F)
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T)) :
    zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) =
      (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t) +
      (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t) := by
  let S : Set ℝ := Set.Icc (-(F.rectangle T).T) (F.rectangle T).T
  have hfun :
      (fun t : ℝ =>
        completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) =
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t +
          zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t) := by
    funext t
    have hpath :
        zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t =
          zetaCompletedExplicitFormulaLeftAffineLine F t :=
      zetaCompletedExplicitFormulaPrime_leftPath_eq_affineLine F T t
    have hshift :
        zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - (1 / 2 : ℂ) =
          zetaCompletedExplicitFormulaLeftCenteredAffineLine F t :=
      zetaCompletedExplicitFormulaPrime_shiftedLeftPath_eq_affineLine F T t
    have hcompleted_affine :
        completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) =
        completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t) := by
      calc
        completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) =
            completedZetaNegLogDeriv
              (zetaCompletedExplicitFormulaLeftAffineLine F t) *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) := by
          exact congrArg
            (fun z : ℂ =>
              completedZetaNegLogDeriv z *
                zetaCompletedExplicitFormulaPhi f
                  (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
            hpath
        _ =
            completedZetaNegLogDeriv
              (zetaCompletedExplicitFormulaLeftAffineLine F t) *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t) := by
          exact congrArg
            (fun z : ℂ =>
              completedZetaNegLogDeriv
                (zetaCompletedExplicitFormulaLeftAffineLine F t) *
                zetaCompletedExplicitFormulaPhi f z)
            hshift
    exact Eq.trans hcompleted_affine
      (zetaCompletedExplicitFormula_completedLeftAffineKernel_eq_prime_add_inverseGamma
        f F t)
  have hintegrand :
      zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) =
      ∫ t in S,
        zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t +
          zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t :=
    congrArg
      (fun φ : ℝ → ℂ => ∫ t in S, φ t)
      hfun
  have hadd :
      (∫ t in S,
        zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t +
          zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t) =
      (∫ t in S,
        zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t) +
      (∫ t in S,
        zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t) :=
    integral_add hprime hinverseGamma
  exact Eq.trans hintegrand hadd

/-- Finite-radius prime-left residue-free rectangle identity after the left
completed-log-derivative side has been decomposed into prime and inverse-Gamma
finite windows.

This theorem owns the sign and orientation conversion needed by the scheduled
residue-free proof.  It is useful when a caller has already supplied the
finite-window decomposition explicitly. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_primeLeft_add_finitePrimeErrors_eq_zero_of_leftIntegral_decomposition
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) {T : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hleft_decomp :
      zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) =
        (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
          zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t) +
        (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
          zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t)) :
    ∀ ε : ℝ,
      0 < ε →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            ∀ b : ℂ,
              b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a ≠ b → ε + ε < dist a b) →
          (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
            zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t) +
            ((∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
                zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t) +
              Complex.I *
                zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteHorizontalRightError
                  f F T) +
            Complex.I *
              zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteExcisionError
                f T ε = 0 := by
  intro ε hε hclosed hsep
  have hcompleted_boundary :
      (-(zetaCompletedExplicitFormulaLeftLineIntegral
            f (F.rectangle T) * Complex.I)) +
          zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteHorizontalRightError
            f F T +
          zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteExcisionError
            f T ε = 0 :=
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_leftTangent_add_finiteErrors_eq_zero_ownerFiniteRectangle
      f F h hT hinterior hboundary ε hε hclosed hsep
  exact
    explicitFormula_primeLeftBoundary_of_completedLeftBoundary
      (zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T))
      (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t)
      (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t)
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteHorizontalRightError
        f F T)
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteExcisionError
        f T ε)
      hleft_decomp
      hcompleted_boundary

/-- Finite-radius residue-free rectangle identity after both vertical
completed-log-derivative sides have been decomposed into their prime and
inverse-Gamma packets.

This is the honest two-sided boundary algebra: the right prime packet remains
visible as `primeLeft - primeRight`, and the inverse-Gamma error is the
difference `inverseGammaLeft - inverseGammaRight` rather than
`inverseGammaLeft - completedRight`. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_primeDifference_add_inverseGammaDifference_add_finiteErrors_eq_zero_of_vertical_decompositions
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) {T : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hleft_decomp :
      zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) =
        (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
          zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t) +
        (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
          zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t))
    (hright_decomp :
      zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) =
        (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
          zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t) +
        (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
          zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t)) :
    ∀ ε : ℝ,
      0 < ε →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            ∀ b : ℂ,
              b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a ≠ b → ε + ε < dist a b) →
          ((∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
              zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t) -
            ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
              zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t) +
            (((∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
                zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t) -
              ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
                zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t) +
              Complex.I *
                (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
                  zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T))) +
            Complex.I *
              zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteExcisionError
                f T ε = 0 := by
  intro ε hε hclosed hsep
  let C : ℂ := zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T)
  let P : ℂ :=
    ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
      zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t
  let G : ℂ :=
    ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
      zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t
  let R : ℂ := zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T)
  let Q : ℂ :=
    ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
      zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t
  let J : ℂ :=
    ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
      zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t
  let H : ℂ :=
    zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
      zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T)
  let E : ℂ :=
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteExcisionError
      f T ε
  have hcompleted_boundary :
      (-(C * Complex.I)) + (R * Complex.I + H) + E = 0 :=
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_leftTangent_add_finiteErrors_eq_zero_ownerFiniteRectangle
      f F h hT hinterior hboundary ε hε hclosed hsep
  have hsplit :
      (P - Q) + ((G - J) + Complex.I * H) + Complex.I * E = 0 :=
    explicitFormula_primeLeftBoundary_fullRightSplit_of_completedBoundary
      C P G R Q J H E hleft_decomp hright_decomp hcompleted_boundary
  exact hsplit

/-- Finite-radius prime-left residue-free rectangle identity in prime-oriented
boundary-sum form, with the finite left completed-log-derivative decomposition
proved from integrability of the two summands. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_primeLeft_add_finitePrimeErrors_eq_zero_ownerFiniteRectangle
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) {T : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hprime :
      IntegrableOn
        (zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F)
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T))
    (hinverseGamma :
      IntegrableOn
        (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F)
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T)) :
    ∀ ε : ℝ,
      0 < ε →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            ∀ b : ℂ,
              b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a ≠ b → ε + ε < dist a b) →
          (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
            zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t) +
            ((∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
                zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t) +
              Complex.I *
                zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteHorizontalRightError
                  f F T) +
            Complex.I *
              zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteExcisionError
                f T ε = 0 := by
  have hleft_decomp :
      zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) =
        (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
          zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t) +
        (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
          zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t) :=
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_leftIntegral_eq_prime_add_inverseGamma_of_integrableOn
      f F T hprime hinverseGamma
  exact
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_primeLeft_add_finitePrimeErrors_eq_zero_of_leftIntegral_decomposition
      f F h hT hinterior hboundary hleft_decomp

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
