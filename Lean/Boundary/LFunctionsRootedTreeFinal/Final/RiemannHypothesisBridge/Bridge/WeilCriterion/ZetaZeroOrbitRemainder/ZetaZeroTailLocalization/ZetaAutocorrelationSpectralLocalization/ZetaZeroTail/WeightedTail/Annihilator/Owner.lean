import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.DualPairing.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Owner

/-!
# Completed-zero coordinate annihilators

This file defines the analytic functional associated to a bounded completed-zero
coefficient family and records its absolutely convergent zero-side series.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

open scoped ENNReal

/-- The completed-zero functional induced by a bounded coefficient family. -/
noncomputable def zetaCompletedZeroSideAnnihilator
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedZeroSideL1DualPairing
    b
    (zetaCompletedZeroSideCoordinateL1LinearMap
      hbranch
      hpartialOneTwo
      hcompactOneTwo
      hfinite
      hpartialLeft
      hcompactBoundary
      f)

/-- The bounded-coefficient completed-zero annihilator as a linear functional
on admissible probes. -/
noncomputable def zetaCompletedZeroSideAnnihilatorLinearMap
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ZetaAdmissibleFunction →ₗ[ℂ] ℂ :=
  (zetaCompletedZeroSideL1DualContinuousLinearMap b).toLinearMap.comp
    (zetaCompletedZeroSideCoordinateL1LinearMap
      hbranch
      hpartialOneTwo
      hcompactOneTwo
      hfinite
      hpartialLeft
      hcompactBoundary)

/-- The linear annihilator functional evaluates to its absolutely convergent
completed-zero coefficient series. -/
theorem zetaCompletedZeroSideAnnihilatorLinearMap_apply
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroSideAnnihilatorLinearMap
        b
        hbranch
        hpartialOneTwo
        hcompactOneTwo
        hfinite
        hpartialLeft
        hcompactBoundary
        f =
      zetaCompletedZeroSideAnnihilator
        b
        hbranch
        hpartialOneTwo
        hcompactOneTwo
        hfinite
        hpartialLeft
        hcompactBoundary
        f := by
  rfl

/-- The coefficient series defining a completed-zero annihilator is summable. -/
theorem summable_zetaCompletedZeroSideAnnihilator
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (f : ZetaAdmissibleFunction) :
    Summable
      (fun rho : ZetaCompletedZeroCoordinate =>
        b rho * zetaZeroSideContribution (rho : ℂ) f) := by
  have hpairing :
      Summable
        (fun rho : ZetaCompletedZeroCoordinate =>
          b rho *
            (zetaCompletedZeroSideCoordinateL1LinearMap
              hbranch
              hpartialOneTwo
              hcompactOneTwo
              hfinite
              hpartialLeft
              hcompactBoundary
              f)
              rho) := by
    exact
      zetaCompletedZeroSideL1DualPairing_summable
        b
        (zetaCompletedZeroSideCoordinateL1LinearMap
          hbranch
          hpartialOneTwo
          hcompactOneTwo
          hfinite
          hpartialLeft
          hcompactBoundary
          f)
  have hseries :
      (fun rho : ZetaCompletedZeroCoordinate =>
        b rho *
          (zetaCompletedZeroSideCoordinateL1LinearMap
            hbranch
            hpartialOneTwo
            hcompactOneTwo
            hfinite
            hpartialLeft
            hcompactBoundary
            f)
            rho) =
        (fun rho : ZetaCompletedZeroCoordinate =>
          b rho * zetaZeroSideContribution (rho : ℂ) f) := by
    funext rho
    exact
      congrArg
        (fun z : ℂ => b rho * z)
        (zetaCompletedZeroSideCoordinateL1LinearMap_apply
          hbranch
          hpartialOneTwo
          hcompactOneTwo
          hfinite
          hpartialLeft
          hcompactBoundary
          f
          rho)
  exact Eq.mpr (congrArg Summable hseries) hpairing

/-- The annihilator is the corresponding absolutely convergent zero-side series. -/
theorem zetaCompletedZeroSideAnnihilator_eq_tsum
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroSideAnnihilator
        b
        hbranch
        hpartialOneTwo
        hcompactOneTwo
        hfinite
        hpartialLeft
        hcompactBoundary
        f =
      tsum
        (fun rho : ZetaCompletedZeroCoordinate =>
          b rho * zetaZeroSideContribution (rho : ℂ) f) := by
  unfold zetaCompletedZeroSideAnnihilator
  unfold zetaCompletedZeroSideL1DualPairing
  exact
    tsum_congr
      (fun rho =>
        congrArg
          (fun z : ℂ => b rho * z)
          (zetaCompletedZeroSideCoordinateL1LinearMap_apply
            hbranch
            hpartialOneTwo
            hcompactOneTwo
            hfinite
            hpartialLeft
          hcompactBoundary
          f
          rho))

/-- If a bounded completed-zero coefficient family annihilates every admissible
probe coordinate, it also annihilates the completed-zero `l1` closure of those
coordinates. -/
theorem zetaCompletedZeroSideL1DualPairing_eq_zero_on_coordinateClosure
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (hvanishing :
      forall f : ZetaAdmissibleFunction,
        zetaCompletedZeroSideAnnihilator
          b
          hbranch
          hpartialOneTwo
          hcompactOneTwo
          hfinite
          hpartialLeft
          hcompactBoundary
          f = 0) :
    forall x : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal),
      x ∈
        zetaCompletedZeroSideCoordinateL1Closure
          hbranch
          hpartialOneTwo
          hcompactOneTwo
          hfinite
          hpartialLeft
          hcompactBoundary ->
        zetaCompletedZeroSideL1DualPairing b x = 0 := by
  let L :
      lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal) →L[ℂ] ℂ :=
    zetaCompletedZeroSideL1DualContinuousLinearMap b
  have hclosed : IsClosed (L ⁻¹' ({0} : Set ℂ)) := by
    exact isClosed_singleton.preimage L.continuous
  have himage :
      zetaCompletedZeroSideCoordinateL1Image
          hbranch
          hpartialOneTwo
          hcompactOneTwo
          hfinite
          hpartialLeft
          hcompactBoundary ⊆
        L ⁻¹' ({0} : Set ℂ) := by
    intro x hx
    match hx with
    | ⟨f, hf⟩ =>
        change L x = 0
        have hpairing :
            L
              (zetaCompletedZeroSideCoordinateL1LinearMap
                hbranch
                hpartialOneTwo
                hcompactOneTwo
                hfinite
                hpartialLeft
                hcompactBoundary
                f) = 0 := by
          exact
            Eq.trans
              (zetaCompletedZeroSideL1DualContinuousLinearMap_apply
                b
                (zetaCompletedZeroSideCoordinateL1LinearMap
                  hbranch
                  hpartialOneTwo
                  hcompactOneTwo
                  hfinite
                  hpartialLeft
                  hcompactBoundary
                  f))
              (hvanishing f)
        exact
          Eq.subst
            (motive := fun coordinate => L coordinate = 0)
            hf
            hpairing
  have hclosure :
      zetaCompletedZeroSideCoordinateL1Closure
          hbranch
          hpartialOneTwo
          hcompactOneTwo
          hfinite
          hpartialLeft
          hcompactBoundary ⊆
        L ⁻¹' ({0} : Set ℂ) := by
    exact closure_minimal himage hclosed
  intro x hx
  have hLx : L x = 0 := by
    have hLxMembership : x ∈ L ⁻¹' ({0} : Set ℂ) := hclosure hx
    change L x = 0 at hLxMembership
    exact hLxMembership
  exact
    Eq.trans
      (zetaCompletedZeroSideL1DualContinuousLinearMap_apply b x).symm
      hLx

/-- Density of the admissible completed-zero coordinate image forces every
bounded annihilator coefficient family to vanish. -/
theorem zetaCompletedZeroSideL1DualCoefficient_eq_zero_of_coordinateClosure_eq_univ
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (hvanishing :
      forall f : ZetaAdmissibleFunction,
        zetaCompletedZeroSideAnnihilator
          b
          hbranch
          hpartialOneTwo
          hcompactOneTwo
          hfinite
          hpartialLeft
          hcompactBoundary
          f = 0)
    (hdense :
      zetaCompletedZeroSideCoordinateL1Closure
          hbranch
          hpartialOneTwo
          hcompactOneTwo
          hfinite
          hpartialLeft
          hcompactBoundary = Set.univ) :
    b = 0 := by
  apply zetaCompletedZeroSideL1DualPairing_eq_zero_of_forall_eq_zero b
  intro x
  have hxClosure :
      x ∈
        zetaCompletedZeroSideCoordinateL1Closure
          hbranch
          hpartialOneTwo
          hcompactOneTwo
          hfinite
          hpartialLeft
          hcompactBoundary := by
      exact
        Eq.mp
          (congrArg
            (fun carrier => x ∈ carrier)
            hdense.symm)
          (Set.mem_univ x)
  exact
    zetaCompletedZeroSideL1DualPairing_eq_zero_on_coordinateClosure
      b
      hbranch
      hpartialOneTwo
      hcompactOneTwo
      hfinite
      hpartialLeft
      hcompactBoundary
      hvanishing
      x
      hxClosure

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
