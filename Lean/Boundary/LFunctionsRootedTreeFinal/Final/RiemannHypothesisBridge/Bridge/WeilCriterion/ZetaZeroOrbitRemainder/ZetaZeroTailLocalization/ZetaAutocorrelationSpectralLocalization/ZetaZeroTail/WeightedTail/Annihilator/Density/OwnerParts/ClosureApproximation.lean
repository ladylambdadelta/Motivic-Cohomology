import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Annihilator.Density.OwnerParts.FiniteWindowGap
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Annihilator.Density.OwnerParts.HahnBanachSeparation
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Annihilator.DistributionalClassification.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.FiniteComplement.Owner

/-!
# Completed-zero closure and finite-window approximation

This owner part assembles finite-window uniqueness, Hahn-Banach density, and
finite-support right inverses into the approximation statements consumed
downstream.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

open scoped ENNReal
open FiniteWindow

theorem exists_zetaCompletedZeroSideAnnihilator_finiteWindow_dominates_complementaryTail_of_distributionalClassification
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (rho : ZetaCompletedZeroCoordinate)
    (hrho : b rho ≠ 0) :
    ∃ (S : Finset ℂ)
      (hS : ∀ eta : ℂ, eta ∈ S → ZetaCompletedZero eta)
      (f : ZetaAdmissibleFunction),
      (rho : ℂ) ∈ S ∧
        norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) <
          norm (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f) :=
  match
    exists_zetaCompletedZeroSideAnnihilator_finiteWindow_gap_bound
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      b rho hrho with
  | ⟨S, hS, f, carrierBound, carrierGap, hpayload⟩ =>
      let hcarrierGapPositive : 0 < carrierGap :=
        hpayload.2.2.1
      let hcarrierIdentity :
          carrierBound =
            norm (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f) :=
        hpayload.2.2.2.1
      let htailGapLe :
          norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) +
              carrierGap ≤
            carrierBound :=
        hpayload.2.2.2.2
      let htailGapLeWindow :
          norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) +
              carrierGap ≤
            norm (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f) :=
        FiniteWindow.tail_gap_le_finiteWindow_norm_of_carrier_identity
          b S hS f carrierBound carrierGap hcarrierIdentity htailGapLe
      let hdominates :
          norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) <
            norm (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f) :=
        FiniteWindow.tail_norm_lt_of_positive_gap_bound
          (norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f))
          (norm (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f))
          carrierGap
          hcarrierGapPositive
          htailGapLeWindow
      ⟨S, hS, f, hpayload.1, hdominates⟩

theorem exists_zetaCompletedZeroSideAnnihilator_finiteWindow_dominates_complementaryTail
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (rho : ZetaCompletedZeroCoordinate)
    (hrho : b rho ≠ 0) :
    ∃ (S : Finset ℂ)
      (hS : ∀ eta : ℂ, eta ∈ S → ZetaCompletedZero eta)
      (f : ZetaAdmissibleFunction),
      (rho : ℂ) ∈ S ∧
        norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) <
          norm (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f) :=
  exists_zetaCompletedZeroSideAnnihilator_finiteWindow_dominates_complementaryTail_of_distributionalClassification
    hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
    b rho hrho

theorem zetaCompletedZeroSideAnnihilator_uniqueness_explicitFormula
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∀ b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal),
      ZetaCompletedZeroSideAnnihilatorVanishes
        b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary →
        b = 0 :=
  fun b hvanishes =>
    FiniteWindow.zetaCompletedZeroSideAnnihilator_coefficient_eq_zero_of_vanishes
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      b hvanishes

theorem zetaCompletedZeroSideCoordinateL1Closure_eq_univ
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    zetaCompletedZeroSideCoordinateL1Closure
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary =
      Set.univ :=
  zetaCompletedZeroSideCoordinateL1Closure_eq_univ_of_annihilatorUniqueness
    hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
    (zetaCompletedZeroSideAnnihilator_uniqueness_explicitFormula
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary)

theorem zetaCompletedZeroSideL1DualCoefficient_eq_zero_of_annihilator_vanishing
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
          b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f = 0) :
    b = 0 :=
  zetaCompletedZeroSideL1DualCoefficient_eq_zero_of_coordinateClosure_eq_univ
    b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
    hvanishing
    (zetaCompletedZeroSideCoordinateL1Closure_eq_univ
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary)

theorem zetaCompletedZeroSideCoordinateL1FiniteRightInverse_mem_closure
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (S : Finset ZetaCompletedZeroCoordinate)
    (a : S → ℂ) :
    zetaCompletedZeroSideCoordinateL1FiniteRightInverse S a ∈
      zetaCompletedZeroSideCoordinateL1Closure
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary :=
  let hdense :
      zetaCompletedZeroSideCoordinateL1Closure
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary =
        Set.univ :=
    zetaCompletedZeroSideCoordinateL1Closure_eq_univ
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
  Eq.mp
    (congrArg
      (fun carrier : Set (lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)) =>
        zetaCompletedZeroSideCoordinateL1FiniteRightInverse S a ∈ carrier)
      hdense.symm)
    (Set.mem_univ (zetaCompletedZeroSideCoordinateL1FiniteRightInverse S a))

theorem exists_zetaCompletedZeroSideCoordinateL1_approximation_of_finiteRightInverse
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (S : Finset ZetaCompletedZeroCoordinate)
    (a : S → ℂ)
    (epsilon : ℝ)
    (hepsilon : 0 < epsilon) :
    ∃ f : ZetaAdmissibleFunction,
      dist
        (zetaCompletedZeroSideCoordinateL1FiniteRightInverse S a)
        (zetaCompletedZeroSideCoordinateL1LinearMap
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f) <
        epsilon :=
  let hclosure :
      zetaCompletedZeroSideCoordinateL1FiniteRightInverse S a ∈
        closure
          (Set.range
            (zetaCompletedZeroSideCoordinateL1LinearMap
              hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary)) :=
    zetaCompletedZeroSideCoordinateL1FiniteRightInverse_mem_closure
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary S a
  match (Metric.mem_closure_range_iff.mp hclosure) epsilon hepsilon with
  | ⟨f, hf⟩ => ⟨f, hf⟩

theorem finiteRightInverse_coordinate_dist_le_l1_dist
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (S : Finset ZetaCompletedZeroCoordinate)
    (a : S → ℂ)
    (f : ZetaAdmissibleFunction)
    (rho : S) :
    dist
        (zetaCompletedZeroSideCoordinateL1FiniteRightInverse S a
          (rho : ZetaCompletedZeroCoordinate))
        (zetaCompletedZeroSideCoordinateL1LinearMap
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f
          (rho : ZetaCompletedZeroCoordinate)) ≤
      dist
        (zetaCompletedZeroSideCoordinateL1FiniteRightInverse S a)
        (zetaCompletedZeroSideCoordinateL1LinearMap
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f) :=
  lp.norm_apply_le_norm
    one_ne_zero
    (zetaCompletedZeroSideCoordinateL1FiniteRightInverse S a -
      zetaCompletedZeroSideCoordinateL1LinearMap
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f)
    (rho : ZetaCompletedZeroCoordinate)

theorem finiteRightInverse_target_coordinate_eq
    (S : Finset ZetaCompletedZeroCoordinate)
    (a : S → ℂ)
    (rho : S) :
    a rho =
      zetaCompletedZeroSideCoordinateL1FiniteRightInverse S a
        (rho : ZetaCompletedZeroCoordinate) :=
  (zetaCompletedZeroSideCoordinateL1FiniteRightInverse_apply S a rho).symm

theorem coordinateLinearMap_eq_coordinateL1LinearMap
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (f : ZetaAdmissibleFunction)
    (rho : ZetaCompletedZeroCoordinate) :
    zetaCompletedZeroSideCoordinateLinearMap f rho =
      zetaCompletedZeroSideCoordinateL1LinearMap
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f rho :=
  Eq.trans
    (zetaCompletedZeroSideCoordinateLinearMap_apply f rho)
    (zetaCompletedZeroSideCoordinateL1LinearMap_apply
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f rho).symm

theorem finiteRightInverse_window_coordinate_dist_eq
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (S : Finset ZetaCompletedZeroCoordinate)
    (a : S → ℂ)
    (f : ZetaAdmissibleFunction)
    (rho : S) :
    dist
        (a rho)
        (zetaCompletedZeroSideCoordinateLinearMap f (rho : ZetaCompletedZeroCoordinate)) =
      dist
        (zetaCompletedZeroSideCoordinateL1FiniteRightInverse S a
          (rho : ZetaCompletedZeroCoordinate))
        (zetaCompletedZeroSideCoordinateL1LinearMap
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f
          (rho : ZetaCompletedZeroCoordinate)) :=
  Eq.trans
    (congrArg
      (fun coordinate : ℂ =>
        dist coordinate
          (zetaCompletedZeroSideCoordinateLinearMap f
            (rho : ZetaCompletedZeroCoordinate)))
      (finiteRightInverse_target_coordinate_eq S a rho))
    (congrArg
      (fun coordinate : ℂ =>
        dist
          (zetaCompletedZeroSideCoordinateL1FiniteRightInverse S a
            (rho : ZetaCompletedZeroCoordinate))
          coordinate)
      (coordinateLinearMap_eq_coordinateL1LinearMap
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
        f (rho : ZetaCompletedZeroCoordinate)))

theorem finiteRightInverse_window_coordinate_dist_lt
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (S : Finset ZetaCompletedZeroCoordinate)
    (a : S → ℂ)
    (epsilon : ℝ)
    (f : ZetaAdmissibleFunction)
    (hf :
      dist
        (zetaCompletedZeroSideCoordinateL1FiniteRightInverse S a)
        (zetaCompletedZeroSideCoordinateL1LinearMap
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f) <
        epsilon)
    (rho : S) :
    dist
      (a rho)
      (zetaCompletedZeroSideCoordinateLinearMap f (rho : ZetaCompletedZeroCoordinate)) <
        epsilon :=
  lt_of_le_of_lt
    (le_trans
      (le_of_eq
        (finiteRightInverse_window_coordinate_dist_eq
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
          S a f rho))
      (finiteRightInverse_coordinate_dist_le_l1_dist
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
        S a f rho))
    hf

theorem exists_zetaCompletedZeroSideCoordinate_approximation_on_finiteWindow
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (S : Finset ZetaCompletedZeroCoordinate)
    (a : S → ℂ)
    (epsilon : ℝ)
    (hepsilon : 0 < epsilon) :
    ∃ f : ZetaAdmissibleFunction,
      ∀ rho : S,
        dist
          (a rho)
          (zetaCompletedZeroSideCoordinateLinearMap
            f
            (rho : ZetaCompletedZeroCoordinate)) < epsilon :=
  match
    exists_zetaCompletedZeroSideCoordinateL1_approximation_of_finiteRightInverse
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      S a epsilon hepsilon with
  | ⟨f, hf⟩ =>
      ⟨f,
        fun rho =>
          finiteRightInverse_window_coordinate_dist_lt
            hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
            S a epsilon f hf rho⟩

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
