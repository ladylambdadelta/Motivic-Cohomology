import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Annihilator.DistributionalClassification.Vanishing
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Annihilator.FiniteWindow.Core
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Annihilator.FiniteWindow.CarrierSeparation

/-!
# Finite-window completed-zero annihilator assembly

This owner turns the paired finite-coordinate detection theorem into
coefficientwise uniqueness for bounded completed-zero distributions.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction
namespace FiniteWindow

open scoped ENNReal

theorem norm_eq_of_eq_neg_complex
    (x : ℂ)
    (y : ℂ)
    (hy : y = -x) :
    norm x = norm y :=
  Eq.trans
    (norm_neg x).symm
    (congrArg norm hy.symm)

theorem zetaCompletedZeroSideAnnihilator_complementaryTail_norm_eq_finiteWindow_norm
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (S : Finset ℂ)
    (hS : ∀ eta : ℂ, eta ∈ S → ZetaCompletedZero eta)
    (f : ZetaAdmissibleFunction)
    (hwindowEqNegTail :
      zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f =
        - zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) :
    norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) =
      norm (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f) :=
  norm_eq_of_eq_neg_complex
    (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f)
    (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f)
    hwindowEqNegTail

theorem not_lt_of_eq_real
    (x : ℝ)
    (y : ℝ)
    (hxy : x = y) :
    ¬ x < y :=
  not_lt_of_ge (le_of_eq hxy.symm)

theorem zetaCompletedZeroSideAnnihilator_ne_zero_of_finiteWindow_dominates_complementaryTail
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (S : Finset ℂ)
    (hS : ∀ eta : ℂ, eta ∈ S → ZetaCompletedZero eta)
    (f : ZetaAdmissibleFunction)
    (hdominates :
      norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) <
        norm (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f) ) :
    zetaCompletedZeroSideAnnihilator
      b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f ≠ 0 :=
  fun hannihilates =>
    let hwindowEqNegTail :
        zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f =
          - zetaCompletedZeroSideAnnihilatorComplementaryTail b S f :=
      zetaCompletedZeroSideAnnihilatorFiniteWindow_eq_neg_complementaryTail_of_annihilates
        b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
        S hS f hannihilates
    let hnormEq :
        norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) =
          norm (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f) :=
      zetaCompletedZeroSideAnnihilator_complementaryTail_norm_eq_finiteWindow_norm
        b S hS f hwindowEqNegTail
    not_lt_of_eq_real
      (norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f))
      (norm (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f))
      hnormEq
      hdominates

theorem zetaCompletedZeroSideAnnihilator_ne_zero_of_finiteWindow_gap_bound
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (S : Finset ℂ)
    (hS : ∀ eta : ℂ, eta ∈ S → ZetaCompletedZero eta)
    (f : ZetaAdmissibleFunction)
    (carrierGap : ℝ)
    (hcarrierGapPositive : 0 < carrierGap)
    (htailGapLe :
      norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) +
          carrierGap ≤
        norm (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f)) :
    zetaCompletedZeroSideAnnihilator
      b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f ≠ 0 :=
  let hdominates :
      norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) <
        norm (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f) :=
    tail_norm_lt_of_positive_gap_bound
      (norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f))
      (norm (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f))
      carrierGap
      hcarrierGapPositive
      htailGapLe
  zetaCompletedZeroSideAnnihilator_ne_zero_of_finiteWindow_dominates_complementaryTail
    b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
    S hS f hdominates

theorem zetaCompletedZeroSideAnnihilator_ne_zero_of_positive_norm_lower_bound
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (f : ZetaAdmissibleFunction)
    (constant : ℝ)
    (hconstantPositive : 0 < constant)
    (hconstantBound :
      constant ≤
        norm
          (zetaCompletedZeroSideAnnihilator
            b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft
              hcompactBoundary f)) :
    zetaCompletedZeroSideAnnihilator
      b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f ≠ 0 :=
  fun hannihilatorZero =>
    let hnormZero :
        norm
          (zetaCompletedZeroSideAnnihilator
            b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft
              hcompactBoundary f) = 0 :=
      Eq.trans
        (congrArg norm hannihilatorZero)
        (norm_zero : norm (0 : ℂ) = 0)
    let hconstantLeZero : constant ≤ 0 :=
      Eq.subst
        (motive := fun value : ℝ => constant ≤ value)
        hnormZero
        hconstantBound
    (not_lt_of_ge hconstantLeZero) hconstantPositive

theorem zetaCompletedZeroSideAnnihilator_selectedCoefficient_not_ne_of_vanishes
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (hvanishes :
      ZetaCompletedZeroSideAnnihilatorVanishes
        b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary)
    (rho : ZetaCompletedZeroCoordinate) :
    ¬ b rho ≠ 0 :=
  fun hrho =>
    match
      exists_zetaCompletedZeroSideAnnihilator_positive_norm_lower_bound_with_carrier
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
        b rho hrho with
    | ⟨S, hS, f, constant, hpayload⟩ =>
        let hconstantPositive : 0 < constant :=
          hpayload.2.1
        let hannihilatorBound :
            constant ≤
              norm
                (zetaCompletedZeroSideAnnihilator
                  b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft
                    hcompactBoundary f) :=
          hpayload.2.2
        zetaCompletedZeroSideAnnihilator_ne_zero_of_positive_norm_lower_bound
          b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
          f constant hconstantPositive hannihilatorBound
          (hvanishes f)

/-- Finite-window detection turns probewise annihilation into vanishing of one
selected bounded completed-zero coefficient. -/
theorem zetaCompletedZeroSideAnnihilator_selectedCoefficient_eq_zero_of_vanishes
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (hvanishes :
      ZetaCompletedZeroSideAnnihilatorVanishes
        b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary)
    (rho : ZetaCompletedZeroCoordinate) :
    b rho = 0 :=
  not_ne_iff.mp
    (zetaCompletedZeroSideAnnihilator_selectedCoefficient_not_ne_of_vanishes
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      b hvanishes rho)

/-- Finite-window detection of every nonzero coefficient turns probewise
annihilation into coefficientwise uniqueness. -/
theorem zetaCompletedZeroSideAnnihilator_coefficient_eq_zero_of_vanishes
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (hvanishes :
      ZetaCompletedZeroSideAnnihilatorVanishes
        b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary) :
    b = 0 :=
  lp.ext
    (funext
      (fun rho : ZetaCompletedZeroCoordinate =>
        zetaCompletedZeroSideAnnihilator_selectedCoefficient_eq_zero_of_vanishes
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
          b hvanishes rho))

end FiniteWindow
end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
