import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Annihilator.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Annihilator.FiniteWindow.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Annihilator.DistributionalClassification.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.DualRepresentation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.FiniteComplement.Owner
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Module.Dual

/-!
# Completed-zero coordinate density

This owner isolates the explicit-formula uniqueness statement needed to turn
the bounded completed-zero annihilator calculation into coordinate density.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

/-- The continuous quotient map by the closed completed-zero coordinate
submodule. -/
noncomputable def zetaCompletedZeroSideCoordinateL1QuotientMap
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal) →L[ℂ]
      (lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal) ⧸
        zetaCompletedZeroSideCoordinateL1ClosureSubmodule
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary) := by
  let S : Submodule ℂ (lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)) :=
    zetaCompletedZeroSideCoordinateL1ClosureSubmodule
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
  letI : IsClosed (S : Set (lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal))) :=
    isClosed_zetaCompletedZeroSideCoordinateL1ClosureSubmodule
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
  exact
    LinearMap.mkContinuous S.mkQ (1 : ℝ)
      (fun x =>
        calc
          norm (S.mkQ x) ≤ norm x := Submodule.Quotient.norm_mk_le x
          _ = (1 : ℝ) * norm x := (one_mul (norm x)).symm)

/-- The completed-zero quotient map kills every admissible probe coordinate. -/
theorem zetaCompletedZeroSideCoordinateL1QuotientMap_apply_coordinate
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroSideCoordinateL1QuotientMap
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
        (zetaCompletedZeroSideCoordinateL1LinearMap
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f) = 0 := by
  let S : Submodule ℂ (lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)) :=
    zetaCompletedZeroSideCoordinateL1ClosureSubmodule
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
  have hcoordinate :
      zetaCompletedZeroSideCoordinateL1LinearMap
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f ∈ S := by
    exact
      mem_zetaCompletedZeroSideCoordinateL1ClosureSubmodule
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f
  change S.mkQ
      (zetaCompletedZeroSideCoordinateL1LinearMap
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f) = 0
  exact Submodule.Quotient.mk_eq_zero.mpr hcoordinate

/-- A vector outside the closed completed-zero coordinate submodule has a
continuous complex-linear functional which vanishes on every probe coordinate
and does not vanish at that vector. -/
theorem exists_zetaCompletedZeroSideCoordinateL1_separator
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (x : lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal))
    (hx : x ∉ zetaCompletedZeroSideCoordinateL1ClosureSubmodule
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary) :
    ∃ L : lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal) →L[ℂ] ℂ,
      (∀ f : ZetaAdmissibleFunction,
        L (zetaCompletedZeroSideCoordinateL1LinearMap
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f) = 0) ∧
      L x ≠ 0 := by
  let S : Submodule ℂ (lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)) :=
    zetaCompletedZeroSideCoordinateL1ClosureSubmodule
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
  letI : IsClosed (S : Set (lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal))) :=
    isClosed_zetaCompletedZeroSideCoordinateL1ClosureSubmodule
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
  let q := zetaCompletedZeroSideCoordinateL1QuotientMap
    hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
  have hqx : q x ≠ 0 := by
    intro hzero
    apply hx
    change S.mkQ x = 0 at hzero
    exact Submodule.Quotient.mk_eq_zero.mp hzero
  obtain ⟨g, hgNorm, hgValue⟩ := exists_dual_vector ℂ (q x) hqx
  let L : lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal) →L[ℂ] ℂ :=
    g.comp q
  have hcoordinateVanishes :
      ∀ f : ZetaAdmissibleFunction,
        L (zetaCompletedZeroSideCoordinateL1LinearMap
          hbranch hpartialOneTwo hcompactOneTwo hfinite
          hpartialLeft hcompactBoundary f) = 0 := by
    intro f
    change g
      (q (zetaCompletedZeroSideCoordinateL1LinearMap
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f)) = 0
    exact
      congrArg g
        (zetaCompletedZeroSideCoordinateL1QuotientMap_apply_coordinate
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f)
  have hnonzero : L x ≠ 0 := by
    intro hzero
    have hnormZero : norm (q x) = 0 := by
      have hcoercedNormZero : (norm (q x) : ℂ) = 0 := by
        calc
          (norm (q x) : ℂ) = g (q x) := hgValue.symm
          _ = L x := rfl
          _ = 0 := hzero
      exact Complex.ofReal_eq_zero.mp hcoercedNormZero
    exact hqx (norm_eq_zero.mp hnormZero)
  exact ⟨L, hcoordinateVanishes, hnonzero⟩

/-- The finite completed-zero window contribution of a bounded coefficient
distribution. -/
noncomputable def zetaCompletedZeroSideAnnihilatorFiniteWindow
    (b : lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (S : Finset ℂ)
    (hS : ∀ eta : ℂ, eta ∈ S → ZetaCompletedZero eta)
    (f : ZetaAdmissibleFunction) : ℂ :=
  ∑ eta in S.attach,
    b ⟨eta, hS eta eta.2⟩ * zetaZeroSideContribution eta f

/-- The complementary completed-zero tail of a bounded coefficient
distribution after a finite window has been excised. -/
noncomputable def zetaCompletedZeroSideAnnihilatorComplementaryTail
    (b : lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (S : Finset ℂ)
    (f : ZetaAdmissibleFunction) : ℂ :=
  tsum (fun rho : {rho : ℂ // ZetaCompletedZero rho ∧ rho ∉ S} =>
    b ⟨rho, rho.2.1⟩ * zetaZeroSideContribution (rho : ℂ) f)

/-- The bounded completed-zero annihilator splits into a finite window and its
absolutely convergent complementary tail. -/
theorem zetaCompletedZeroSideAnnihilator_eq_finiteWindow_add_complementaryTail
    (b : lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (S : Finset ℂ)
    (hS : ∀ eta : ℂ, eta ∈ S → ZetaCompletedZero eta)
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroSideAnnihilator
        b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f =
      zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f +
        zetaCompletedZeroSideAnnihilatorComplementaryTail b S f := by
  have hsum :
      Summable (fun rho : ZetaCompletedZeroCoordinate =>
        b rho * zetaZeroSideContribution (rho : ℂ) f) :=
    summable_zetaCompletedZeroSideAnnihilator
      b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f
  have hsplit :=
    completedZeroSubtype_tsum_eq_finite_add_complement
      S
      (fun rho : ZetaCompletedZeroCoordinate =>
        b rho * zetaZeroSideContribution (rho : ℂ) f)
      hS
      hsum
  unfold zetaCompletedZeroSideAnnihilator
  unfold zetaCompletedZeroSideL1DualPairing
  unfold zetaCompletedZeroSideAnnihilatorFiniteWindow
  unfold zetaCompletedZeroSideAnnihilatorComplementaryTail
  exact hsplit

/-- If a bounded completed-zero distribution annihilates a probe, its selected
finite window is the negative of the complementary tail. -/
theorem zetaCompletedZeroSideAnnihilatorFiniteWindow_eq_neg_complementaryTail_of_annihilates
    (b : lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (S : Finset ℂ)
    (hS : ∀ eta : ℂ, eta ∈ S → ZetaCompletedZero eta)
    (f : ZetaAdmissibleFunction)
    (hannihilates :
      zetaCompletedZeroSideAnnihilator
        b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f = 0) :
    zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f =
      - zetaCompletedZeroSideAnnihilatorComplementaryTail b S f := by
  have hsplit :=
    zetaCompletedZeroSideAnnihilator_eq_finiteWindow_add_complementaryTail
      b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary S hS f
  have hsumZero :
      zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f +
        zetaCompletedZeroSideAnnihilatorComplementaryTail b S f = 0 := by
    exact Eq.trans hsplit.symm hannihilates
  exact eq_neg_of_add_eq_zero_left hsumZero

/-- Distributional uniqueness for bounded completed-zero coefficients implies
the finite-window localization statement below.  Its proof identifies the
bounded zero distribution with the prime and archimedean explicit-formula
distribution and shows that a vanishing distribution has zero coefficients. -/
theorem exists_zetaCompletedZeroSideAnnihilator_finiteWindow_dominates_complementaryTail_of_distributionalClassification
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (b : lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (rho : ZetaCompletedZeroCoordinate)
    (hrho : b rho ≠ 0) :
    ∃ (S : Finset ℂ)
      (hS : ∀ eta : ℂ, eta ∈ S → ZetaCompletedZero eta)
      (f : ZetaAdmissibleFunction),
      (rho : ℂ) ∈ S ∧
        norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) <
          norm (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f) := by
  exact
    FiniteWindow.exists_zetaCompletedZeroSideAnnihilator_finiteWindow_dominates_complementaryTail
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      b rho hrho

/-- A nonzero bounded completed-zero coefficient can be detected on a finite
zero window whose contribution strictly dominates the complementary tail. -/
theorem exists_zetaCompletedZeroSideAnnihilator_finiteWindow_dominates_complementaryTail
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (b : lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (rho : ZetaCompletedZeroCoordinate)
    (hrho : b rho ≠ 0) :
    ∃ (S : Finset ℂ)
      (hS : ∀ eta : ℂ, eta ∈ S → ZetaCompletedZero eta)
      (f : ZetaAdmissibleFunction),
      (rho : ℂ) ∈ S ∧
        norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) <
          norm (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f) := by
  exact
    exists_zetaCompletedZeroSideAnnihilator_finiteWindow_dominates_complementaryTail_of_distributionalClassification
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      b rho hrho

/-- Strict finite-window domination of the complementary tail forces the
bounded completed-zero annihilator to be nonzero on that probe. -/
theorem zetaCompletedZeroSideAnnihilator_ne_zero_of_finiteWindow_dominates_complementaryTail
    (b : lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
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
      b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f ≠ 0 := by
  intro hannihilates
  have hwindowEqNegTail :
      zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f =
        - zetaCompletedZeroSideAnnihilatorComplementaryTail b S f :=
    zetaCompletedZeroSideAnnihilatorFiniteWindow_eq_neg_complementaryTail_of_annihilates
      b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      S hS f hannihilates
  have hnormEq :
      norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) =
        norm (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f) := by
    calc
      norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) =
          norm (- zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) :=
        (norm_neg (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f)).symm
      _ = norm (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f) :=
        congrArg norm hwindowEqNegTail.symm
  exact (not_lt_of_ge (le_of_eq hnormEq)) hdominates

/-- Explicit-formula uniqueness for bounded completed-zero coefficient
distributions, reduced to finite-window domination of the complementary tail. -/
theorem zetaCompletedZeroSideAnnihilator_uniqueness_explicitFormula
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∀ b : lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal),
      ZetaCompletedZeroSideAnnihilatorVanishes
        b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary →
        b = 0 := by
  intro b hvanishes
  exact
    FiniteWindow.zetaCompletedZeroSideAnnihilator_coefficient_eq_zero_of_vanishes
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      b hvanishes

/-- Hahn-Banach converts uniqueness of bounded annihilators into density of
the completed-zero coordinate image. -/
theorem zetaCompletedZeroSideCoordinateL1Closure_eq_univ_of_annihilatorUniqueness
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (huniqueness :
      ∀ b : lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal),
        ZetaCompletedZeroSideAnnihilatorVanishes
          b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary →
          b = 0) :
    zetaCompletedZeroSideCoordinateL1Closure
        hbranch
        hpartialOneTwo
        hcompactOneTwo
        hfinite
        hpartialLeft
        hcompactBoundary = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_contra hx
  have hxSubmodule :
      x ∉ zetaCompletedZeroSideCoordinateL1ClosureSubmodule
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary := by
    intro hxSubmoduleMembership
    apply hx
    exact
      Eq.mpr
        (congrArg
          (fun carrier : Set (lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)) =>
            x ∈ carrier)
          (zetaCompletedZeroSideCoordinateL1Closure_eq_closureSubmodule
            hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary))
        hxSubmoduleMembership
  obtain ⟨L, hLcoordinate, hLnonzero⟩ :=
    exists_zetaCompletedZeroSideCoordinateL1_separator
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary x hxSubmodule
  obtain ⟨b, hrepresentation⟩ :=
    exists_zetaCompletedZeroSideL1DualRepresentation L
  have hbAnnihilates :
      ∀ f : ZetaAdmissibleFunction,
        zetaCompletedZeroSideAnnihilator
          b
          hbranch
          hpartialOneTwo
          hcompactOneTwo
          hfinite
          hpartialLeft
          hcompactBoundary
          f = 0 := by
    intro f
    calc
      zetaCompletedZeroSideAnnihilator
          b
          hbranch
          hpartialOneTwo
          hcompactOneTwo
          hfinite
          hpartialLeft
          hcompactBoundary
          f =
          zetaCompletedZeroSideL1DualPairing
            b
            (zetaCompletedZeroSideCoordinateL1LinearMap
              hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f) := by
            rfl
      _ =
          L
            (zetaCompletedZeroSideCoordinateL1LinearMap
              hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f) :=
            (hrepresentation
              (zetaCompletedZeroSideCoordinateL1LinearMap
                hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f)).symm
      _ = 0 := hLcoordinate f
  have hbZero : b = 0 := huniqueness b hbAnnihilates
  apply hLnonzero
  calc
    L x = zetaCompletedZeroSideL1DualPairing b x := hrepresentation x
    _ = zetaCompletedZeroSideL1DualPairing (0 :
          lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal)) x := by
        exact congrArg (fun coefficient => zetaCompletedZeroSideL1DualPairing coefficient x) hbZero
    _ = 0 := by
      unfold zetaCompletedZeroSideL1DualPairing
      have hzeroSeries :
          (fun rho : ZetaCompletedZeroCoordinate =>
            (0 : lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal)) rho * x rho) =
          (fun _ : ZetaCompletedZeroCoordinate => (0 : ℂ)) := by
        funext rho
        exact zero_mul (x rho)
      calc
        tsum (fun rho : ZetaCompletedZeroCoordinate =>
          (0 : lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal)) rho * x rho) =
            tsum (fun _ : ZetaCompletedZeroCoordinate => (0 : ℂ)) :=
              congrArg tsum hzeroSeries
        _ = 0 := tsum_zero

/-- The completed explicit formula has no nonzero bounded completed-zero
annihilator; equivalently, admissible probe coordinates are dense in the
completed-zero `l1` coordinate space. -/
theorem zetaCompletedZeroSideCoordinateL1Closure_eq_univ
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    zetaCompletedZeroSideCoordinateL1Closure
        hbranch
        hpartialOneTwo
        hcompactOneTwo
        hfinite
        hpartialLeft
        hcompactBoundary = Set.univ := by
  exact
    zetaCompletedZeroSideCoordinateL1Closure_eq_univ_of_annihilatorUniqueness
      hbranch
      hpartialOneTwo
      hcompactOneTwo
      hfinite
      hpartialLeft
      hcompactBoundary
      (zetaCompletedZeroSideAnnihilator_uniqueness_explicitFormula
        hbranch
        hpartialOneTwo
        hcompactOneTwo
        hfinite
        hpartialLeft
        hcompactBoundary)

/-- A bounded coefficient family annihilating every admissible probe is zero. -/
theorem zetaCompletedZeroSideL1DualCoefficient_eq_zero_of_annihilator_vanishing
    (b : lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
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
    b = 0 := by
  exact
    zetaCompletedZeroSideL1DualCoefficient_eq_zero_of_coordinateClosure_eq_univ
      b
      hbranch
      hpartialOneTwo
      hcompactOneTwo
      hfinite
      hpartialLeft
      hcompactBoundary
      hvanishing
      (zetaCompletedZeroSideCoordinateL1Closure_eq_univ
        hbranch
        hpartialOneTwo
        hcompactOneTwo
        hfinite
        hpartialLeft
        hcompactBoundary)

/-- Every finite completed-zero target vector lies in the closure of admissible
probe coordinates, represented by its canonical finite-support right inverse. -/
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
        hbranch
        hpartialOneTwo
        hcompactOneTwo
        hfinite
        hpartialLeft
        hcompactBoundary := by
  have hdense :
      zetaCompletedZeroSideCoordinateL1Closure
          hbranch
          hpartialOneTwo
          hcompactOneTwo
          hfinite
          hpartialLeft
          hcompactBoundary = Set.univ :=
    zetaCompletedZeroSideCoordinateL1Closure_eq_univ
      hbranch
      hpartialOneTwo
      hcompactOneTwo
      hfinite
      hpartialLeft
      hcompactBoundary
  exact
    Eq.mpr
      (congrArg
        (fun carrier : Set (lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)) =>
          zetaCompletedZeroSideCoordinateL1FiniteRightInverse S a ∈ carrier)
        hdense.symm)
      (Set.mem_univ (zetaCompletedZeroSideCoordinateL1FiniteRightInverse S a))

/-- A finite completed-zero coordinate target has admissible probes whose
`l1` coordinate vector approximates its canonical finite-support right
inverse to every positive tolerance. -/
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
          hbranch
          hpartialOneTwo
          hcompactOneTwo
          hfinite
          hpartialLeft
          hcompactBoundary
          f) < epsilon := by
  have hclosure :
      zetaCompletedZeroSideCoordinateL1FiniteRightInverse S a ∈
        closure
          (Set.range
            (zetaCompletedZeroSideCoordinateL1LinearMap
              hbranch
              hpartialOneTwo
              hcompactOneTwo
              hfinite
              hpartialLeft
              hcompactBoundary)) := by
    exact
      zetaCompletedZeroSideCoordinateL1FiniteRightInverse_mem_closure
        hbranch
        hpartialOneTwo
        hcompactOneTwo
        hfinite
        hpartialLeft
        hcompactBoundary
        S a
  obtain ⟨f, hf⟩ :=
    (mem_closure_range_iff.mp hclosure) epsilon hepsilon
  exact ⟨f, hf⟩

/-- The `l1` finite-right-inverse approximation controls every coordinate in
the prescribed finite completed-zero window. -/
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
            hbranch
            hpartialOneTwo
            hcompactOneTwo
            hfinite
            hpartialLeft
            hcompactBoundary
            f
            (rho : ZetaCompletedZeroCoordinate)) < epsilon := by
  obtain ⟨f, hf⟩ :=
    exists_zetaCompletedZeroSideCoordinateL1_approximation_of_finiteRightInverse
      hbranch
      hpartialOneTwo
      hcompactOneTwo
      hfinite
      hpartialLeft
      hcompactBoundary
      S a epsilon hepsilon
  have hwindowApproximation :
      ∀ rho : S,
        dist
          (a rho)
          (zetaCompletedZeroSideCoordinateLinearMap
            hbranch
            hpartialOneTwo
            hcompactOneTwo
            hfinite
            hpartialLeft
            hcompactBoundary
            f
            (rho : ZetaCompletedZeroCoordinate)) < epsilon := by
    intro rho
    have hpoint :
      dist
        (zetaCompletedZeroSideCoordinateL1FiniteRightInverse S a
          (rho : ZetaCompletedZeroCoordinate))
        (zetaCompletedZeroSideCoordinateL1LinearMap
          hbranch
          hpartialOneTwo
          hcompactOneTwo
          hfinite
          hpartialLeft
          hcompactBoundary
          f
          (rho : ZetaCompletedZeroCoordinate)) ≤
        dist
          (zetaCompletedZeroSideCoordinateL1FiniteRightInverse S a)
          (zetaCompletedZeroSideCoordinateL1LinearMap
            hbranch
            hpartialOneTwo
            hcompactOneTwo
            hfinite
            hpartialLeft
            hcompactBoundary
            f) := by
    exact
      lp.norm_apply_le_norm
        ENNReal.one_ne_zero
        (zetaCompletedZeroSideCoordinateL1FiniteRightInverse S a -
          zetaCompletedZeroSideCoordinateL1LinearMap
            hbranch
            hpartialOneTwo
            hcompactOneTwo
            hfinite
            hpartialLeft
            hcompactBoundary
            f)
        (rho : ZetaCompletedZeroCoordinate)
    calc
      dist
        (a rho)
        (zetaCompletedZeroSideCoordinateL1LinearMap
          hbranch
          hpartialOneTwo
          hcompactOneTwo
          hfinite
          hpartialLeft
          hcompactBoundary
          f
          (rho : ZetaCompletedZeroCoordinate)) =
        dist
          (zetaCompletedZeroSideCoordinateL1FiniteRightInverse S a
            (rho : ZetaCompletedZeroCoordinate))
          (zetaCompletedZeroSideCoordinateL1LinearMap
            hbranch
            hpartialOneTwo
            hcompactOneTwo
            hfinite
            hpartialLeft
            hcompactBoundary
            f
            (rho : ZetaCompletedZeroCoordinate)) := by
          exact
            congrArg
              (fun coordinate : ℂ =>
                dist coordinate
                  (zetaCompletedZeroSideCoordinateL1LinearMap
                    hbranch
                    hpartialOneTwo
                    hcompactOneTwo
                    hfinite
                    hpartialLeft
                    hcompactBoundary
                    f
                    (rho : ZetaCompletedZeroCoordinate)))
              (zetaCompletedZeroSideCoordinateL1FiniteRightInverse_apply S a rho).symm
    _ ≤
        dist
          (zetaCompletedZeroSideCoordinateL1FiniteRightInverse S a)
          (zetaCompletedZeroSideCoordinateL1LinearMap
            hbranch
            hpartialOneTwo
            hcompactOneTwo
            hfinite
            hpartialLeft
            hcompactBoundary
            f) := hpoint
      _ < epsilon := hf
  exact ⟨f, hwindowApproximation⟩

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
