import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Annihilator.DistributionalClassification.Vanishing
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Annihilator.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.DualRepresentation.Owner
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Module.Dual

/-!
# Hahn-Banach separation for completed-zero coordinate density

This owner part isolates the quotient-map and separating-functional mechanism
used to turn annihilator uniqueness into density of admissible completed-zero
coordinates.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

open scoped ENNReal

theorem quotient_norm_le_one_mul
    {E : Type}
    [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    (S : Submodule ℂ E)
    (x : E) :
    norm (S.mkQ x) ≤ (1 : ℝ) * norm x :=
  le_trans
    (Submodule.Quotient.norm_mk_le S x)
    (le_of_eq (one_mul (norm x)).symm)

noncomputable def zetaCompletedZeroSideCoordinateL1QuotientMap
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal) →L[ℂ]
      (lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal) ⧸
        zetaCompletedZeroSideCoordinateL1ClosureSubmodule
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary) :=
  let S :
      Submodule ℂ (lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)) :=
    zetaCompletedZeroSideCoordinateL1ClosureSubmodule
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
  let hSClosed : IsClosed
      (S : Set (lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal))) :=
    isClosed_zetaCompletedZeroSideCoordinateL1ClosureSubmodule
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
  haveI : IsClosed
      (S : Set (lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal))) :=
    hSClosed
  LinearMap.mkContinuous S.mkQ (1 : ℝ)
    (fun x => quotient_norm_le_one_mul S x)

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
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f) = 0 :=
  let S :
      Submodule ℂ (lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)) :=
    zetaCompletedZeroSideCoordinateL1ClosureSubmodule
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
  let hcoordinate :
      zetaCompletedZeroSideCoordinateL1LinearMap
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f ∈ S :=
    mem_zetaCompletedZeroSideCoordinateL1ClosureSubmodule
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f
  show S.mkQ
      (zetaCompletedZeroSideCoordinateL1LinearMap
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f) = 0 from
    (Submodule.Quotient.mk_eq_zero S).mpr hcoordinate

theorem quotient_coordinate_ne_zero_of_not_mem_closureSubmodule
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (x : lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal))
    (hx : x ∉ zetaCompletedZeroSideCoordinateL1ClosureSubmodule
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary) :
    zetaCompletedZeroSideCoordinateL1QuotientMap
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary x ≠ 0 :=
  let S :
      Submodule ℂ (lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)) :=
    zetaCompletedZeroSideCoordinateL1ClosureSubmodule
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
  fun hzero =>
    hx
      ((Submodule.Quotient.mk_eq_zero S).mp
        (show S.mkQ x = 0 from hzero))

theorem composed_quotient_separator_vanishes_on_coordinates
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (q :
      lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal) →L[ℂ]
        (lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal) ⧸
          zetaCompletedZeroSideCoordinateL1ClosureSubmodule
            hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary))
    (g :
      (lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal) ⧸
        zetaCompletedZeroSideCoordinateL1ClosureSubmodule
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary) →L[ℂ] ℂ)
    (hq :
      q =
        zetaCompletedZeroSideCoordinateL1QuotientMap
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary) :
    ∀ f : ZetaAdmissibleFunction,
      (g.comp q)
        (zetaCompletedZeroSideCoordinateL1LinearMap
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f) = 0 :=
  fun f =>
    let hqCoordinate :
        q
          (zetaCompletedZeroSideCoordinateL1LinearMap
            hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f) = 0 :=
      Eq.trans
        (congrArg
          (fun map :
            lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal) →L[ℂ]
              (lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal) ⧸
                zetaCompletedZeroSideCoordinateL1ClosureSubmodule
                  hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary) =>
              map
                (zetaCompletedZeroSideCoordinateL1LinearMap
                  hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f))
          hq)
        (zetaCompletedZeroSideCoordinateL1QuotientMap_apply_coordinate
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f)
    Eq.trans (congrArg g hqCoordinate) (map_zero g)

theorem composed_quotient_separator_ne_zero_at_vector
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (q :
      lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal) →L[ℂ]
        (lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal) ⧸
          zetaCompletedZeroSideCoordinateL1ClosureSubmodule
            hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary))
    (g :
      (lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal) ⧸
        zetaCompletedZeroSideCoordinateL1ClosureSubmodule
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary) →L[ℂ] ℂ)
    (x : lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal))
    (hqx : q x ≠ 0)
    (hgValue : ↑(norm (q x)) = g (q x)) :
    (g.comp q) x ≠ 0 :=
  let S :
      Submodule ℂ (lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)) :=
    zetaCompletedZeroSideCoordinateL1ClosureSubmodule
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
  let hSClosed : IsClosed
      (S : Set (lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal))) :=
    isClosed_zetaCompletedZeroSideCoordinateL1ClosureSubmodule
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
  haveI : IsClosed
      (S : Set (lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal))) :=
    hSClosed
  fun hzero =>
    let hcoercedNormZero : (norm (q x) : ℂ) = 0 :=
      Eq.trans hgValue hzero
    let hnormZero : norm (q x) = 0 :=
      Complex.ofReal_eq_zero.mp hcoercedNormZero
    hqx (norm_eq_zero.mp hnormZero)

theorem exists_zetaCompletedZeroSideCoordinateL1_separator
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (x : lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal))
    (hx : x ∉ zetaCompletedZeroSideCoordinateL1ClosureSubmodule
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary) :
    ∃ L : lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal) →L[ℂ] ℂ,
      (∀ f : ZetaAdmissibleFunction,
        L (zetaCompletedZeroSideCoordinateL1LinearMap
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f) = 0) ∧
      L x ≠ 0 :=
  let S :
      Submodule ℂ (lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)) :=
    zetaCompletedZeroSideCoordinateL1ClosureSubmodule
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
  let hSClosed : IsClosed
      (S : Set (lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal))) :=
    isClosed_zetaCompletedZeroSideCoordinateL1ClosureSubmodule
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
  haveI : IsClosed
      (S : Set (lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal))) :=
    hSClosed
  let q :
      lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal) →L[ℂ]
        (lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal) ⧸
          zetaCompletedZeroSideCoordinateL1ClosureSubmodule
            hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary) :=
    zetaCompletedZeroSideCoordinateL1QuotientMap
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
  let hqx : q x ≠ 0 :=
    quotient_coordinate_ne_zero_of_not_mem_closureSubmodule
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary x hx
  match exists_dual_vector ℂ (q x) hqx with
  | ⟨g, hgNorm, hgValue⟩ =>
      let L : lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal) →L[ℂ] ℂ :=
        g.comp q
      let hcoordinateVanishes :
          ∀ f : ZetaAdmissibleFunction,
            L (zetaCompletedZeroSideCoordinateL1LinearMap
              hbranch hpartialOneTwo hcompactOneTwo hfinite
              hpartialLeft hcompactBoundary f) = 0 :=
        composed_quotient_separator_vanishes_on_coordinates
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
          q g (Eq.refl q)
      let hnonzero : L x ≠ 0 :=
        composed_quotient_separator_ne_zero_at_vector
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
          q g x hqx hgValue.symm
      ⟨L, hcoordinateVanishes, hnonzero⟩

theorem not_mem_closureSet_to_not_mem_closureSubmodule
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (x : lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal))
    (hx :
      x ∉ zetaCompletedZeroSideCoordinateL1Closure
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary) :
    x ∉ zetaCompletedZeroSideCoordinateL1ClosureSubmodule
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary :=
  fun hxSubmoduleMembership =>
    hx
      (Eq.mpr
        (congrArg
          (fun carrier :
            Set (lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)) =>
            x ∈ carrier)
          (zetaCompletedZeroSideCoordinateL1Closure_eq_closureSubmodule
            hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary))
        hxSubmoduleMembership)

theorem zetaCompletedZeroSideL1DualPairing_eq_tsum
    (b : lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (x : lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)) :
    zetaCompletedZeroSideL1DualPairing b x =
      tsum
        (fun rho : ZetaCompletedZeroCoordinate =>
          b rho * x rho) :=
  Eq.refl
    (tsum
      (fun rho : ZetaCompletedZeroCoordinate =>
        b rho * x rho))

theorem zetaCompletedZeroSideAnnihilator_eq_pairing_on_coordinate
    (b : lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroSideAnnihilator
        b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f =
      zetaCompletedZeroSideL1DualPairing b
        (zetaCompletedZeroSideCoordinateL1LinearMap
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f) :=
  Eq.refl
    (zetaCompletedZeroSideL1DualPairing b
      (zetaCompletedZeroSideCoordinateL1LinearMap
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f))

theorem separator_annihilator_vanishes_of_representation
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (L : lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal) →L[ℂ] ℂ)
    (b : lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (hLcoordinate :
      ∀ f : ZetaAdmissibleFunction,
        L (zetaCompletedZeroSideCoordinateL1LinearMap
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f) = 0)
    (hrepresentation :
      ∀ x : lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal),
        L x = zetaCompletedZeroSideL1DualPairing b x) :
    ZetaCompletedZeroSideAnnihilatorVanishes
      b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary :=
  fun f =>
    Eq.trans
      (zetaCompletedZeroSideAnnihilator_eq_pairing_on_coordinate
        b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f)
      (Eq.trans
        (hrepresentation
          (zetaCompletedZeroSideCoordinateL1LinearMap
            hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f)).symm
        (hLcoordinate f))

theorem zetaCompletedZeroSideL1DualPairing_zero_coefficient
    (x : lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)) :
    zetaCompletedZeroSideL1DualPairing
      (0 : lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal)) x = 0 :=
  let hzeroSeries :
      (fun rho : ZetaCompletedZeroCoordinate =>
        (0 : lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal)) rho *
          x rho) =
        (fun rho : ZetaCompletedZeroCoordinate => (0 : ℂ)) :=
    funext
      (fun rho : ZetaCompletedZeroCoordinate =>
        zero_mul (x rho))
  Eq.trans
    (zetaCompletedZeroSideL1DualPairing_eq_tsum
      (0 : lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
      x)
    (Eq.trans
      (congrArg tsum hzeroSeries)
      (tsum_zero : tsum (fun rho : ZetaCompletedZeroCoordinate => (0 : ℂ)) = 0))

theorem separator_value_zero_of_zero_representing_coefficient
    (L : lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal) →L[ℂ] ℂ)
    (b : lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (x : lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal))
    (hrepresentation :
      ∀ y : lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal),
        L y = zetaCompletedZeroSideL1DualPairing b y)
    (hbZero : b = 0) :
    L x = 0 :=
  Eq.trans
    (hrepresentation x)
    (Eq.trans
      (congrArg
        (fun coefficient =>
          zetaCompletedZeroSideL1DualPairing coefficient x)
        hbZero)
      (zetaCompletedZeroSideL1DualPairing_zero_coefficient x))

theorem zetaCompletedZeroSideCoordinateL1Closure_eq_univ_of_annihilatorUniqueness
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (huniqueness :
      ∀ b : lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal),
        ZetaCompletedZeroSideAnnihilatorVanishes
          b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary →
          b = 0) :
    zetaCompletedZeroSideCoordinateL1Closure
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary =
      Set.univ :=
  let closureCarrier :
      Set (lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)) :=
    zetaCompletedZeroSideCoordinateL1Closure
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
  let hnotProper : ¬ closureCarrier ≠ Set.univ :=
    fun hproper =>
      match (Set.ne_univ_iff_exists_not_mem (s := closureCarrier)).mp hproper with
      | ⟨x, hx⟩ =>
          match
            exists_zetaCompletedZeroSideCoordinateL1_separator
              hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
              x
              (not_mem_closureSet_to_not_mem_closureSubmodule
                hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
                x hx) with
          | ⟨L, hLcoordinate, hLnonzero⟩ =>
              match exists_zetaCompletedZeroSideL1DualRepresentation L with
              | ⟨b, hrepresentation⟩ =>
                  let hbAnnihilates :
                      ZetaCompletedZeroSideAnnihilatorVanishes
                        b hbranch hpartialOneTwo hcompactOneTwo hfinite
                          hpartialLeft hcompactBoundary :=
                    separator_annihilator_vanishes_of_representation
                      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
                      L b hLcoordinate hrepresentation
                  let hbZero : b = 0 :=
                    huniqueness b hbAnnihilates
                  let hLxZero : L x = 0 :=
                    separator_value_zero_of_zero_representing_coefficient
                      L b x hrepresentation hbZero
                  hLnonzero hLxZero
  not_ne_iff.mp hnotProper

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
