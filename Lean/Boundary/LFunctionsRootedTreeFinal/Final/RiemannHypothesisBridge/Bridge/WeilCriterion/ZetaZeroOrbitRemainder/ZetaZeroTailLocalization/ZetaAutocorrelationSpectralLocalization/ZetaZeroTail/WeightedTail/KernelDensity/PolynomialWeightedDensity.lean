import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.FiniteSpectralZeroCarrierSeparation
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.AtomicDistributionUniqueness
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.PolynomialMultiplierGrowth
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.DualRepresentation.Owner
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Module.Dual

/-!
# Polynomial-weighted completed-zero coordinate density

This is the analytic density owner needed after finite spectral constraints have
been converted into a constant-coefficient differential multiplier.  The
finite-set kernel condition itself is not assumed here.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

theorem lp_one_norm_eq_tsum_norm
    (x : lp (fun rho : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)) :
    ‖x‖ = ∑' rho : ZetaCompletedZeroCoordinate, ‖x rho‖ := by
  have honePositive : 0 < (1 : ENNReal).toReal :=
    Eq.subst
      (motive := fun exponent : ℝ => 0 < exponent)
      ENNReal.one_toReal.symm
      zero_lt_one
  have hnormPower := lp.norm_rpow_eq_tsum honePositive x
  have hleft : ‖x‖ ^ (1 : ENNReal).toReal = ‖x‖ := by
    exact Eq.trans
      (congrArg (fun exponent : ℝ => ‖x‖ ^ exponent) ENNReal.one_toReal)
      (Real.rpow_one ‖x‖)
  have hright :
      (∑' rho : ZetaCompletedZeroCoordinate,
        ‖x rho‖ ^ (1 : ENNReal).toReal) =
        ∑' rho : ZetaCompletedZeroCoordinate, ‖x rho‖ :=
    tsum_congr
      (fun rho : ZetaCompletedZeroCoordinate =>
        Eq.trans
          (congrArg
            (fun exponent : ℝ => ‖x rho‖ ^ exponent)
            ENNReal.one_toReal)
          (Real.rpow_one ‖x rho‖))
  exact Eq.trans hleft.symm (Eq.trans hnormPower hright)

noncomputable def polynomialWeightedCompletedZeroCoordinateLinearMap
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (P : Finset ℂ) :
    ZetaAdmissibleFunction →ₗ[ℂ]
      lp (fun rho : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal) :=
  (zetaCompletedZeroSideCoordinateL1LinearMap
    hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary).comp
      (finiteSpectralZeroLinearMap P)

theorem polynomialWeightedCompletedZeroCoordinateLinearMap_apply
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (P : Finset ℂ)
    (f : ZetaAdmissibleFunction)
    (rho : ZetaCompletedZeroCoordinate) :
    polynomialWeightedCompletedZeroCoordinateLinearMap
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
        P f rho =
      finiteSpectralZeroMultiplier P (rho : ℂ) *
        zetaZeroSideContribution (rho : ℂ) f := by
  exact Eq.trans
    (zetaCompletedZeroSideCoordinateL1LinearMap_apply
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      (finiteSpectralZeroOperator P f) rho)
    (finiteSpectralZeroMultiplier_eq_operatorMultiplier P f (rho : ℂ))

theorem polynomialWeightedCompletedZeroAnnihilator_coefficients_vanish_off_finiteSet
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (P : Finset ℂ)
    (b : lp (fun rho : ZetaCompletedZeroCoordinate => ℂ) (⊤ : ENNReal))
    (hvanishing :
      ∀ f : ZetaAdmissibleFunction,
        zetaCompletedZeroSideL1DualPairing b
          (polynomialWeightedCompletedZeroCoordinateLinearMap
            hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
            P f) = 0) :
    ∀ rho : ZetaCompletedZeroCoordinate,
      (rho : ℂ) ∉ P → b rho = 0 := by
  let coefficient : ZetaCompletedZeroCoordinate → ℂ :=
    fun rho =>
      b rho *
        (finiteSpectralZeroMultiplier P (rho : ℂ) *
          -((zetaZeroMultiplicity (rho : ℂ) : ℂ)))
  have hseriesIdentity :
      ∀ f : ZetaAdmissibleFunction,
        (fun rho : ZetaCompletedZeroCoordinate =>
          b rho *
            polynomialWeightedCompletedZeroCoordinateLinearMap
              hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
              P f rho) =
        (fun rho : ZetaCompletedZeroCoordinate =>
          coefficient rho * zetaSpectralEval f (rho : ℂ)) := by
    intro f
    funext rho
    have hcoordinate := polynomialWeightedCompletedZeroCoordinateLinearMap_apply
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      P f rho
    unfold coefficient
    unfold zetaZeroSideContribution at hcoordinate
    exact Eq.trans
      (congrArg (fun value : ℂ => b rho * value) hcoordinate)
      (calc
        b rho *
            (finiteSpectralZeroMultiplier P (rho : ℂ) *
              (-((zetaZeroMultiplicity (rho : ℂ) : ℂ)) *
                zetaSpectralEval f (rho : ℂ))) =
            b rho *
              ((finiteSpectralZeroMultiplier P (rho : ℂ) *
                -((zetaZeroMultiplicity (rho : ℂ) : ℂ))) *
                  zetaSpectralEval f (rho : ℂ)) := by
          exact congrArg
            (fun value : ℂ => b rho * value)
            (mul_assoc
              (finiteSpectralZeroMultiplier P (rho : ℂ))
              (-((zetaZeroMultiplicity (rho : ℂ) : ℂ)))
              (zetaSpectralEval f (rho : ℂ))).symm
        _ = (b rho *
              (finiteSpectralZeroMultiplier P (rho : ℂ) *
                -((zetaZeroMultiplicity (rho : ℂ) : ℂ)))) *
              zetaSpectralEval f (rho : ℂ) := by
          exact (mul_assoc
            (b rho)
            (finiteSpectralZeroMultiplier P (rho : ℂ) *
              -((zetaZeroMultiplicity (rho : ℂ) : ℂ)))
            (zetaSpectralEval f (rho : ℂ))).symm)
  have hsummable :
      ∀ f : ZetaAdmissibleFunction,
        Summable
          (fun rho : ZetaCompletedZeroCoordinate =>
            coefficient rho * zetaSpectralEval f (rho : ℂ)) := by
    intro f
    have hpairingSummable :=
      zetaCompletedZeroSideL1DualPairing_summable b
        (polynomialWeightedCompletedZeroCoordinateLinearMap
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary P f)
    exact Eq.mpr
      (congrArg Summable (hseriesIdentity f).symm)
      hpairingSummable
  have hdistributionVanishing :
      ∀ f : ZetaAdmissibleFunction,
        (∑' rho : ZetaCompletedZeroCoordinate,
          coefficient rho * zetaSpectralEval f (rho : ℂ)) = 0 := by
    intro f
    unfold zetaCompletedZeroSideL1DualPairing at hvanishing
    exact Eq.trans
      (congrArg tsum (hseriesIdentity f).symm)
      (hvanishing f)
  have hcoefficientZero : coefficient = 0 :=
    completedZeroAtomicLaplaceDistribution_coefficients_eq_zero
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      coefficient
      (show CompletedZeroAtomicPolynomialGrowth coefficient from
        polynomialWeightedCompletedZeroAtomicCoefficient_growth
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
          P b)
      hsummable hdistributionVanishing
  intro rho hrho
  have hcoefficientAt : coefficient rho = 0 :=
    congrArg (fun values : ZetaCompletedZeroCoordinate → ℂ => values rho)
      hcoefficientZero
  change
    b rho *
      (finiteSpectralZeroMultiplier P (rho : ℂ) *
        -((zetaZeroMultiplicity (rho : ℂ) : ℂ))) = 0 at hcoefficientAt
  have hmultiplierNonzero : finiteSpectralZeroMultiplier P (rho : ℂ) ≠ 0 :=
    finiteSpectralZeroMultiplier_ne_zero_of_not_mem P (rho : ℂ) hrho
  have hmultiplicityPositive : 0 < zetaZeroMultiplicity (rho : ℂ) :=
    zetaZeroMultiplicity_pos_of_completedZero rho
  have hmultiplicityNonzero :
      -((zetaZeroMultiplicity (rho : ℂ) : ℂ)) ≠ 0 :=
    neg_ne_zero.mpr
      (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hmultiplicityPositive))
  have hfactorNonzero :
      finiteSpectralZeroMultiplier P (rho : ℂ) *
        -((zetaZeroMultiplicity (rho : ℂ) : ℂ)) ≠ 0 :=
    mul_ne_zero hmultiplierNonzero hmultiplicityNonzero
  exact (mul_eq_zero.mp hcoefficientAt).resolve_right hfactorNonzero

noncomputable def completedZeroCoordinateMask
    (P : Finset ℂ)
    (x : lp (fun rho : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)) :
    lp (fun rho : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal) := by
  let masked : ZetaCompletedZeroCoordinate → ℂ :=
    fun rho => if (rho : ℂ) ∈ P then 0 else x rho
  have honePositive : 0 < (1 : ENNReal).toReal :=
    Eq.subst
      (motive := fun exponent : ℝ => 0 < exponent)
      ENNReal.one_toReal.symm
      zero_lt_one
  have hxSummable := x.2.summable honePositive
  have hmaskedSummable :
      Summable
        (fun rho : ZetaCompletedZeroCoordinate =>
          ‖masked rho‖ ^ (1 : ENNReal).toReal) :=
    Summable.of_nonneg_of_le
      (fun rho =>
        Real.rpow_nonneg (norm_nonneg (masked rho)) (1 : ENNReal).toReal)
      (fun rho =>
        if hmembership : (rho : ℂ) ∈ P then
          have hmaskedZero : masked rho = 0 := if_pos hmembership
          have hzeroPower : ‖masked rho‖ ^ (1 : ENNReal).toReal = 0 := by
            exact Eq.trans
              (congrArg
                (fun value : ℝ => value ^ (1 : ENNReal).toReal)
                (Eq.trans
                  (congrArg norm hmaskedZero)
                  (norm_zero : ‖(0 : ℂ)‖ = 0)))
              (Real.zero_rpow (ne_of_gt honePositive))
          Eq.subst
            (motive := fun value : ℝ => value ≤
              ‖x rho‖ ^ (1 : ENNReal).toReal)
            hzeroPower.symm
            (Real.rpow_nonneg (norm_nonneg (x rho)) (1 : ENNReal).toReal)
        else
          have hmaskedValue : masked rho = x rho := if_neg hmembership
          Eq.subst
            (motive := fun value : ℂ =>
              ‖value‖ ^ (1 : ENNReal).toReal ≤
                ‖x rho‖ ^ (1 : ENNReal).toReal)
            hmaskedValue.symm
            (le_refl (‖x rho‖ ^ (1 : ENNReal).toReal)))
      hxSummable
  exact ⟨masked, memℓp_gen hmaskedSummable⟩

theorem completedZeroCoordinateMask_apply
    (P : Finset ℂ)
    (x : lp (fun rho : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal))
    (rho : ZetaCompletedZeroCoordinate) :
    completedZeroCoordinateMask P x rho =
      if (rho : ℂ) ∈ P then 0 else x rho := by
  rfl

noncomputable def polynomialWeightedCoordinateClosureSubmodule
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (P : Finset ℂ) :
    Submodule ℂ (lp (fun rho : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)) :=
  (LinearMap.range
    (polynomialWeightedCompletedZeroCoordinateLinearMap
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary P)).topologicalClosure

theorem exists_continuousLinear_separator_of_not_mem_closedSubmodule
    (S : Submodule ℂ
      (lp (fun rho : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)))
    (hSclosed : IsClosed
      (S : Set (lp (fun rho : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal))))
    (x : lp (fun rho : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal))
    (hx : x ∉ S) :
    ∃ L : lp (fun rho : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal) →L[ℂ] ℂ,
      (∀ y : lp (fun rho : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal),
        y ∈ S → L y = 0) ∧ L x ≠ 0 := by
  letI : IsClosed
      (S : Set (lp (fun rho : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal))) :=
    hSclosed
  let q :
      lp (fun rho : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal) →L[ℂ]
        (lp (fun rho : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal) ⧸ S) :=
    LinearMap.mkContinuous S.mkQ (1 : ℝ)
      (fun value =>
        calc
          ‖S.mkQ value‖ ≤ ‖value‖ :=
            Submodule.Quotient.norm_mk_le S value
          _ = (1 : ℝ) * ‖value‖ :=
            (one_mul ‖value‖).symm)
  have hqx : q x ≠ 0 := by
    intro hzero
    have hquotientZero : S.mkQ x = 0 := hzero
    exact hx ((Submodule.Quotient.mk_eq_zero S).mp hquotientZero)
  obtain ⟨g, hgnorm, hgvalue⟩ := exists_dual_vector ℂ (q x) hqx
  let L : lp (fun rho : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal) →L[ℂ] ℂ :=
    g.comp q
  have hLvanishes :
      ∀ y : lp (fun rho : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal),
        y ∈ S → L y = 0 :=
    fun y hy => by
      have hquotientZero : S.mkQ y = 0 :=
        (Submodule.Quotient.mk_eq_zero S).mpr hy
      exact Eq.trans
        (congrArg g hquotientZero)
        (g.map_zero)
  have hLx : L x ≠ 0 := by
    intro hzero
    have hnormZero : ‖q x‖ = 0 := by
      have hcomplexNormZero : (‖q x‖ : ℂ) = 0 :=
        Eq.trans hgvalue.symm hzero
      exact Complex.ofReal_eq_zero.mp hcomplexNormZero
    exact hqx (norm_eq_zero.mp hnormZero)
  exact ⟨L, hLvanishes, hLx⟩

theorem completedZeroCoordinateMask_not_mem_polynomialWeightedCoordinateClosure_impossible
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (P : Finset ℂ)
    (target : lp (fun rho : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal))
    (hnotMember : completedZeroCoordinateMask P target ∉
      polynomialWeightedCoordinateClosureSubmodule
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary P) :
    False := by
  let S := polynomialWeightedCoordinateClosureSubmodule
    hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary P
  have hSclosed : IsClosed
      (S : Set (lp (fun rho : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal))) :=
    Submodule.isClosed_topologicalClosure
      (LinearMap.range
        (polynomialWeightedCompletedZeroCoordinateLinearMap
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary P))
  obtain ⟨L, hLvanishes, hLnonzero⟩ :=
    exists_continuousLinear_separator_of_not_mem_closedSubmodule
      S hSclosed (completedZeroCoordinateMask P target) hnotMember
  obtain ⟨b, hrepresentation⟩ :=
    exists_zetaCompletedZeroSideL1DualRepresentation L
  have hcoordinateVanishing :
      ∀ f : ZetaAdmissibleFunction,
        zetaCompletedZeroSideL1DualPairing b
          (polynomialWeightedCompletedZeroCoordinateLinearMap
            hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
            P f) = 0 := by
    intro f
    have hrange :
        polynomialWeightedCompletedZeroCoordinateLinearMap
            hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
            P f ∈ S :=
      by
        change
          polynomialWeightedCompletedZeroCoordinateLinearMap
              hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
              P f ∈
            closure
              (LinearMap.range
                (polynomialWeightedCompletedZeroCoordinateLinearMap
                  hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft
                  hcompactBoundary P) :
                Set
                  (lp
                    (fun rho : ZetaCompletedZeroCoordinate => ℂ)
                    (1 : ENNReal)))
        exact subset_closure
          (LinearMap.mem_range_self
            (polynomialWeightedCompletedZeroCoordinateLinearMap
              hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary P)
            f)
    exact Eq.trans
      (hrepresentation
        (polynomialWeightedCompletedZeroCoordinateLinearMap
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
          P f)).symm
      (hLvanishes
        (polynomialWeightedCompletedZeroCoordinateLinearMap
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
          P f)
        hrange)
  have hbOffFinite :
      ∀ rho : ZetaCompletedZeroCoordinate,
        (rho : ℂ) ∉ P → b rho = 0 :=
    polynomialWeightedCompletedZeroAnnihilator_coefficients_vanish_off_finiteSet
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      P b hcoordinateVanishing
  have hpairingZero :
      zetaCompletedZeroSideL1DualPairing b
        (completedZeroCoordinateMask P target) = 0 := by
    unfold zetaCompletedZeroSideL1DualPairing
    have hzeroSeries :
        (fun rho : ZetaCompletedZeroCoordinate =>
          b rho * completedZeroCoordinateMask P target rho) =
        (fun rho : ZetaCompletedZeroCoordinate => (0 : ℂ)) := by
      funext rho
      if hmembership : (rho : ℂ) ∈ P then
        exact Eq.trans
          (congrArg
            (fun value : ℂ => b rho * value)
            (Eq.trans
              (completedZeroCoordinateMask_apply P target rho)
              (if_pos hmembership)))
          (mul_zero (b rho))
      else
        exact Eq.trans
          (congrArg
            (fun coefficient : ℂ =>
              coefficient * completedZeroCoordinateMask P target rho)
            (hbOffFinite rho hmembership))
          (zero_mul (completedZeroCoordinateMask P target rho))
    exact Eq.trans (congrArg tsum hzeroSeries) tsum_zero
  exact hLnonzero
    (Eq.trans
      (hrepresentation (completedZeroCoordinateMask P target))
      hpairingZero)

theorem completedZeroCoordinateMask_mem_polynomialWeightedCoordinateClosure
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (P : Finset ℂ)
    (target : lp (fun rho : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)) :
    completedZeroCoordinateMask P target ∈
      polynomialWeightedCoordinateClosureSubmodule
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary P :=
  by_contradiction
    (fun hnotMember =>
      completedZeroCoordinateMask_not_mem_polynomialWeightedCoordinateClosure_impossible
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary P target
        hnotMember)

theorem dist_completedZeroCoordinateMask_polynomialWeightedCoordinate_eq_complement_tsum
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (P : Finset ℂ)
    (target : lp (fun rho : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal))
    (f : ZetaAdmissibleFunction) :
    dist (completedZeroCoordinateMask P target)
        (polynomialWeightedCompletedZeroCoordinateLinearMap
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
          P f) =
      ∑' rho : ZetaCompletedZeroCoordinate,
        if (rho : ℂ) ∈ P then 0
        else
          ‖target rho -
            finiteSpectralZeroMultiplier P (rho : ℂ) *
              zetaZeroSideContribution (rho : ℂ) f‖ := by
  let A := polynomialWeightedCompletedZeroCoordinateLinearMap
    hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary P
  have hpointwise :
      (fun rho : ZetaCompletedZeroCoordinate =>
        ‖(completedZeroCoordinateMask P target - A f) rho‖) =
      (fun rho : ZetaCompletedZeroCoordinate =>
        if (rho : ℂ) ∈ P then 0
        else
          ‖target rho -
            finiteSpectralZeroMultiplier P (rho : ℂ) *
              zetaZeroSideContribution (rho : ℂ) f‖) := by
    funext rho
    if hmembership : (rho : ℂ) ∈ P then
      have hspectralZero :
          zetaSpectralEval (finiteSpectralZeroOperator P f) (rho : ℂ) = 0 :=
        zetaSpectralEval_finiteSpectralZeroOperator_eq_zero_of_mem
          P f (rho : ℂ) hmembership
      have hsideZero :
          zetaZeroSideContribution (rho : ℂ) (finiteSpectralZeroOperator P f) = 0 :=
        zetaZeroSideContribution_eq_zero_of_zetaSpectralEval_eq_zero
          (rho : ℂ) (finiteSpectralZeroOperator P f) hspectralZero
      have hcoordinateZero : A f rho = 0 :=
        Eq.trans
          (zetaCompletedZeroSideCoordinateL1LinearMap_apply
            hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft
            hcompactBoundary (finiteSpectralZeroOperator P f) rho)
          hsideZero
      have hmaskZero : completedZeroCoordinateMask P target rho = 0 :=
        Eq.trans
          (completedZeroCoordinateMask_apply P target rho)
          (if_pos hmembership)
      have hsubApply :
          (completedZeroCoordinateMask P target - A f) rho =
            completedZeroCoordinateMask P target rho - A f rho := rfl
      have hnormZero :
          ‖(completedZeroCoordinateMask P target - A f) rho‖ = 0 :=
        Eq.trans
          (congrArg norm hsubApply)
          (Eq.trans
            (congrArg norm
              (Eq.trans
                (congrArg₂ HSub.hSub hmaskZero hcoordinateZero)
                (sub_self (0 : ℂ))))
            (norm_zero : ‖(0 : ℂ)‖ = 0))
      exact Eq.trans hnormZero (if_pos hmembership).symm
    else
      have hmaskValue : completedZeroCoordinateMask P target rho = target rho :=
        Eq.trans
          (completedZeroCoordinateMask_apply P target rho)
          (if_neg hmembership)
      have hcoordinateValue :
          A f rho =
            finiteSpectralZeroMultiplier P (rho : ℂ) *
              zetaZeroSideContribution (rho : ℂ) f :=
        polynomialWeightedCompletedZeroCoordinateLinearMap_apply
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft
          hcompactBoundary P f rho
      have hsubApply :
          (completedZeroCoordinateMask P target - A f) rho =
            completedZeroCoordinateMask P target rho - A f rho := rfl
      have hnormValue :
          ‖(completedZeroCoordinateMask P target - A f) rho‖ =
            ‖target rho -
              finiteSpectralZeroMultiplier P (rho : ℂ) *
                zetaZeroSideContribution (rho : ℂ) f‖ :=
        Eq.trans
          (congrArg norm hsubApply)
          (congrArg norm
            (congrArg₂ HSub.hSub hmaskValue hcoordinateValue))
      exact Eq.trans hnormValue (if_neg hmembership).symm
  exact Eq.trans
    (dist_eq_norm (completedZeroCoordinateMask P target) (A f))
    (Eq.trans
      (lp_one_norm_eq_tsum_norm (completedZeroCoordinateMask P target - A f))
      (congrArg tsum hpointwise))

/-- The polynomial-weighted coordinate range comes arbitrarily close to the
masked completed-zero target. -/
theorem exists_polynomialWeightedCoordinate_near_completedZeroCoordinateMask
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (P : Finset ℂ)
    (target : lp (fun rho : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal))
    (epsilon : ℝ)
    (hepsilon : 0 < epsilon) :
    ∃ f : ZetaAdmissibleFunction,
      dist (completedZeroCoordinateMask P target)
        (polynomialWeightedCompletedZeroCoordinateLinearMap
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
          P f) < epsilon := by
  let A := polynomialWeightedCompletedZeroCoordinateLinearMap
    hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary P
  have hclosureSubmodule :=
    completedZeroCoordinateMask_mem_polynomialWeightedCoordinateClosure
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      P target
  have hclosureRangeSubmodule :
      completedZeroCoordinateMask P target ∈
        closure
          (LinearMap.range A :
            Set (lp (fun rho : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal))) := by
    exact Eq.mp
      (congrArg
        (fun carrier : Set
          (lp (fun rho : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)) =>
            completedZeroCoordinateMask P target ∈ carrier)
        (Submodule.topologicalClosure_coe (LinearMap.range A)))
      hclosureSubmodule
  have hrangeEquality :
      (LinearMap.range A :
        Set (lp (fun rho : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal))) =
      Set.range A := by
    exact Set.ext
      (fun value =>
        Iff.intro
          (fun hvalue =>
            match hvalue with
            | ⟨f, hf⟩ => ⟨f, hf⟩)
          (fun hvalue =>
            match hvalue with
            | ⟨f, hf⟩ => ⟨f, hf⟩))
  have hclosureRange :
      completedZeroCoordinateMask P target ∈ closure (Set.range A) :=
    Eq.mp
      (congrArg
        (fun carrier : Set
          (lp (fun rho : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)) =>
            completedZeroCoordinateMask P target ∈ closure carrier)
        hrangeEquality)
      hclosureRangeSubmodule
  have hnearRange :
      ∃ value ∈ Set.range A,
        dist (completedZeroCoordinateMask P target) value < epsilon :=
    (Metric.mem_closure_iff.mp hclosureRange) epsilon hepsilon
  obtain ⟨value, hvalueRange, hdistanceValue⟩ := hnearRange
  obtain ⟨f, hf⟩ := hvalueRange
  have hdistance :
      dist (completedZeroCoordinateMask P target) (A f) < epsilon :=
    Eq.subst
      (motive := fun candidate :
        lp (fun rho : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal) =>
          dist (completedZeroCoordinateMask P target) candidate < epsilon)
      hf.symm
      hdistanceValue
  exact ⟨f, hdistance⟩

theorem exists_polynomialWeighted_completedZeroSideCoordinate_approximation
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (P : Finset ℂ)
    (target : lp (fun rho : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal))
    (epsilon : ℝ)
    (hepsilon : 0 < epsilon) :
    ∃ f : ZetaAdmissibleFunction,
      (∑' rho : ZetaCompletedZeroCoordinate,
        if (rho : ℂ) ∈ P then 0
        else
          ‖target rho -
            finiteSpectralZeroMultiplier P (rho : ℂ) *
              zetaZeroSideContribution (rho : ℂ) f‖) < epsilon := by
  obtain ⟨f, hdistance⟩ :=
    exists_polynomialWeightedCoordinate_near_completedZeroCoordinateMask
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      P target epsilon hepsilon
  exact ⟨f,
    Eq.subst
      (motive := fun value : ℝ => value < epsilon)
      (dist_completedZeroCoordinateMask_polynomialWeightedCoordinate_eq_complement_tsum
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
        P target f)
      hdistance⟩

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
