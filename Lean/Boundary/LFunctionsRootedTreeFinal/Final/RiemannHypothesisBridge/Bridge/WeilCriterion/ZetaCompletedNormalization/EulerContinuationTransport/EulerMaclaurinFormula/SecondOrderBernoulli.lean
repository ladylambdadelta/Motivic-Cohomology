import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.OneIntervalBernoulli
import Mathlib.MeasureTheory.Integral.FundThmCalculus

/-!
# Second-order Bernoulli block calculus

The first periodic Bernoulli remainder has mean zero on every unit block.  Its
canonical zero-endpoint quadratic primitive therefore permits a second
integration by parts without boundary terms.  This file owns that generic
block identity; zeta-specific decay estimates are downstream specializations.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

/-- Zero-endpoint quadratic primitive of the first periodic Bernoulli factor
on the natural-number block `[n,n+1]`. -/
noncomputable def eulerMaclaurinSecondOrderBernoulliBlockPrimitive
    (n : ℕ)
    (x : ℝ) : ℂ :=
  ((((x - (n : ℝ)) ^ 2) / 2 - (x - (n : ℝ)) / 2 : ℝ) : ℂ)

/-- The block primitive differentiates to the affine representative of the
first periodic Bernoulli factor. -/
theorem eulerMaclaurinSecondOrderBernoulliBlockPrimitive_hasDerivAt
    (n : ℕ)
    (x : ℝ) :
    HasDerivAt
      (eulerMaclaurinSecondOrderBernoulliBlockPrimitive n)
      ((x - (n : ℝ) - 1 / 2 : ℝ) : ℂ)
      x := by
  let a : ℝ := n
  have hcoordinate : HasDerivAt (fun y : ℝ => y - a) 1 x :=
    (hasDerivAt_id x).sub_const a
  have hsquareRaw :
      HasDerivAt
        (fun y : ℝ => (y - a) ^ 2)
        (((2 : ℕ) : ℝ) * (x - a) ^ (2 - 1) * 1)
        x :=
    hcoordinate.pow 2
  have hpower : (x - a) ^ (2 - 1) = x - a :=
    pow_one (x - a)
  have hsquareCoefficient :
      (((2 : ℕ) : ℝ) * (x - a) ^ (2 - 1) * 1) =
        2 * (x - a) := by
    calc
      (((2 : ℕ) : ℝ) * (x - a) ^ (2 - 1) * 1) =
          2 * (x - a) ^ (2 - 1) * 1 := rfl
      _ = 2 * (x - a) * 1 :=
        congrArg (fun value : ℝ => 2 * value * 1) hpower
      _ = 2 * (x - a) := mul_one (2 * (x - a))
  have hsquare :
      HasDerivAt
        (fun y : ℝ => (y - a) ^ 2)
        (2 * (x - a))
        x :=
    hsquareRaw.congr_deriv hsquareCoefficient
  have hsquareHalf :
      HasDerivAt
        (fun y : ℝ => ((y - a) ^ 2) / 2)
        ((2 * (x - a)) / 2)
        x :=
    hsquare.div_const 2
  have hcoordinateHalf :
      HasDerivAt
        (fun y : ℝ => (y - a) / 2)
        (1 / 2)
        x :=
    hcoordinate.div_const 2
  have hreal :
      HasDerivAt
        (fun y : ℝ => ((y - a) ^ 2) / 2 - (y - a) / 2)
        ((2 * (x - a)) / 2 - 1 / 2)
        x :=
    hsquareHalf.sub hcoordinateHalf
  have htwo_ne : (2 : ℝ) ≠ 0 := two_ne_zero
  have hdivide : (2 * (x - a)) / 2 = x - a :=
    (div_eq_iff htwo_ne).mpr (mul_comm (2 : ℝ) (x - a))
  have hcoefficient :
      (2 * (x - a)) / 2 - 1 / 2 = x - a - 1 / 2 :=
    congrArg (fun value : ℝ => value - 1 / 2) hdivide
  have hrealTarget :
      HasDerivAt
        (fun y : ℝ => ((y - a) ^ 2) / 2 - (y - a) / 2)
        (x - a - 1 / 2)
        x :=
    hreal.congr_deriv hcoefficient
  have hcomplex := hrealTarget.ofReal_comp
  exact hcomplex

/-- The quadratic block primitive vanishes at the left endpoint. -/
theorem eulerMaclaurinSecondOrderBernoulliBlockPrimitive_leftEndpoint
    (n : ℕ) :
    eulerMaclaurinSecondOrderBernoulliBlockPrimitive n (n : ℝ) = 0 := by
  have hcoordinate : (n : ℝ) - (n : ℝ) = 0 := sub_self (n : ℝ)
  unfold eulerMaclaurinSecondOrderBernoulliBlockPrimitive
  exact Complex.ofReal_eq_zero.mpr
    (Eq.trans
      (congrArg
        (fun value : ℝ => value ^ 2 / 2 - value / 2)
        hcoordinate)
      (Eq.trans
        (congrArg₂ Sub.sub
          (Eq.trans
            (congrArg (fun value : ℝ => value / 2)
              (zero_pow (show (2 : ℕ) ≠ 0 from Nat.succ_ne_zero 1)))
            (zero_div 2))
          (zero_div 2))
        (sub_zero 0)))

/-- The quadratic block primitive vanishes at the right endpoint. -/
theorem eulerMaclaurinSecondOrderBernoulliBlockPrimitive_rightEndpoint
    (n : ℕ) :
    eulerMaclaurinSecondOrderBernoulliBlockPrimitive n ((n : ℝ) + 1) = 0 := by
  have hcoordinate : (n : ℝ) + 1 - (n : ℝ) = 1 :=
    add_sub_cancel_left (n : ℝ) 1
  unfold eulerMaclaurinSecondOrderBernoulliBlockPrimitive
  exact Complex.ofReal_eq_zero.mpr
    (Eq.trans
      (congrArg
        (fun value : ℝ => value ^ 2 / 2 - value / 2)
        hcoordinate)
      (Eq.trans
        (congrArg (fun value : ℝ => value / 2 - 1 / 2) (one_pow 2))
        (sub_self (1 / 2))))

/-- The zero-endpoint quadratic primitive has norm at most one throughout its
unit block.  The deliberately loose constant keeps all later tail estimates
monotone and explicit. -/
theorem eulerMaclaurinSecondOrderBernoulliBlockPrimitive_norm_le_one
    (n : ℕ)
    {x : ℝ}
    (hx : x ∈ Set.Icc (n : ℝ) ((n : ℝ) + 1)) :
    ‖eulerMaclaurinSecondOrderBernoulliBlockPrimitive n x‖ ≤ 1 := by
  let u : ℝ := x - (n : ℝ)
  have huNonnegative : 0 ≤ u := sub_nonneg.mpr hx.1
  have huLeOne : u ≤ 1 := by
    have hsubtract : x - (n : ℝ) ≤ ((n : ℝ) + 1) - (n : ℝ) :=
      sub_le_sub_right hx.2 (n : ℝ)
    have hright : ((n : ℝ) + 1) - (n : ℝ) = 1 :=
      add_sub_cancel_left (n : ℝ) 1
    exact Eq.subst
      (motive := fun value : ℝ => u ≤ value)
      hright
      hsubtract
  have huSquareNonnegative : 0 ≤ u ^ 2 := pow_nonneg huNonnegative 2
  have huSquareLeOne : u ^ 2 ≤ 1 := by
    have hraw : u ^ 2 ≤ (1 : ℝ) ^ 2 :=
      pow_le_pow_left₀ huNonnegative huLeOne 2
    exact Eq.subst
      (motive := fun value : ℝ => u ^ 2 ≤ value)
      (one_pow 2)
      hraw
  have hhalfNonnegative : 0 ≤ (2 : ℝ) := le_of_lt zero_lt_two
  have huSquareHalfNonnegative : 0 ≤ u ^ 2 / 2 :=
    div_nonneg huSquareNonnegative hhalfNonnegative
  have huHalfNonnegative : 0 ≤ u / 2 :=
    div_nonneg huNonnegative hhalfNonnegative
  have huSquareHalfLe : u ^ 2 / 2 ≤ 1 / 2 :=
    div_le_div_of_nonneg_right huSquareLeOne hhalfNonnegative
  have huHalfLe : u / 2 ≤ 1 / 2 :=
    div_le_div_of_nonneg_right huLeOne hhalfNonnegative
  have habsDifference : |u ^ 2 / 2 - u / 2| ≤ 1 := by
    have htriangle :
        |u ^ 2 / 2 - u / 2| ≤ |u ^ 2 / 2| + |u / 2| :=
      abs_sub (u ^ 2 / 2) (u / 2)
    have hremoveAbs :
        |u ^ 2 / 2| + |u / 2| = u ^ 2 / 2 + u / 2 :=
      congrArg₂ Add.add
        (abs_of_nonneg huSquareHalfNonnegative)
        (abs_of_nonneg huHalfNonnegative)
    have hsumHalf : u ^ 2 / 2 + u / 2 ≤ 1 / 2 + 1 / 2 :=
      add_le_add huSquareHalfLe huHalfLe
    have hone : (1 : ℝ) / 2 + 1 / 2 = 1 := by
      have htwoNe : (2 : ℝ) ≠ 0 := two_ne_zero
      calc
        (1 : ℝ) / 2 + 1 / 2 = (1 + 1) / 2 :=
          (add_div 1 1 2).symm
        _ = 2 / 2 :=
          congrArg (fun value : ℝ => value / 2) one_add_one_eq_two
        _ = 1 := div_self htwoNe
    exact le_trans htriangle
      (Eq.subst
        (motive := fun value : ℝ => value ≤ 1)
        hremoveAbs.symm
        (le_trans hsumHalf (le_of_eq hone)))
  have hnorm :
      ‖((u ^ 2 / 2 - u / 2 : ℝ) : ℂ)‖ =
        |u ^ 2 / 2 - u / 2| :=
    RCLike.norm_ofReal (u ^ 2 / 2 - u / 2)
  unfold eulerMaclaurinSecondOrderBernoulliBlockPrimitive
  exact Eq.subst
    (motive := fun value : ℝ => value ≤ 1)
    hnorm.symm
    habsDifference

/-- On the interior of a natural unit block, the primitive derivative is the
project's first periodic Bernoulli factor. -/
theorem eulerMaclaurinSecondOrderBernoulliBlockPrimitive_hasDerivAt_periodic
    (n : ℕ)
    {x : ℝ}
    (hx : x ∈ Set.Ioo (n : ℝ) ((n : ℝ) + 1)) :
    HasDerivAt
      (eulerMaclaurinSecondOrderBernoulliBlockPrimitive n)
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)
      x := by
  have hderivative :=
    eulerMaclaurinSecondOrderBernoulliBlockPrimitive_hasDerivAt n x
  have hperiodic :
      eulerMaclaurinFirstPeriodicBernoulli x =
        x - (n : ℝ) - 1 / 2 :=
    have hright : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 :=
      Nat.cast_add_one n
    have hxOwner : x ∈ Set.Ioo (n : ℝ) (((n + 1 : ℕ) : ℝ)) :=
      ⟨hx.1,
        Eq.subst
          (motive := fun bound : ℝ => x < bound)
          hright.symm
          hx.2⟩
    eulerMaclaurinFirstPeriodicBernoulli_eq_sub_nat_sub_half_on_Ioo n hxOwner
  exact hderivative.congr_deriv (congrArg Complex.ofReal hperiodic.symm)

/-- Generic zero-boundary second integration by parts on one natural-number
block. -/
theorem eulerMaclaurin_firstPeriodicBernoulli_secondOrder_oneBlock
    (phase phaseDerivative : ℝ → ℂ)
    (n : ℕ)
    (hphase :
      ∀ x ∈ Set.uIcc (n : ℝ) ((n : ℝ) + 1),
        HasDerivAt phase (phaseDerivative x) x)
    (hphaseDerivative :
      IntervalIntegrable phaseDerivative volume (n : ℝ) ((n : ℝ) + 1)) :
    (∫ x in (n : ℝ)..((n : ℝ) + 1),
        phase x * ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)) =
      -∫ x in (n : ℝ)..((n : ℝ) + 1),
        phaseDerivative x *
          eulerMaclaurinSecondOrderBernoulliBlockPrimitive n x := by
  have hprimitive :
      ∀ x ∈ Set.uIcc (n : ℝ) ((n : ℝ) + 1),
        HasDerivAt
          (eulerMaclaurinSecondOrderBernoulliBlockPrimitive n)
          ((x - (n : ℝ) - 1 / 2 : ℝ) : ℂ)
          x :=
    fun x _hx =>
      eulerMaclaurinSecondOrderBernoulliBlockPrimitive_hasDerivAt n x
  have haffineContinuous :
      Continuous (fun x : ℝ => ((x - (n : ℝ) - 1 / 2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((continuous_id.sub continuous_const).sub continuous_const)
  have haffineIntegrable :
      IntervalIntegrable
        (fun x : ℝ => ((x - (n : ℝ) - 1 / 2 : ℝ) : ℂ))
        volume
        (n : ℝ)
        ((n : ℝ) + 1) :=
    haffineContinuous.intervalIntegrable (n : ℝ) ((n : ℝ) + 1)
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hphase hprimitive hphaseDerivative haffineIntegrable
  have hleft :=
    eulerMaclaurinSecondOrderBernoulliBlockPrimitive_leftEndpoint n
  have hright :=
    eulerMaclaurinSecondOrderBernoulliBlockPrimitive_rightEndpoint n
  have hboundaryRight :
      phase ((n : ℝ) + 1) *
          eulerMaclaurinSecondOrderBernoulliBlockPrimitive n ((n : ℝ) + 1) = 0 :=
    Eq.trans
      (congrArg (fun value : ℂ => phase ((n : ℝ) + 1) * value) hright)
      (mul_zero (phase ((n : ℝ) + 1)))
  have hboundaryLeft :
      phase (n : ℝ) *
          eulerMaclaurinSecondOrderBernoulliBlockPrimitive n (n : ℝ) = 0 :=
    Eq.trans
      (congrArg (fun value : ℂ => phase (n : ℝ) * value) hleft)
      (mul_zero (phase (n : ℝ)))
  have haffineIdentity :
      (∫ x in (n : ℝ)..((n : ℝ) + 1),
          phase x * ((x - (n : ℝ) - 1 / 2 : ℝ) : ℂ)) =
        -∫ x in (n : ℝ)..((n : ℝ) + 1),
          phaseDerivative x *
            eulerMaclaurinSecondOrderBernoulliBlockPrimitive n x := by
    calc
      (∫ x in (n : ℝ)..((n : ℝ) + 1),
          phase x * ((x - (n : ℝ) - 1 / 2 : ℝ) : ℂ)) =
          phase ((n : ℝ) + 1) *
              eulerMaclaurinSecondOrderBernoulliBlockPrimitive n ((n : ℝ) + 1) -
            phase (n : ℝ) *
              eulerMaclaurinSecondOrderBernoulliBlockPrimitive n (n : ℝ) -
            ∫ x in (n : ℝ)..((n : ℝ) + 1),
              phaseDerivative x *
                eulerMaclaurinSecondOrderBernoulliBlockPrimitive n x := hibp
      _ = 0 - 0 -
            ∫ x in (n : ℝ)..((n : ℝ) + 1),
              phaseDerivative x *
                eulerMaclaurinSecondOrderBernoulliBlockPrimitive n x :=
        congrArg₂ Sub.sub
          (congrArg₂ Sub.sub hboundaryRight hboundaryLeft)
          rfl
      _ = -∫ x in (n : ℝ)..((n : ℝ) + 1),
            phaseDerivative x *
              eulerMaclaurinSecondOrderBernoulliBlockPrimitive n x := by
        exact Eq.trans
          (congrArg
            (fun value : ℂ => value -
              ∫ x in (n : ℝ)..((n : ℝ) + 1),
                phaseDerivative x *
                  eulerMaclaurinSecondOrderBernoulliBlockPrimitive n x)
            (sub_self 0))
          (zero_sub
            (∫ x in (n : ℝ)..((n : ℝ) + 1),
              phaseDerivative x *
                eulerMaclaurinSecondOrderBernoulliBlockPrimitive n x))
  have hperiodicAlmostEverywhere :
      (fun x : ℝ =>
        phase x * ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)) =ᵐ[
          volume.restrict (Set.Ioc (n : ℝ) ((n : ℝ) + 1))]
      (fun x : ℝ =>
        phase x * ((x - (n : ℝ) - 1 / 2 : ℝ) : ℂ)) := by
    have hendpointNull :
        volume ({(n : ℝ) + 1} : Set ℝ) = 0 :=
      measure_singleton ((n : ℝ) + 1)
    have hnotEndpoint :
        ∀ᵐ x : ℝ, x ∈ ({(n : ℝ) + 1} : Set ℝ)ᶜ :=
      compl_mem_ae_iff.mpr hendpointNull
    have hnotEndpointRestricted :
        ∀ᵐ x : ℝ ∂volume.restrict (Set.Ioc (n : ℝ) ((n : ℝ) + 1)),
          x ∈ ({(n : ℝ) + 1} : Set ℝ)ᶜ :=
      ae_restrict_of_ae hnotEndpoint
    have hrestrictedMembership :
        ∀ᵐ x : ℝ ∂volume.restrict (Set.Ioc (n : ℝ) ((n : ℝ) + 1)),
          x ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1) :=
      ae_restrict_mem measurableSet_Ioc
    filter_upwards [hnotEndpointRestricted, hrestrictedMembership] with x hxNotEndpoint hxBlock
    have hxNeEndpoint : x ≠ (n : ℝ) + 1 := by
      intro hxEndpoint
      exact hxNotEndpoint (hxEndpoint ▸ Set.mem_singleton ((n : ℝ) + 1))
    have hxInterior : x ∈ Set.Ioo (n : ℝ) ((n : ℝ) + 1) :=
      ⟨hxBlock.1, lt_of_le_of_ne hxBlock.2 hxNeEndpoint⟩
    exact congrArg (fun value : ℂ => phase x * value)
      (congrArg Complex.ofReal
        (have hright : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 :=
            Nat.cast_add_one n
          have hxOwner : x ∈ Set.Ioo (n : ℝ) (((n + 1 : ℕ) : ℝ)) :=
            ⟨hxInterior.1,
              Eq.subst
                (motive := fun bound : ℝ => x < bound)
                hright.symm
                hxInterior.2⟩
          eulerMaclaurinFirstPeriodicBernoulli_eq_sub_nat_sub_half_on_Ioo
            n hxOwner))
  have hsetIntegral :
      (∫ x in Set.Ioc (n : ℝ) ((n : ℝ) + 1),
          phase x * ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)) =
        ∫ x in Set.Ioc (n : ℝ) ((n : ℝ) + 1),
          phase x * ((x - (n : ℝ) - 1 / 2 : ℝ) : ℂ) :=
    integral_congr_ae hperiodicAlmostEverywhere
  have hinterval :
      (∫ x in (n : ℝ)..((n : ℝ) + 1),
          phase x * ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)) =
        ∫ x in (n : ℝ)..((n : ℝ) + 1),
          phase x * ((x - (n : ℝ) - 1 / 2 : ℝ) : ℂ) := by
    exact Eq.trans
      (intervalIntegral.integral_of_le (le_add_of_nonneg_right zero_le_one))
      (Eq.trans hsetIntegral
        (intervalIntegral.integral_of_le
          (le_add_of_nonneg_right zero_le_one)).symm)
  exact Eq.trans hinterval haffineIdentity

end
end LFunctions
end Boundary
