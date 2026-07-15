import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.SharpPhaseIntegralParts.ContinuousBernoulliFourier.BlockIntegralAssembly

/-!
# Assembly of the constant Bernoulli-moment terms
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

private theorem realSixMulTwoEqTwelve : (6 : ℝ) * 2 = 12 := by
  have hnat : ((6 * 2 : ℕ) : ℝ) = ((12 : ℕ) : ℝ) :=
    congrArg (fun n : ℕ => (n : ℝ))
      (show (6 * 2 : ℕ) = 12 from rfl)
  have hleft : ((6 * 2 : ℕ) : ℝ) = (6 : ℝ) * 2 :=
    Nat.cast_mul 6 2
  have hright : ((12 : ℕ) : ℝ) = (12 : ℝ) :=
    rfl
  exact Eq.trans hleft.symm (Eq.trans hnat hright)

/-- The derivative of the zero-mode oscillator in the global coordinate based
at the canonical left endpoint. -/
noncomputable def boundaryLineOnePointRealParam_globalZeroModeDerivative
    (t : ℝ)
    (C : ℕ)
    (x : ℝ) : ℂ :=
  boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t C x *
    Complex.realPhaseOscillation
      (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 C) x

/-- A local constant-moment term is the corresponding interval of the global
zero-mode derivative. -/
theorem intervalIntegral_boundaryLineOnePointRealParam_localConstant_eq_globalBlock
    (t : ℝ)
    (C k : ℕ) :
    (∫ u in (0 : ℝ)..1,
        (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude
            t (C + k) u *
          Complex.realPhaseOscillation
            (boundaryLineOnePointRealParam_unitBlockCombinedPhase
              t 0 (C + k)) u) *
          (1 / 12 : ℂ)) =
      ∫ x in (k : ℝ)..((k + 1 : ℕ) : ℝ),
        boundaryLineOnePointRealParam_globalZeroModeDerivative t C x *
          (1 / 12 : ℂ) := by
  let F : ℝ → ℂ := fun x =>
    boundaryLineOnePointRealParam_globalZeroModeDerivative t C x *
      (1 / 12 : ℂ)
  have hpoint :
      ∀ u : ℝ,
        (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude
              t (C + k) u *
            Complex.realPhaseOscillation
              (boundaryLineOnePointRealParam_unitBlockCombinedPhase
                t 0 (C + k)) u) *
            (1 / 12 : ℂ) = F ((k : ℝ) + u) := by
    intro u
    unfold F
    unfold boundaryLineOnePointRealParam_globalZeroModeDerivative
    exact congrArg (fun z : ℂ => z * (1 / 12 : ℂ))
      (congrArg₂ Mul.mul
        (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude_natAdd
          t C k u)
        (boundaryLineOnePointRealParam_zeroModeOscillation_natAdd t C k u))
  have hlocal :
      (∫ u in (0 : ℝ)..1,
          (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude
              t (C + k) u *
            Complex.realPhaseOscillation
              (boundaryLineOnePointRealParam_unitBlockCombinedPhase
                t 0 (C + k)) u) *
            (1 / 12 : ℂ)) =
        ∫ u in (0 : ℝ)..1, F ((k : ℝ) + u) :=
    intervalIntegral.integral_congr (fun u _hu => hpoint u)
  have htranslate :
      (∫ u in (0 : ℝ)..1, F ((k : ℝ) + u)) =
        ∫ x in ((k : ℝ) + 0)..((k : ℝ) + 1), F x :=
    intervalIntegral.integral_comp_add_left F (k : ℝ)
  have hleft : (k : ℝ) + 0 = (k : ℝ) :=
    add_zero (k : ℝ)
  have hright : (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) :=
    Eq.trans
      (congrArg (fun r : ℝ => (k : ℝ) + r)
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ)))
      (Nat.cast_add k 1).symm
  exact Eq.trans hlocal
    (Eq.trans htranslate
      (congrArg₂ (fun a b : ℝ => ∫ x in a..b, F x) hleft hright))

/-- The global zero-mode derivative is integrable on every finite nonnegative
interval after the cutoff. -/
theorem intervalIntegrable_boundaryLineOnePointRealParam_globalZeroModeDerivative
    (t : ℝ)
    {C : ℕ}
    (hC : ⌊2 + ‖t‖⌋₊ ≤ C)
    {L : ℝ}
    (hL : 0 ≤ L) :
    IntervalIntegrable
      (boundaryLineOnePointRealParam_globalZeroModeDerivative t C)
      volume 0 L := by
  have hcontinuous :
      ContinuousOn
        (boundaryLineOnePointRealParam_globalZeroModeDerivative t C)
        (Set.uIcc (0 : ℝ) L) := by
    intro u hu
    have huIcc : u ∈ Set.Icc (0 : ℝ) L :=
      Eq.subst (motive := fun s : Set ℝ => u ∈ s) (Set.uIcc_of_le hL) hu
    have hcoordinatePositive : 0 < (C : ℝ) + u :=
      boundaryLineOnePointRealParam_unitBlock_coordinate_pos t hC huIcc.1
    have hamplitude :
        ContinuousAt
          (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t C)
          u :=
      (hasDerivAt_boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude
        t C hcoordinatePositive).continuousAt
    have hoscillation :
        ContinuousAt
          (Complex.realPhaseOscillation
            (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 C))
          u :=
      (hasDerivAt_boundaryLineOnePointRealParam_zeroModeOscillation
        t hC huIcc.1).continuousAt
    exact (hamplitude.mul hoscillation).continuousWithinAt
  exact hcontinuous.intervalIntegrable

/-- FTC evaluation of the assembled constant-moment derivative integral. -/
theorem intervalIntegral_boundaryLineOnePointRealParam_globalZeroModeDerivative_eq_endpoints
    (t : ℝ)
    {C D : ℕ}
    (hC : ⌊2 + ‖t‖⌋₊ ≤ C) :
    (∫ x in (0 : ℝ)..(D : ℝ),
        boundaryLineOnePointRealParam_globalZeroModeDerivative t C x) =
      Complex.realPhaseOscillation
          (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 C) (D : ℝ) -
        Complex.realPhaseOscillation
          (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 C) 0 := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx =>
      hasDerivAt_boundaryLineOnePointRealParam_zeroModeOscillation
        t hC
        ((Eq.subst (motive := fun s : Set ℝ => x ∈ s)
          (Set.uIcc_of_le (Nat.cast_nonneg D)) hx).1))
    (intervalIntegrable_boundaryLineOnePointRealParam_globalZeroModeDerivative
      t hC (Nat.cast_nonneg D))

/-- The assembled constant Bernoulli moment has norm at most `1/6`. -/
theorem norm_intervalIntegral_boundaryLineOnePointRealParam_globalZeroModeDerivative_mul_oneTwelfth_le_oneSixth
    (t : ℝ)
    {C D : ℕ}
    (hC : ⌊2 + ‖t‖⌋₊ ≤ C) :
    ‖∫ x in (0 : ℝ)..(D : ℝ),
        boundaryLineOnePointRealParam_globalZeroModeDerivative t C x *
          (1 / 12 : ℂ)‖ ≤ (1 : ℝ) / 6 := by
  let E : ℝ → ℂ :=
    Complex.realPhaseOscillation
      (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 C)
  have hfactor :
      (∫ x in (0 : ℝ)..(D : ℝ),
          boundaryLineOnePointRealParam_globalZeroModeDerivative t C x *
            (1 / 12 : ℂ)) =
        (∫ x in (0 : ℝ)..(D : ℝ),
          boundaryLineOnePointRealParam_globalZeroModeDerivative t C x) *
            (1 / 12 : ℂ) :=
    intervalIntegral.integral_mul_const (1 / 12 : ℂ)
      (boundaryLineOnePointRealParam_globalZeroModeDerivative t C)
  have hendpoints :=
    intervalIntegral_boundaryLineOnePointRealParam_globalZeroModeDerivative_eq_endpoints
      t hC (D := D)
  have hdiff : ‖E (D : ℝ) - E 0‖ ≤ 2 := by
    exact le_trans
      (norm_sub_le (E (D : ℝ)) (E 0))
      (le_of_eq
        (Eq.trans
          (congrArg₂ Add.add
            (Complex.norm_realPhaseOscillation _ _)
            (Complex.norm_realPhaseOscillation _ _))
          (one_add_one_eq_two)))
  have hconstantNorm : ‖(1 / 12 : ℂ)‖ = (1 : ℝ) / 12 := by
    exact Eq.trans
      (norm_div (1 : ℂ) (12 : ℂ))
      (congrArg₂ Div.div norm_one (Complex.norm_ofNat 12))
  have hnonnegative : 0 ≤ ‖(1 / 12 : ℂ)‖ :=
    norm_nonneg _
  have hproduct :
      ‖E (D : ℝ) - E 0‖ * ‖(1 / 12 : ℂ)‖ ≤
        2 * ‖(1 / 12 : ℂ)‖ :=
    mul_le_mul_of_nonneg_right hdiff hnonnegative
  have htwoTwelfths : 2 * ((1 : ℝ) / 12) = (1 : ℝ) / 6 := by
    have hsix_ne : (6 : ℝ) ≠ 0 :=
      OfNat.ofNat_ne_zero 6
    have htwelve_ne : (12 : ℝ) ≠ 0 :=
      OfNat.ofNat_ne_zero 12
    have htwelve : (12 : ℝ) = 6 * 2 :=
      realSixMulTwoEqTwelve.symm
    have hdivision : (2 : ℝ) / 12 = (1 : ℝ) / 6 := by
      exact (div_eq_iff htwelve_ne).mpr
        (Eq.trans
          (congrArg (fun r : ℝ => ((1 : ℝ) / 6) * r) htwelve)
          (Eq.trans
            (mul_assoc ((1 : ℝ) / 6) 6 2).symm
            (Eq.trans
              (congrArg (fun r : ℝ => r * 2)
                (div_mul_cancel₀ (1 : ℝ) hsix_ne))
              (one_mul 2)))).symm
    exact Eq.trans
      (two_mul ((1 : ℝ) / 12))
      (Eq.trans
        (add_div 1 1 12).symm
        (Eq.trans
          (congrArg (fun r : ℝ => r / 12)
            (one_add_one_eq_two : (1 : ℝ) + 1 = 2))
          hdivision))
  exact Eq.subst
    (motive := fun z : ℂ => ‖z‖ ≤ (1 : ℝ) / 6)
    (Eq.trans hfactor (congrArg (fun z : ℂ => z * (1 / 12 : ℂ)) hendpoints)).symm
    (le_trans
      (le_of_eq (norm_mul (E (D : ℝ) - E 0) (1 / 12 : ℂ)))
      (le_trans hproduct
        (le_of_eq
          (Eq.trans
            (congrArg (fun r : ℝ => 2 * r) hconstantNorm)
            htwoTwelfths))))

/-- The finite sum of local constant-moment terms is the single assembled
global constant-moment integral. -/
theorem sum_intervalIntegral_boundaryLineOnePointRealParam_localConstant_eq_global
    (t : ℝ)
    {C : ℕ}
    (hC : ⌊2 + ‖t‖⌋₊ ≤ C)
    (D : ℕ) :
    (∑ k ∈ Finset.range D,
      ∫ u in (0 : ℝ)..1,
        (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude
            t (C + k) u *
          Complex.realPhaseOscillation
            (boundaryLineOnePointRealParam_unitBlockCombinedPhase
              t 0 (C + k)) u) *
          (1 / 12 : ℂ)) =
      ∫ x in (0 : ℝ)..(D : ℝ),
        boundaryLineOnePointRealParam_globalZeroModeDerivative t C x *
          (1 / 12 : ℂ) := by
  have hlocal :
      (∑ k ∈ Finset.range D,
        ∫ u in (0 : ℝ)..1,
          (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude
              t (C + k) u *
            Complex.realPhaseOscillation
              (boundaryLineOnePointRealParam_unitBlockCombinedPhase
                t 0 (C + k)) u) *
            (1 / 12 : ℂ)) =
        ∑ k ∈ Finset.range D,
          ∫ x in (k : ℝ)..((k + 1 : ℕ) : ℝ),
            boundaryLineOnePointRealParam_globalZeroModeDerivative t C x *
              (1 / 12 : ℂ) :=
    Finset.sum_congr rfl
    (fun k (_hk : k ∈ Finset.range D) =>
      intervalIntegral_boundaryLineOnePointRealParam_localConstant_eq_globalBlock
        t C k)
  have hintegrable :
      ∀ k < D,
        IntervalIntegrable
          (fun x : ℝ =>
            boundaryLineOnePointRealParam_globalZeroModeDerivative t C x *
              (1 / 12 : ℂ))
          volume (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
    intro k _hk
    have hglobal :=
      intervalIntegrable_boundaryLineOnePointRealParam_globalZeroModeDerivative
        t hC (show (0 : ℝ) ≤ (D : ℝ) from Nat.cast_nonneg D)
    have hDnonnegative : (0 : ℝ) ≤ (D : ℝ) :=
      Nat.cast_nonneg D
    have hk_mem :
        (k : ℝ) ∈ Set.uIcc (0 : ℝ) (D : ℝ) := by
      exact Eq.subst
        (motive := fun s : Set ℝ => (k : ℝ) ∈ s)
        (Set.uIcc_of_le hDnonnegative).symm
        (And.intro
          (Nat.cast_nonneg k)
          (Nat.cast_le.mpr (Nat.le_of_lt _hk)))
    have hsucc_mem :
        ((k + 1 : ℕ) : ℝ) ∈ Set.uIcc (0 : ℝ) (D : ℝ) := by
      exact Eq.subst
        (motive := fun s : Set ℝ => ((k + 1 : ℕ) : ℝ) ∈ s)
        (Set.uIcc_of_le hDnonnegative).symm
        (And.intro
          (Nat.cast_nonneg (k + 1))
          (Nat.cast_le.mpr (Nat.succ_le_of_lt _hk)))
    exact (hglobal.mono_set
      (Set.uIcc_subset_uIcc hk_mem hsucc_mem)).mul_const
          (1 / 12 : ℂ)
  have hadjacent :
      (∑ k ∈ Finset.range D,
          ∫ x in (k : ℝ)..((k + 1 : ℕ) : ℝ),
            boundaryLineOnePointRealParam_globalZeroModeDerivative t C x *
              (1 / 12 : ℂ)) =
        ∫ x in ((0 : ℕ) : ℝ)..((D : ℕ) : ℝ),
          boundaryLineOnePointRealParam_globalZeroModeDerivative t C x *
            (1 / 12 : ℂ) :=
    intervalIntegral.sum_integral_adjacent_intervals
      (f := fun x : ℝ =>
        boundaryLineOnePointRealParam_globalZeroModeDerivative t C x *
          (1 / 12 : ℂ))
      (a := fun k : ℕ => (k : ℝ))
      (n := D)
      hintegrable
  have hzero : ((0 : ℕ) : ℝ) = 0 :=
    Nat.cast_zero
  have hfinal :
      (∫ x in ((0 : ℕ) : ℝ)..((D : ℕ) : ℝ),
          boundaryLineOnePointRealParam_globalZeroModeDerivative t C x *
            (1 / 12 : ℂ)) =
        ∫ x in (0 : ℝ)..(D : ℝ),
          boundaryLineOnePointRealParam_globalZeroModeDerivative t C x *
            (1 / 12 : ℂ) :=
    congrArg
      (fun left : ℝ =>
        ∫ x in left..(D : ℝ),
          boundaryLineOnePointRealParam_globalZeroModeDerivative t C x *
            (1 / 12 : ℂ))
      hzero
  exact Eq.trans hlocal (Eq.trans hadjacent hfinal)

end
end LFunctions
end Boundary
