import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.FunctionalEquationTransport.Core.Owner

/-!
# Completed functional-equation analysis layer

This is the analysis section of functional-equation transport, containing
near-origin properties, Gamma continuity theorems, and removable-extension
theory for the completed functional-equation multiplier.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- `Gammaℝ` has no zero in the punctured closed unit ball. -/
theorem Gammaℝ_ne_zero_of_ne_zero_norm_le_one
    {z : ℂ}
    (hz_ne_zero : z ≠ 0)
    (hz_norm : ‖z‖ ≤ 1) :
    Complex.Gammaℝ z ≠ 0 :=
  fun hGamma_zero =>
  match Complex.Gammaℝ_eq_zero_iff.mp hGamma_zero with
  | ⟨n, hz_eq⟩ =>
    match n with
    | Nat.zero =>
      have hz_zero : z = 0 := by
        have hmul_zero : (2 : ℂ) * ((0 : ℕ) : ℂ) = 0 := by
          calc
            (2 : ℂ) * ((0 : ℕ) : ℂ) = (2 : ℂ) * 0 := by
              exact congrArg (fun x : ℂ => (2 : ℂ) * x) Nat.cast_zero
            _ = 0 := by
              exact mul_zero (2 : ℂ)
        calc
          z = -(2 * ((0 : ℕ) : ℂ)) := hz_eq
          _ = -0 := by
            exact congrArg Neg.neg hmul_zero
          _ = 0 := by
            exact neg_zero
      hz_ne_zero hz_zero
    | Nat.succ n =>
      have hprod_re :
          (2 * ((Nat.succ n : ℕ) : ℂ)).re =
            (2 : ℝ) * (Nat.succ n : ℝ) := by
        calc
          (2 * ((Nat.succ n : ℕ) : ℂ)).re =
              (2 : ℂ).re * ((Nat.succ n : ℕ) : ℂ).re -
                (2 : ℂ).im * ((Nat.succ n : ℕ) : ℂ).im := by
            exact Complex.mul_re (2 : ℂ) ((Nat.succ n : ℕ) : ℂ)
          _ = (2 : ℝ) * (Nat.succ n : ℝ) -
                (2 : ℂ).im * ((Nat.succ n : ℕ) : ℂ).im := by
            exact congrArg
              (fun x : ℝ =>
                x * ((Nat.succ n : ℕ) : ℂ).re -
                  (2 : ℂ).im * ((Nat.succ n : ℕ) : ℂ).im)
              (Complex.natCast_re 2)
          _ = (2 : ℝ) * (Nat.succ n : ℝ) -
                (2 : ℂ).im * 0 := by
            exact congrArg
              (fun x : ℝ =>
                (2 : ℝ) * (Nat.succ n : ℝ) - (2 : ℂ).im * x)
              (Complex.natCast_im (Nat.succ n))
          _ = (2 : ℝ) * (Nat.succ n : ℝ) - 0 * 0 := by
            exact congrArg
              (fun x : ℝ =>
                (2 : ℝ) * (Nat.succ n : ℝ) - x * 0)
              (Complex.natCast_im 2)
          _ = (2 : ℝ) * (Nat.succ n : ℝ) - 0 := by
            exact congrArg
              (fun x : ℝ => (2 : ℝ) * (Nat.succ n : ℝ) - x)
              (zero_mul 0)
          _ = (2 : ℝ) * (Nat.succ n : ℝ) := by
            exact sub_zero ((2 : ℝ) * (Nat.succ n : ℝ))
      have hz_re_eq :
          z.re = -((2 : ℝ) * (Nat.succ n : ℝ)) := by
        calc
          z.re = (-(2 * ((Nat.succ n : ℕ) : ℂ))).re := by
            exact congrArg Complex.re hz_eq
          _ = -((2 * ((Nat.succ n : ℕ) : ℂ)).re) := by
            exact Complex.neg_re (2 * ((Nat.succ n : ℕ) : ℂ))
          _ = -((2 : ℝ) * (Nat.succ n : ℝ)) := by
            exact congrArg Neg.neg hprod_re
      have hsucc_ge_one : (1 : ℝ) ≤ (Nat.succ n : ℝ) :=
        calc
          (1 : ℝ) = ((Nat.succ 0 : ℕ) : ℝ) := by
            exact Nat.cast_one.symm
          _ ≤ (Nat.succ n : ℝ) := by
            exact Nat.cast_le.mpr (Nat.succ_le_succ (Nat.zero_le n))
      have htwo_le_prod : (2 : ℝ) ≤ (2 : ℝ) * (Nat.succ n : ℝ) := by
        calc
          (2 : ℝ) = 2 * 1 := by
            exact (mul_one 2).symm
          _ ≤ 2 * (Nat.succ n : ℝ) := by
            exact mul_le_mul_of_nonneg_left hsucc_ge_one (le_of_lt zero_lt_two)
      have hprod_nonneg : 0 ≤ (2 : ℝ) * (Nat.succ n : ℝ) :=
        le_trans (le_of_lt zero_lt_two) htwo_le_prod
      have habs_eq :
          |z.re| = (2 : ℝ) * (Nat.succ n : ℝ) := by
        calc
          |z.re| = |-((2 : ℝ) * (Nat.succ n : ℝ))| := by
            exact congrArg abs hz_re_eq
          _ = |(2 : ℝ) * (Nat.succ n : ℝ)| := by
            exact abs_neg ((2 : ℝ) * (Nat.succ n : ℝ))
          _ = (2 : ℝ) * (Nat.succ n : ℝ) := by
            exact abs_of_nonneg hprod_nonneg
      have htwo_le_norm : (2 : ℝ) ≤ ‖z‖ := by
        exact le_trans
          (Eq.subst
            (motive := fun x : ℝ => (2 : ℝ) ≤ x)
            habs_eq.symm
            htwo_le_prod)
          (RCLike.abs_re_le_norm z)
      have htwo_le_one : (2 : ℝ) ≤ 1 :=
        le_trans htwo_le_norm hz_norm
      not_lt_of_ge htwo_le_one one_lt_two

/-- In the punctured unit ball, `z / 2` avoids the poles of `Complex.Gamma`. -/
theorem Gamma_half_ne_neg_nat_of_ne_zero_norm_le_one
    {z : ℂ}
    (hz_ne_zero : z ≠ 0)
    (hz_norm : ‖z‖ ≤ 1) :
    ∀ m : ℕ, z / 2 ≠ -m :=
  fun m hhalf =>
  match m with
  | Nat.zero =>
      have hz_div_zero : z / 2 = 0 := by
        calc
          z / 2 = -((0 : ℕ) : ℂ) := hhalf
          _ = -0 := by
            exact congrArg Neg.neg (Nat.cast_zero)
          _ = 0 := by
            exact neg_zero
      have hz_zero : z = 0 := by
        exact div_eq_zero_iff.mp hz_div_zero |>.resolve_right two_ne_zero
      hz_ne_zero hz_zero
  | Nat.succ n =>
      have hz_eq :
          z = -(2 * ((Nat.succ n : ℕ) : ℂ)) := by
        calc
          z = (z / 2) * 2 := by
            exact (div_mul_cancel₀ z two_ne_zero).symm
          _ = (-((Nat.succ n : ℕ) : ℂ)) * 2 := by
            exact congrArg (fun w : ℂ => w * 2) hhalf
          _ = -(2 * ((Nat.succ n : ℕ) : ℂ)) := by
            calc
              (-((Nat.succ n : ℕ) : ℂ)) * 2 =
                  -( ((Nat.succ n : ℕ) : ℂ) * 2) := by
                exact neg_mul (((Nat.succ n : ℕ) : ℂ)) 2
              _ = -(2 * ((Nat.succ n : ℕ) : ℂ)) := by
                exact congrArg Neg.neg (mul_comm (((Nat.succ n : ℕ) : ℂ)) 2)
      have hGamma_zero : Complex.Gammaℝ z = 0 :=
        Complex.Gammaℝ_eq_zero_iff.mpr ⟨Nat.succ n, hz_eq⟩
      Gammaℝ_ne_zero_of_ne_zero_norm_le_one hz_ne_zero hz_norm hGamma_zero

/-- `Gammaℝ` is continuous in the punctured unit ball. -/
theorem Gammaℝ_continuousAt_of_ne_zero_norm_le_one
    {z : ℂ}
    (hz_ne_zero : z ≠ 0)
    (hz_norm : ‖z‖ ≤ 1) :
    ContinuousAt Complex.Gammaℝ z := by
  have hGamma :
      ContinuousAt (fun w : ℂ => Complex.Gamma (w / 2)) z := by
    exact
      (Complex.differentiableAt_Gamma
        (z / 2)
        (Gamma_half_ne_neg_nat_of_ne_zero_norm_le_one hz_ne_zero hz_norm)).continuousAt.comp
        (x := z)
        (continuousAt_id.div_const (2 : ℂ))
  have hpow :
      ContinuousAt (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2)) z :=
    (continuousAt_id.neg.div_const 2).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  exact hpow.mul hGamma

/-- `Gammaℝ` is continuous at right-half-plane points. -/
theorem Gammaℝ_continuousAt_of_re_pos
    {z : ℂ}
    (hz_re : 0 < z.re) :
    ContinuousAt Complex.Gammaℝ z := by
  have hGamma :
      ContinuousAt (fun w : ℂ => Complex.Gamma (w / 2)) z := by
    have hpoles : ∀ m : ℕ, z / 2 ≠ -m :=
      fun m hhalf =>
      have hhalf_re_pos : 0 < (z / 2).re := by
        calc
          0 < z.re / 2 := div_pos hz_re two_pos
          _ = (z / 2).re := by
            exact (RCLike.div_re_ofReal (z := z) (r := (2 : ℝ))).symm
      have hhalf_re_nonpos : (z / 2).re ≤ 0 := by
        have hneg_re :
            (-((m : ℕ) : ℂ)).re ≤ 0 := by
          calc
            (-((m : ℕ) : ℂ)).re = -(((m : ℕ) : ℂ).re) := by
              exact Complex.neg_re (((m : ℕ) : ℂ))
            _ = -((m : ℕ) : ℝ) := by
              exact congrArg Neg.neg (Complex.natCast_re m)
            _ ≤ 0 := by
              exact neg_nonpos.mpr (Nat.cast_nonneg m)
        exact Eq.subst
          (motive := fun w : ℂ => w.re ≤ 0)
          hhalf.symm
          hneg_re
      not_le_of_gt hhalf_re_pos hhalf_re_nonpos
    exact (Complex.differentiableAt_Gamma (z / 2) hpoles).continuousAt.comp
      (x := z)
      (continuousAt_id.div_const (2 : ℂ))
  have hpow :
      ContinuousAt (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2)) z :=
    (continuousAt_id.neg.div_const 2).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  exact hpow.mul hGamma

/-- On the punctured closed left half-unit ball, the multiplier unfolds to the
raw Gamma-ratio branch. -/
theorem poleClearedRiemannZeta_completedFunctionalEquationMultiplier_eq_raw_on_nearOriginLeftSet_of_ne_zero
    {z : ℂ}
    (hz_mem :
      z ∈ poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet)
    (hz_ne_zero : z ≠ 0) :
    poleClearedRiemannZeta_completedFunctionalEquationMultiplier z =
      ((z - 1) / (((1 : ℂ) - z) - 1)) *
        (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z) := by
  have hGamma_ne :
      Complex.Gammaℝ z ≠ 0 :=
    Gammaℝ_ne_zero_of_ne_zero_norm_le_one hz_ne_zero hz_mem.2
  have hdef :
      poleClearedRiemannZeta_completedFunctionalEquationMultiplier z =
        if z = 0 then
          poleClearedRiemannZeta 0
        else if Complex.Gammaℝ z = 0 then
          poleClearedRiemannZeta z / poleClearedRiemannZeta ((1 : ℂ) - z)
        else
          ((z - 1) / (((1 : ℂ) - z) - 1)) *
            (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z) :=
    rfl
  exact Eq.trans hdef (Eq.trans (if_neg hz_ne_zero) (if_neg hGamma_ne))

/-- The raw Gamma-ratio branch is continuous at nonzero points of the closed
left half-unit ball. -/
theorem poleClearedRiemannZeta_completedFunctionalEquationMultiplier_raw_continuousAt_nearOriginLeftSet_of_ne_zero
    {z : ℂ}
    (hz_mem :
      z ∈ poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet)
    (hz_ne_zero : z ≠ 0) :
    ContinuousAt
      (fun w : ℂ =>
        ((w - 1) / (((1 : ℂ) - w) - 1)) *
          (Complex.Gammaℝ ((1 : ℂ) - w) / Complex.Gammaℝ w))
      z := by
  have hden_raw : (((1 : ℂ) - z) - 1) ≠ 0 :=
    fun hden_zero =>
    have hneg_zero : -z = 0 := by
      exact Eq.trans
        (show -z = ((1 : ℂ) - z) - 1 by
          exact (sub_sub_cancel_left (1 : ℂ) z).symm)
        hden_zero
    hz_ne_zero (neg_eq_zero.mp hneg_zero)
  have hGamma_z_ne :
      Complex.Gammaℝ z ≠ 0 :=
    Gammaℝ_ne_zero_of_ne_zero_norm_le_one hz_ne_zero hz_mem.2
  have hreflect_re_pos : 0 < ((1 : ℂ) - z).re := by
    have hsub_pos : 0 < 1 - z.re :=
      sub_pos.mpr (lt_of_le_of_lt hz_mem.1 zero_lt_one)
    have hcoord : ((1 : ℂ) - z).re = 1 - z.re := by
      calc
        ((1 : ℂ) - z).re = (1 : ℂ).re - z.re := by
          exact Complex.sub_re (1 : ℂ) z
        _ = 1 - z.re := by
          exact congrArg (fun x : ℝ => x - z.re) Complex.one_re
    exact Eq.subst
      (motive := fun x : ℝ => 0 < x)
      hcoord.symm
      hsub_pos
  have hfactor :
      ContinuousAt
        (fun w : ℂ => (w - 1) / (((1 : ℂ) - w) - 1)) z :=
    (continuousAt_id.sub continuousAt_const).div
      ((continuousAt_const.sub continuousAt_id).sub continuousAt_const)
      hden_raw
  have hreflect_map :
      ContinuousAt (fun w : ℂ => (1 : ℂ) - w) z :=
    continuousAt_const.sub continuousAt_id
  have hGamma_reflect :
      ContinuousAt (fun w : ℂ => Complex.Gammaℝ ((1 : ℂ) - w)) z :=
    (Gammaℝ_continuousAt_of_re_pos hreflect_re_pos).comp
      (x := z)
      hreflect_map
  have hGamma_current :
      ContinuousAt (fun w : ℂ => Complex.Gammaℝ w) z :=
    Gammaℝ_continuousAt_of_ne_zero_norm_le_one hz_ne_zero hz_mem.2
  have hratio :
      ContinuousAt
        (fun w : ℂ => Complex.Gammaℝ ((1 : ℂ) - w) / Complex.Gammaℝ w) z :=
    hGamma_reflect.div hGamma_current hGamma_z_ne
  exact hfactor.mul hratio

/-- Away from `0` inside the closed left half-unit ball, the completed
functional-equation multiplier is locally the raw Gamma-ratio expression and is
continuous there. -/
theorem poleClearedRiemannZeta_completedFunctionalEquationMultiplier_continuousWithinAt_nearOriginLeftSet_of_ne_zero
    {z : ℂ}
    (hz_mem :
      z ∈ poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet)
    (hz_ne_zero : z ≠ 0) :
    ContinuousWithinAt poleClearedRiemannZeta_completedFunctionalEquationMultiplier
      poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet z := by
  have hraw_cont :
      ContinuousAt
        (fun w : ℂ =>
          ((w - 1) / (((1 : ℂ) - w) - 1)) *
            (Complex.Gammaℝ ((1 : ℂ) - w) / Complex.Gammaℝ w))
        z :=
    poleClearedRiemannZeta_completedFunctionalEquationMultiplier_raw_continuousAt_nearOriginLeftSet_of_ne_zero
      hz_mem hz_ne_zero
  have hbranch :
      poleClearedRiemannZeta_completedFunctionalEquationMultiplier =ᶠ[
        𝓝[
          poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet] z]
        (fun w : ℂ =>
          ((w - 1) / (((1 : ℂ) - w) - 1)) *
            (Complex.Gammaℝ ((1 : ℂ) - w) / Complex.Gammaℝ w)) := by
    have hpunctured : ∀ᶠ w in 𝓝 z, w ≠ 0 :=
      eventually_ne_nhds hz_ne_zero
    have hwithin :
        ∀ᶠ w in
          𝓝[
            poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet] z,
          w ≠ 0 :=
      hpunctured.filter_mono nhdsWithin_le_nhds
    have hregional :
        ∀ᶠ w in
          𝓝[
            poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet] z,
          w ≠ 0 ∧
            w ∈
              poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet :=
      hwithin.and self_mem_nhdsWithin
    exact hregional.mono
      (fun w hw =>
        poleClearedRiemannZeta_completedFunctionalEquationMultiplier_eq_raw_on_nearOriginLeftSet_of_ne_zero
          hw.2 hw.1)
  exact
    hraw_cont.continuousWithinAt.congr_of_eventuallyEq
      hbranch
      (poleClearedRiemannZeta_completedFunctionalEquationMultiplier_eq_raw_on_nearOriginLeftSet_of_ne_zero
        hz_mem hz_ne_zero)

/-- The reflected pole-cleared denominator stays nonzero near the origin. -/
theorem poleClearedRiemannZeta_reflected_near_zero_nonzero_eventually :
    ∀ᶠ z in 𝓝 (0 : ℂ),
      poleClearedRiemannZeta ((1 : ℂ) - z) ≠ 0 := by
  have hcont :
      ContinuousAt (fun z : ℂ => poleClearedRiemannZeta ((1 : ℂ) - z)) 0 :=
    have hreflect_map :
        ContinuousAt (fun z : ℂ => (1 : ℂ) - z) 0 :=
      continuousAt_const.sub continuousAt_id
    have hbase :
        ContinuousAt poleClearedRiemannZeta ((1 : ℂ) - (0 : ℂ)) :=
      Eq.subst
        (motive := fun w : ℂ => ContinuousAt poleClearedRiemannZeta w)
        (sub_zero (1 : ℂ)).symm
        (poleClearedRiemannZeta_continuousAt 1)
    hbase.comp
      (x := (0 : ℂ))
      hreflect_map
  have hvalue :
      poleClearedRiemannZeta ((1 : ℂ) - (0 : ℂ)) ≠ 0 := by
    have hsub : (1 : ℂ) - (0 : ℂ) = 1 :=
      sub_zero (1 : ℂ)
    have hpole : poleClearedRiemannZeta ((1 : ℂ) - (0 : ℂ)) = 1 :=
      Eq.subst
        (motive := fun w : ℂ => poleClearedRiemannZeta w = 1)
        hsub.symm
        poleClearedRiemannZeta_one
    exact hpole.trans_ne one_ne_zero
  exact hcont.eventually_ne hvalue

/-- Near `0` on the left half-unit ball, the removable multiplier agrees with
the pole-cleared quotient. -/
theorem poleClearedRiemannZeta_completedFunctionalEquationMultiplier_eq_poleCleared_quotient_eventually_zero_nearOriginLeftSet :
    poleClearedRiemannZeta_completedFunctionalEquationMultiplier =ᶠ[
      𝓝[
        poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet] (0 : ℂ)]
      (fun z : ℂ =>
        poleClearedRiemannZeta z / poleClearedRiemannZeta ((1 : ℂ) - z)) := by
  have hden_nhds :
      ∀ᶠ z in 𝓝 (0 : ℂ),
        poleClearedRiemannZeta ((1 : ℂ) - z) ≠ 0 :=
    poleClearedRiemannZeta_reflected_near_zero_nonzero_eventually
  have hden_within :
      ∀ᶠ z in
        𝓝[
          poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet] (0 : ℂ),
        poleClearedRiemannZeta ((1 : ℂ) - z) ≠ 0 :=
    hden_nhds.filter_mono nhdsWithin_le_nhds
  have hregional :
      ∀ᶠ z in
        𝓝[
          poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet] (0 : ℂ),
        poleClearedRiemannZeta ((1 : ℂ) - z) ≠ 0 ∧
          z ∈
            poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet :=
    hden_within.and self_mem_nhdsWithin
  exact hregional.mono
    (fun z hz =>
      by
        have hden_ne :
            poleClearedRiemannZeta ((1 : ℂ) - z) ≠ 0 := hz.1
        have hz_mem :
            z ∈
              poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet := hz.2
        if hz_zero : z = 0 then
          have hM :
              poleClearedRiemannZeta_completedFunctionalEquationMultiplier z =
                poleClearedRiemannZeta 0 := by
            exact Eq.subst
              (motive := fun w : ℂ =>
                poleClearedRiemannZeta_completedFunctionalEquationMultiplier w =
                  poleClearedRiemannZeta 0)
              hz_zero.symm
              (by
                have hdef :
                    poleClearedRiemannZeta_completedFunctionalEquationMultiplier 0 =
                      if (0 : ℂ) = 0 then
                        poleClearedRiemannZeta 0
                      else if Complex.Gammaℝ (0 : ℂ) = 0 then
                        poleClearedRiemannZeta 0 /
                          poleClearedRiemannZeta ((1 : ℂ) - (0 : ℂ))
                      else
                        (((0 : ℂ) - 1) / (((1 : ℂ) - (0 : ℂ)) - 1)) *
                          (Complex.Gammaℝ ((1 : ℂ) - (0 : ℂ)) /
                            Complex.Gammaℝ (0 : ℂ)) :=
                  rfl
                exact Eq.trans hdef (if_pos rfl))
          have hsub : (1 : ℂ) - z = 1 := by
            exact Eq.subst
              (motive := fun w : ℂ => (1 : ℂ) - w = 1)
              hz_zero.symm
              (sub_zero (1 : ℂ))
          have hnum :
              poleClearedRiemannZeta z = poleClearedRiemannZeta 0 :=
            congrArg poleClearedRiemannZeta hz_zero
          have hden :
              poleClearedRiemannZeta ((1 : ℂ) - z) = 1 :=
            Eq.subst
              (motive := fun w : ℂ => poleClearedRiemannZeta w = 1)
              hsub.symm
              poleClearedRiemannZeta_one
          calc
            poleClearedRiemannZeta_completedFunctionalEquationMultiplier z =
                poleClearedRiemannZeta 0 := hM
            _ = poleClearedRiemannZeta 0 / 1 := by
              exact (div_one (poleClearedRiemannZeta 0)).symm
            _ = poleClearedRiemannZeta z /
                  poleClearedRiemannZeta ((1 : ℂ) - z) := by
              exact congrArg₂ HDiv.hDiv hnum.symm hden.symm
        else
          have hidentity :
              poleClearedRiemannZeta z =
                poleClearedRiemannZeta_completedFunctionalEquationMultiplier z *
                  poleClearedRiemannZeta ((1 : ℂ) - z) := by
            if hGamma_zero : Complex.Gammaℝ z = 0 then
              have hM :
                  poleClearedRiemannZeta_completedFunctionalEquationMultiplier z =
                    poleClearedRiemannZeta z /
                      poleClearedRiemannZeta ((1 : ℂ) - z) := by
                have hdef :
                    poleClearedRiemannZeta_completedFunctionalEquationMultiplier z =
                      if z = 0 then
                        poleClearedRiemannZeta 0
                      else if Complex.Gammaℝ z = 0 then
                        poleClearedRiemannZeta z /
                          poleClearedRiemannZeta ((1 : ℂ) - z)
                      else
                        ((z - 1) / (((1 : ℂ) - z) - 1)) *
                          (Complex.Gammaℝ ((1 : ℂ) - z) /
                            Complex.Gammaℝ z) :=
                  rfl
                exact Eq.trans hdef (Eq.trans (if_neg hz_zero) (if_pos hGamma_zero))
              exact
                calc
                  poleClearedRiemannZeta z =
                      (poleClearedRiemannZeta z /
                        poleClearedRiemannZeta ((1 : ℂ) - z)) *
                        poleClearedRiemannZeta ((1 : ℂ) - z) := by
                    exact (div_mul_cancel₀
                      (poleClearedRiemannZeta z)
                      hden_ne).symm
                  _ =
                      poleClearedRiemannZeta_completedFunctionalEquationMultiplier z *
                        poleClearedRiemannZeta ((1 : ℂ) - z) := by
                    exact congrArg
                      (fun w : ℂ => w * poleClearedRiemannZeta ((1 : ℂ) - z))
                      hM.symm
            else
              have hM :
                  poleClearedRiemannZeta_completedFunctionalEquationMultiplier z =
                    ((z - 1) / (((1 : ℂ) - z) - 1)) *
                      (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z) := by
                have hdef :
                    poleClearedRiemannZeta_completedFunctionalEquationMultiplier z =
                      if z = 0 then
                        poleClearedRiemannZeta 0
                      else if Complex.Gammaℝ z = 0 then
                        poleClearedRiemannZeta z /
                          poleClearedRiemannZeta ((1 : ℂ) - z)
                      else
                        ((z - 1) / (((1 : ℂ) - z) - 1)) *
                          (Complex.Gammaℝ ((1 : ℂ) - z) /
                            Complex.Gammaℝ z) :=
                  rfl
                exact Eq.trans hdef (Eq.trans (if_neg hz_zero) (if_neg hGamma_zero))
              have hquotient :
                  riemannZeta z =
                    riemannZeta ((1 : ℂ) - z) *
                      Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z :=
                riemannZeta_completedFunctionalEquation_quotient_of_gamma_ne_zero
                  hz_mem.1 hz_zero hGamma_zero
              have hraw :
                  poleClearedRiemannZeta z =
                    (((z - 1) / (((1 : ℂ) - z) - 1)) *
                        (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) *
                      poleClearedRiemannZeta ((1 : ℂ) - z) :=
                poleClearedRiemannZeta_completedFunctionalEquationMultiplier_raw_identity_of_zeta_quotient
                  hz_mem.1 hz_zero hquotient
              exact
                calc
                  poleClearedRiemannZeta z =
                      (((z - 1) / (((1 : ℂ) - z) - 1)) *
                          (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) *
                        poleClearedRiemannZeta ((1 : ℂ) - z) := hraw
                  _ =
                      poleClearedRiemannZeta_completedFunctionalEquationMultiplier z *
                        poleClearedRiemannZeta ((1 : ℂ) - z) := by
                    exact congrArg
                      (fun w : ℂ => w * poleClearedRiemannZeta ((1 : ℂ) - z))
                      hM.symm
          calc
            poleClearedRiemannZeta_completedFunctionalEquationMultiplier z =
                (poleClearedRiemannZeta_completedFunctionalEquationMultiplier z *
                  poleClearedRiemannZeta ((1 : ℂ) - z)) /
                  poleClearedRiemannZeta ((1 : ℂ) - z) := by
              exact (mul_div_cancel_right₀
                (poleClearedRiemannZeta_completedFunctionalEquationMultiplier z)
                hden_ne).symm
            _ = poleClearedRiemannZeta z /
                  poleClearedRiemannZeta ((1 : ℂ) - z) := by
              exact congrArg
                (fun w : ℂ =>
                  w / poleClearedRiemannZeta ((1 : ℂ) - z))
                hidentity.symm)

/-- The pole-cleared reflected quotient is continuous at the origin. -/
theorem poleClearedRiemannZeta_reflected_quotient_continuousAt_zero :
    ContinuousAt
      (fun z : ℂ =>
        poleClearedRiemannZeta z / poleClearedRiemannZeta ((1 : ℂ) - z))
      (0 : ℂ) := by
  have hnum : ContinuousAt poleClearedRiemannZeta (0 : ℂ) :=
    poleClearedRiemannZeta_continuousAt 0
  have hden :
      ContinuousAt (fun z : ℂ => poleClearedRiemannZeta ((1 : ℂ) - z)) 0 :=
    have hreflect_map :
        ContinuousAt (fun z : ℂ => (1 : ℂ) - z) 0 :=
      continuousAt_const.sub continuousAt_id
    have hbase :
        ContinuousAt poleClearedRiemannZeta ((1 : ℂ) - (0 : ℂ)) :=
      Eq.subst
        (motive := fun w : ℂ => ContinuousAt poleClearedRiemannZeta w)
        (sub_zero (1 : ℂ)).symm
        (poleClearedRiemannZeta_continuousAt 1)
    hbase.comp
      (x := (0 : ℂ))
      hreflect_map
  have hden_ne :
      poleClearedRiemannZeta ((1 : ℂ) - (0 : ℂ)) ≠ 0 := by
    have hsub : (1 : ℂ) - (0 : ℂ) = 1 :=
      sub_zero (1 : ℂ)
    have hpole : poleClearedRiemannZeta ((1 : ℂ) - (0 : ℂ)) = 1 :=
      Eq.subst
        (motive := fun w : ℂ => poleClearedRiemannZeta w = 1)
        hsub.symm
        poleClearedRiemannZeta_one
    exact hpole.trans_ne one_ne_zero
  exact hnum.div hden hden_ne

/-- Removable continuity of the completed-functional-equation multiplier at the
origin on the closed left half-unit ball. -/
theorem poleClearedRiemannZeta_completedFunctionalEquationMultiplier_continuousWithinAt_zero_nearOriginLeftSet :
    ContinuousWithinAt poleClearedRiemannZeta_completedFunctionalEquationMultiplier
      poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet 0 := by
  have hquotient :
      ContinuousWithinAt
        (fun z : ℂ =>
          poleClearedRiemannZeta z / poleClearedRiemannZeta ((1 : ℂ) - z))
        poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet
        (0 : ℂ) :=
    poleClearedRiemannZeta_reflected_quotient_continuousAt_zero.continuousWithinAt
  have hagree :
      poleClearedRiemannZeta_completedFunctionalEquationMultiplier =ᶠ[
        𝓝[
          poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet] (0 : ℂ)]
        (fun z : ℂ =>
          poleClearedRiemannZeta z / poleClearedRiemannZeta ((1 : ℂ) - z)) :=
    poleClearedRiemannZeta_completedFunctionalEquationMultiplier_eq_poleCleared_quotient_eventually_zero_nearOriginLeftSet
  have hvalue :
      poleClearedRiemannZeta_completedFunctionalEquationMultiplier 0 =
        poleClearedRiemannZeta 0 / poleClearedRiemannZeta ((1 : ℂ) - (0 : ℂ)) := by
    have hM :
          poleClearedRiemannZeta_completedFunctionalEquationMultiplier 0 =
            poleClearedRiemannZeta 0 := by
      have hdef :
          poleClearedRiemannZeta_completedFunctionalEquationMultiplier 0 =
            if (0 : ℂ) = 0 then
              poleClearedRiemannZeta 0
            else if Complex.Gammaℝ (0 : ℂ) = 0 then
              poleClearedRiemannZeta 0 /
                poleClearedRiemannZeta ((1 : ℂ) - (0 : ℂ))
            else
              (((0 : ℂ) - 1) / (((1 : ℂ) - (0 : ℂ)) - 1)) *
                (Complex.Gammaℝ ((1 : ℂ) - (0 : ℂ)) /
                  Complex.Gammaℝ (0 : ℂ)) :=
        rfl
      exact Eq.trans hdef (if_pos rfl)
    have hden :
        poleClearedRiemannZeta ((1 : ℂ) - (0 : ℂ)) = 1 := by
      have hsub : (1 : ℂ) - (0 : ℂ) = 1 :=
        sub_zero (1 : ℂ)
      exact Eq.subst
        (motive := fun w : ℂ => poleClearedRiemannZeta w = 1)
        hsub.symm
        poleClearedRiemannZeta_one
    calc
      poleClearedRiemannZeta_completedFunctionalEquationMultiplier 0 =
          poleClearedRiemannZeta 0 := hM
      _ = poleClearedRiemannZeta 0 / 1 := by
        exact (div_one (poleClearedRiemannZeta 0)).symm
      _ = poleClearedRiemannZeta 0 /
            poleClearedRiemannZeta ((1 : ℂ) - (0 : ℂ)) := by
        exact congrArg
          (fun w : ℂ => poleClearedRiemannZeta 0 / w)
          hden.symm
  exact hquotient.congr_of_eventuallyEq hagree hvalue

/-- Trivial-zero cancellation for the pole-cleared zeta factor at nonzero
`Gammaℝ` zero faces in the left half-plane.

This is the standard analytic input: `Gammaℝ z = 0` means `z` is a
nonpositive even integer; after excluding `0`, these are exactly the negative
even integers, where `ζ` has its trivial zeros.  The pole-cleared factor has no
pole at such points, so it vanishes. -/
theorem poleClearedRiemannZeta_trivialZero_of_gammaZero_leftHalfPlane
    {z : ℂ}
    (hz_re : z.re ≤ 0)
    (hz_ne_zero : z ≠ 0)
    (hGamma_zero : Complex.Gammaℝ z = 0) :
    poleClearedRiemannZeta z = 0 := by
  match Complex.Gammaℝ_eq_zero_iff.mp hGamma_zero with
  | ⟨n, hz_eq⟩ =>
    match n with
    | Nat.zero =>
      have hz_zero : z = 0 := by
        have hmul_zero : (2 : ℂ) * ((0 : ℕ) : ℂ) = 0 := by
          calc
            (2 : ℂ) * ((0 : ℕ) : ℂ) = (2 : ℂ) * 0 := by
              exact congrArg (fun x : ℂ => (2 : ℂ) * x) Nat.cast_zero
            _ = 0 := by
              exact mul_zero (2 : ℂ)
        calc
          z = -(2 * ((0 : ℕ) : ℂ)) := hz_eq
          _ = -0 := by
            exact congrArg Neg.neg hmul_zero
          _ = 0 := by
            exact neg_zero
      exact False.elim (hz_ne_zero hz_zero)
    | Nat.succ n =>
      have hz_ne_one : z ≠ 1 :=
        fun hz_one =>
        have hz_re_one : z.re = 1 := by
          calc
            z.re = (1 : ℂ).re := by
              exact congrArg Complex.re hz_one
            _ = 1 := by
              exact Complex.one_re
        have hone_le_zero : (1 : ℝ) ≤ 0 :=
          have hone_le_zre : (1 : ℝ) ≤ z.re :=
            le_of_eq hz_re_one.symm
          le_trans hone_le_zre hz_re
        not_lt_of_ge hone_le_zero zero_lt_one
      have hpole :
          poleClearedRiemannZeta z = (z - 1) * riemannZeta z :=
        poleClearedRiemannZeta_eq_of_ne_one hz_ne_one
      have hzeta_zero_at :
          riemannZeta (-(2 * ((Nat.succ n : ℕ) : ℂ))) = 0 := by
        have harg :
            -2 * ((n : ℂ) + 1) =
              -(2 * ((Nat.succ n : ℕ) : ℂ)) := by
          calc
            -2 * ((n : ℂ) + 1) =
                -(2 * ((n : ℂ) + 1)) := by
              exact neg_mul (2 : ℂ) ((n : ℂ) + 1)
            _ = -(2 * ((Nat.succ n : ℕ) : ℂ)) := by
              exact congrArg Neg.neg
                (congrArg (fun x : ℂ => (2 : ℂ) * x) (Nat.cast_succ n).symm)
        exact Eq.subst
          (motive := fun w : ℂ => riemannZeta w = 0)
          harg
          (riemannZeta_neg_two_mul_nat_add_one n)
      have hzeta_zero : riemannZeta z = 0 := by
        exact Eq.subst
          (motive := fun w : ℂ => riemannZeta w = 0)
          hz_eq.symm
          hzeta_zero_at
      calc
        poleClearedRiemannZeta z = (z - 1) * riemannZeta z := hpole
        _ = (z - 1) * 0 := by
          exact congrArg (fun w : ℂ => (z - 1) * w) hzeta_zero
        _ = 0 := by
          exact mul_zero (z - 1)

end

end LFunctions
end Boundary
