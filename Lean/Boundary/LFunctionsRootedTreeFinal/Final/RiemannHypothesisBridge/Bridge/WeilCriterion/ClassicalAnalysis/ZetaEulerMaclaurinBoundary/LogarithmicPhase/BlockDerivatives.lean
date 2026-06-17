import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.Derivatives

/-!
# Integer-block derivative bounds for logarithmic phase estimates

This file owns the monotonicity and lower-bound consequences of the continuous
derivative formulas on positive integer blocks.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The logarithmic-phase derivative magnitude `|t| / x` is decreasing on the
positive real axis. -/
theorem Complex.logarithmicPhase_derivativeMagnitude_antitoneOn_positive
    (t : ℝ) :
    AntitoneOn (fun x : ℝ => ‖t‖ / x) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hreciprocal : (1 : ℝ) / y ≤ (1 : ℝ) / x :=
    one_div_le_one_div_of_le hx hxy
  have hnorm_nonneg : 0 ≤ ‖t‖ :=
    norm_nonneg t
  have hleft : ‖t‖ / y = ‖t‖ * ((1 : ℝ) / y) :=
    div_eq_mul_one_div ‖t‖ y
  have hright : ‖t‖ / x = ‖t‖ * ((1 : ℝ) / x) :=
    div_eq_mul_one_div ‖t‖ x
  exact Eq.subst
    (motive := fun target : ℝ => ‖t‖ / y ≤ target)
    hright.symm
    (Eq.subst
      (motive := fun source : ℝ => source ≤ ‖t‖ * ((1 : ℝ) / x))
      hleft.symm
      (mul_le_mul_of_nonneg_left hreciprocal hnorm_nonneg))

/-- Lower derivative-magnitude bound on a positive block. -/
theorem Complex.logarithmicPhase_derivativeMagnitude_block_lower_bound
    (t : ℝ)
    {a b x : ℝ}
    (ha : 0 < a)
    (hxb : x ∈ Set.Icc a b) :
    ‖t‖ / b ≤ ‖t‖ / x := by
  have hx_pos : 0 < x :=
    lt_of_lt_of_le ha hxb.1
  exact
    Complex.logarithmicPhase_derivativeMagnitude_antitoneOn_positive t
      hx_pos
      (lt_of_lt_of_le hx_pos hxb.2)
      hxb.2

/-- The derivative of the logarithmic phase has the expected lower bound on a
positive integer block. -/
theorem Complex.logarithmicPhase_deriv_norm_block_lower_bound
    (t : ℝ)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (_hab : a ≤ b)
    {x : ℝ}
    (hx : x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) :
    ((‖t‖ : ℝ) / ((b + 1 : ℕ) : ℝ)) ≤
      ‖deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t) x‖ := by
  have ha_pos_nat : 0 < a :=
    Nat.lt_of_succ_le ha
  have hb_pos_nat : 0 < b + 1 :=
    Nat.succ_pos b
  have ha_pos_real : 0 < (a : ℝ) :=
    Nat.cast_pos.mpr ha_pos_nat
  have hx_pos : 0 < x :=
    lt_of_lt_of_le ha_pos_real hx.1
  have hderiv_norm :
      ‖deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t) x‖ =
        ‖t‖ / x :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction_deriv_norm_eq
      t hx_pos
  have hblock :
      ‖t‖ / ((b + 1 : ℕ) : ℝ) ≤ ‖t‖ / x :=
    Complex.logarithmicPhase_derivativeMagnitude_block_lower_bound
      t
      ha_pos_real
      hx
  exact Eq.subst
    (motive := fun target : ℝ => ‖t‖ / ((b + 1 : ℕ) : ℝ) ≤ target)
    hderiv_norm.symm
    hblock

/-- The logarithmic-phase derivative magnitude is monotone on every positive
integer block. -/
theorem Complex.logarithmicPhase_deriv_norm_antitoneOn_integer_block
    (t : ℝ)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (_hab : a ≤ b) :
    AntitoneOn
      (fun x : ℝ =>
        ‖deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t) x‖)
      (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) := by
  intro x hx y hy hxy
  have ha_pos_nat : 0 < a :=
    Nat.lt_of_succ_le ha
  have ha_pos_real : 0 < (a : ℝ) :=
    Nat.cast_pos.mpr ha_pos_nat
  have hx_pos : 0 < x :=
    lt_of_lt_of_le ha_pos_real hx.1
  have hy_pos : 0 < y :=
    lt_of_lt_of_le ha_pos_real hy.1
  have hx_deriv :
      ‖deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t) x‖ =
        ‖t‖ / x :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction_deriv_norm_eq
      t hx_pos
  have hy_deriv :
      ‖deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t) y‖ =
        ‖t‖ / y :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction_deriv_norm_eq
      t hy_pos
  have hphase :
      ‖t‖ / y ≤ ‖t‖ / x :=
    Complex.logarithmicPhase_derivativeMagnitude_antitoneOn_positive t
      hx_pos hy_pos hxy
  exact Eq.subst
    (motive := fun target : ℝ =>
      ‖deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t) y‖ ≤
        target)
    hx_deriv.symm
    (Eq.subst
      (motive := fun source : ℝ => source ≤ ‖t‖ / x)
      hy_deriv.symm
      hphase)

/-- The real scalar logarithmic-phase derivative has the same lower bound on
positive integer blocks. -/
theorem Complex.logarithmicPhaseRealPhase_deriv_norm_block_lower_bound
    (t : ℝ)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (_hab : a ≤ b)
    {x : ℝ}
    (hx : x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) :
    ((‖t‖ : ℝ) / ((b + 1 : ℕ) : ℝ)) ≤
      ‖deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x‖ := by
  have ha_pos_nat : 0 < a :=
    Nat.lt_of_succ_le ha
  have hb_pos_nat : 0 < b + 1 :=
    Nat.succ_pos b
  have ha_pos_real : 0 < (a : ℝ) :=
    Nat.cast_pos.mpr ha_pos_nat
  have hx_pos : 0 < x :=
    lt_of_lt_of_le ha_pos_real hx.1
  have hderiv_norm :
      ‖deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x‖ =
        ‖t‖ / x :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_deriv_norm_eq
      t hx_pos
  have hblock :
      ‖t‖ / ((b + 1 : ℕ) : ℝ) ≤ ‖t‖ / x :=
    Complex.logarithmicPhase_derivativeMagnitude_block_lower_bound
      t
      ha_pos_real
      hx
  exact Eq.subst
    (motive := fun target : ℝ => ‖t‖ / ((b + 1 : ℕ) : ℝ) ≤ target)
    hderiv_norm.symm
    hblock

/-- The absolute real scalar-phase derivative is monotone on every positive
integer block. -/
theorem Complex.logarithmicPhaseRealPhase_deriv_norm_antitoneOn_integer_block
    (t : ℝ)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (_hab : a ≤ b) :
    AntitoneOn
      (fun x : ℝ =>
        ‖deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x‖)
      (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) := by
  intro x hx y hy hxy
  have ha_pos_nat : 0 < a :=
    Nat.lt_of_succ_le ha
  have ha_pos_real : 0 < (a : ℝ) :=
    Nat.cast_pos.mpr ha_pos_nat
  have hx_pos : 0 < x :=
    lt_of_lt_of_le ha_pos_real hx.1
  have hy_pos : 0 < y :=
    lt_of_lt_of_le ha_pos_real hy.1
  have hx_deriv :
      ‖deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x‖ =
        ‖t‖ / x :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_deriv_norm_eq
      t hx_pos
  have hy_deriv :
      ‖deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y‖ =
        ‖t‖ / y :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_deriv_norm_eq
      t hy_pos
  have hphase :
      ‖t‖ / y ≤ ‖t‖ / x :=
    Complex.logarithmicPhase_derivativeMagnitude_antitoneOn_positive t
      hx_pos hy_pos hxy
  exact Eq.subst
    (motive := fun target : ℝ =>
      ‖deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y‖ ≤
        target)
    hx_deriv.symm
    (Eq.subst
      (motive := fun source : ℝ => source ≤ ‖t‖ / x)
      hy_deriv.symm
      hphase)

end

end LFunctions
end Boundary
