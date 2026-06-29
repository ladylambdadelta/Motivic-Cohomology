import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.FirstDerivativeBlock

/-!
# Logarithmic phase estimates

This file owns the oscillatory phase `n^{-it}` input used by the
Euler-Maclaurin boundary argument.  The phase is logarithmic, not a
constant-ratio geometric progression.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped ComplexConjugate Topology

/-- Exact second derivative of the real scalar logarithmic phase on the
positive half-line. -/
theorem Complex.logarithmicPhaseRealPhase_secondDerivative_eq
    (t : ℝ)
    {x : ℝ}
    (hx_pos : 0 < x) :
    deriv
      (deriv
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
      x =
      t * (x * x)⁻¹ := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  have hpositive_mem_nhds : Set.Ioi (0 : ℝ) ∈ 𝓝 x :=
    isOpen_Ioi.mem_nhds hx_pos
  have hlocal :
      (fun y : ℝ => deriv φ y) =ᶠ[𝓝 x]
        (fun y : ℝ => -t / y) :=
    hpositive_mem_nhds.mono
      (fun y hy =>
        Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_deriv_eq
          t hy)
  have hinv :
      HasDerivAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) x :=
    hasDerivAt_inv (ne_of_gt hx_pos)
  have hdiv_raw :
      HasDerivAt (fun y : ℝ => -t * y⁻¹)
        ((-t) * (-(x ^ 2)⁻¹)) x :=
    hinv.const_mul (-t)
  have hdiv_fun :
      (fun y : ℝ => -t / y) = (fun y : ℝ => -t * y⁻¹) := by
    funext y
    exact div_eq_mul_inv (-t) y
  have hderiv_scalar :
      (-t) * (-(x ^ 2)⁻¹) = t * (x * x)⁻¹ := by
    have hpow : x ^ 2 = x * x :=
      pow_two x
    calc
      (-t) * (-(x ^ 2)⁻¹) =
          t * (x ^ 2)⁻¹ := by
        exact neg_mul_neg t ((x ^ 2)⁻¹)
      _ = t * (x * x)⁻¹ := by
        exact congrArg (fun r : ℝ => t * r⁻¹) hpow
  have hdiv :
      HasDerivAt (fun y : ℝ => -t / y) (t * (x * x)⁻¹) x :=
    Eq.subst
      (motive := fun f : ℝ → ℝ =>
        HasDerivAt f (t * (x * x)⁻¹) x)
      hdiv_fun.symm
      (hdiv_raw.congr_deriv hderiv_scalar)
  have hderiv_local :
      deriv (fun y : ℝ => deriv φ y) x =
        deriv (fun y : ℝ => -t / y) x :=
    hlocal.deriv_eq
  have hderiv_rhs :
      deriv (fun y : ℝ => -t / y) x = t * (x * x)⁻¹ :=
    hdiv.deriv
  exact Eq.trans hderiv_local hderiv_rhs

/-- In the nonnegative-parameter branch, the logarithmic phase derivative is
the negative reciprocal profile with amplitude `‖t‖`. -/
theorem Complex.logarithmicPhaseRealPhase_deriv_eq_neg_norm_div
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {x : ℝ}
    (hx_pos : 0 < x) :
    deriv
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x =
      -‖t‖ / x := by
  have hderiv :
      deriv
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x =
        -t / x :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_deriv_eq
      t hx_pos
  have hnorm : ‖t‖ = t :=
    Real.norm_of_nonneg ht_nonneg
  have hright : -t / x = -‖t‖ / x := by
    exact congrArg (fun r : ℝ => -r / x) hnorm.symm
  exact Eq.trans hderiv hright

/-- Parenthesized form of the nonnegative-branch derivative identity. -/
theorem Complex.logarithmicPhaseRealPhase_deriv_eq_neg_norm_div_parenthesized
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {x : ℝ}
    (hx_pos : 0 < x) :
    deriv
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x =
      -(‖t‖ / x) := by
  have hderiv :
      deriv
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x =
        -‖t‖ / x :=
    Complex.logarithmicPhaseRealPhase_deriv_eq_neg_norm_div
      t ht_nonneg hx_pos
  have hright :
      -‖t‖ / x = -(‖t‖ / x) :=
    neg_div ‖t‖ x
  exact Eq.trans hderiv hright

/-- The negated derivative in the nonnegative branch is the positive
reciprocal profile `‖t‖ / x`. -/
theorem Complex.logarithmicPhaseRealPhase_neg_deriv_eq_norm_div
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {x : ℝ}
    (hx_pos : 0 < x) :
    -deriv
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x =
      ‖t‖ / x := by
  have hderiv :
      deriv
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x =
        -‖t‖ / x :=
    Complex.logarithmicPhaseRealPhase_deriv_eq_neg_norm_div
      t ht_nonneg hx_pos
  calc
    -deriv
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x =
        -(-‖t‖ / x) := by
      exact congrArg Neg.neg hderiv
    _ = ‖t‖ / x := by
      show -(-(‖t‖ / x)) = ‖t‖ / x
      exact neg_neg (‖t‖ / x)

/-- Lower endpoint bound for the positive reciprocal derivative profile on an
integer block. -/
theorem Complex.logarithmicPhaseRealPhase_neg_deriv_lower_on_integer_block
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    {x : ℝ}
    (hx : x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) :
    ‖t‖ / (((b + 1 : ℕ) : ℝ)) ≤
      -deriv
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x := by
  have ha_pos : (0 : ℝ) < (a : ℝ) :=
    Nat.cast_pos.mpr (Nat.lt_of_succ_le ha)
  have hx_pos : 0 < x :=
    lt_of_lt_of_le ha_pos hx.1
  have hB_pos : 0 < (((b + 1 : ℕ) : ℝ)) :=
    Nat.cast_pos.mpr (Nat.succ_pos b)
  have hneg_deriv :
      -deriv
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x =
      ‖t‖ / x :=
    Complex.logarithmicPhaseRealPhase_neg_deriv_eq_norm_div
      t ht_nonneg hx_pos
  have hamp_nonneg : 0 ≤ ‖t‖ :=
    norm_nonneg t
  have hrecip_le : (((b + 1 : ℕ) : ℝ))⁻¹ ≤ x⁻¹ :=
    inv_anti₀ hx_pos hx.2
  have hdiv_le : ‖t‖ / (((b + 1 : ℕ) : ℝ)) ≤ ‖t‖ / x := by
    have hmul :
        ‖t‖ * (((b + 1 : ℕ) : ℝ))⁻¹ ≤ ‖t‖ * x⁻¹ :=
      mul_le_mul_of_nonneg_left hrecip_le hamp_nonneg
    exact
      Eq.subst
        (motive := fun left : ℝ => left ≤ ‖t‖ / x)
        (div_eq_mul_inv ‖t‖ (((b + 1 : ℕ) : ℝ))).symm
        (Eq.subst
          (motive := fun right : ℝ => ‖t‖ * (((b + 1 : ℕ) : ℝ))⁻¹ ≤ right)
          (div_eq_mul_inv ‖t‖ x).symm
          hmul)
  exact
    Eq.subst
      (motive := fun right : ℝ =>
        ‖t‖ / (((b + 1 : ℕ) : ℝ)) ≤ right)
      hneg_deriv.symm
      hdiv_le

/-- Upper endpoint bound for the positive reciprocal derivative profile on an
integer block. -/
theorem Complex.logarithmicPhaseRealPhase_neg_deriv_upper_on_integer_block
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    {x : ℝ}
    (hx : x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) :
    -deriv
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x ≤
      ‖t‖ / (a : ℝ) := by
  have ha_pos : (0 : ℝ) < (a : ℝ) :=
    Nat.cast_pos.mpr (Nat.lt_of_succ_le ha)
  have hx_pos : 0 < x :=
    lt_of_lt_of_le ha_pos hx.1
  have hneg_deriv :
      -deriv
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x =
      ‖t‖ / x :=
    Complex.logarithmicPhaseRealPhase_neg_deriv_eq_norm_div
      t ht_nonneg hx_pos
  have hamp_nonneg : 0 ≤ ‖t‖ :=
    norm_nonneg t
  have hrecip_le : x⁻¹ ≤ (a : ℝ)⁻¹ :=
    inv_anti₀ ha_pos hx.1
  have hdiv_le : ‖t‖ / x ≤ ‖t‖ / (a : ℝ) := by
    have hmul :
        ‖t‖ * x⁻¹ ≤ ‖t‖ * (a : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left hrecip_le hamp_nonneg
    exact
      Eq.subst
        (motive := fun left : ℝ => left ≤ ‖t‖ / (a : ℝ))
        (div_eq_mul_inv ‖t‖ x).symm
        (Eq.subst
          (motive := fun right : ℝ => ‖t‖ * x⁻¹ ≤ right)
          (div_eq_mul_inv ‖t‖ (a : ℝ)).symm
          hmul)
  exact
    Eq.subst
      (motive := fun left : ℝ => left ≤ ‖t‖ / (a : ℝ))
      hneg_deriv.symm
      hdiv_le

/-- The positive reciprocal derivative image lies in the endpoint interval
`[‖t‖/(b+1), ‖t‖/a]`. -/
theorem Complex.logarithmicPhaseRealPhase_neg_deriv_mem_endpoint_Icc
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    {x : ℝ}
    (hx : x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) :
    -deriv
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x ∈
      Set.Icc (‖t‖ / (((b + 1 : ℕ) : ℝ))) (‖t‖ / (a : ℝ)) := by
  exact And.intro
    (Complex.logarithmicPhaseRealPhase_neg_deriv_lower_on_integer_block
      t ht_nonneg ha hx)
    (Complex.logarithmicPhaseRealPhase_neg_deriv_upper_on_integer_block
      t ht_nonneg ha hx)

/-- The real scalar logarithmic phase has fixed-sign second derivative on
every positive integer block. -/
theorem Complex.logarithmicPhaseRealPhase_secondDerivative_fixedSignOn_integer_block
    (t : ℝ)
    {a b : ℕ}
    (ha : 1 ≤ a) :
    (∀ x : ℝ,
      x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        0 ≤
          deriv
            (deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
            x) ∨
    (∀ x : ℝ,
      x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        deriv
          (deriv
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
          x ≤ 0) := by
  by_cases ht_nonneg : 0 ≤ t
  · exact Or.inl
      (fun x hx =>
        have ha_pos_nat : 0 < a :=
          Nat.lt_of_succ_le ha
        have ha_pos : (0 : ℝ) < (a : ℝ) :=
          Nat.cast_pos.mpr ha_pos_nat
        have hx_pos : 0 < x :=
          lt_of_lt_of_le ha_pos hx.1
        have hxx_pos : 0 < x * x :=
          mul_pos hx_pos hx_pos
        have hinv_nonneg : 0 ≤ (x * x)⁻¹ :=
          inv_nonneg.mpr (le_of_lt hxx_pos)
        have hprod_nonneg : 0 ≤ t * (x * x)⁻¹ :=
          mul_nonneg ht_nonneg hinv_nonneg
        Eq.subst
          (motive := fun r : ℝ => 0 ≤ r)
          (Complex.logarithmicPhaseRealPhase_secondDerivative_eq t hx_pos).symm
          hprod_nonneg)
  · have ht_nonpos : t ≤ 0 :=
      le_of_lt (lt_of_not_ge ht_nonneg)
    exact Or.inr
      (fun x hx =>
        have ha_pos_nat : 0 < a :=
          Nat.lt_of_succ_le ha
        have ha_pos : (0 : ℝ) < (a : ℝ) :=
          Nat.cast_pos.mpr ha_pos_nat
        have hx_pos : 0 < x :=
          lt_of_lt_of_le ha_pos hx.1
        have hxx_pos : 0 < x * x :=
          mul_pos hx_pos hx_pos
        have hinv_nonneg : 0 ≤ (x * x)⁻¹ :=
          inv_nonneg.mpr (le_of_lt hxx_pos)
        have hprod_nonpos : t * (x * x)⁻¹ ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg ht_nonpos hinv_nonneg
        Eq.subst
          (motive := fun r : ℝ => r ≤ 0)
          (Complex.logarithmicPhaseRealPhase_secondDerivative_eq t hx_pos).symm
          hprod_nonpos)

/-- The first derivative of the real logarithmic phase is continuous on every
positive integer block. -/
theorem Complex.logarithmicPhaseRealPhase_deriv_continuousOn_integer_block
    (t : ℝ)
    {a b : ℕ}
    (ha : 1 ≤ a) :
    ContinuousOn
      (fun x : ℝ =>
        deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)
      (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) := by
  have ha_pos : (0 : ℝ) < (a : ℝ) :=
    Nat.cast_pos.mpr (Nat.lt_of_succ_le ha)
  have hmodel_cont :
      ContinuousOn
        (fun x : ℝ => -t / x)
        (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) := by
    exact
      (continuousOn_const.div continuousOn_id
        (fun x hx =>
          ne_of_gt (lt_of_lt_of_le ha_pos hx.1)))
  exact hmodel_cont.congr
    (fun x hx =>
      Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_deriv_eq
        t (lt_of_lt_of_le ha_pos hx.1))

/-- The first derivative of the real logarithmic phase is differentiable on
the interior of every positive integer block. -/
theorem Complex.logarithmicPhaseRealPhase_deriv_differentiableOn_interior_integer_block
    (t : ℝ)
    {a b : ℕ}
    (ha : 1 ≤ a) :
    DifferentiableOn ℝ
      (fun x : ℝ =>
        deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)
      (interior (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ))) := by
  have ha_pos : (0 : ℝ) < (a : ℝ) :=
    Nat.cast_pos.mpr (Nat.lt_of_succ_le ha)
  have hmodel_diff :
      DifferentiableOn ℝ
        (fun x : ℝ => -t / x)
        (interior (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ))) := by
    exact
      ((differentiableOn_const (c := -t)).div differentiableOn_id
        (fun x hx =>
          ne_of_gt
            (lt_of_lt_of_le ha_pos
              ((interior_subset hx).1))))
  exact hmodel_diff.congr
    (fun x hx =>
      Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_deriv_eq
        t
        (lt_of_lt_of_le ha_pos
          ((interior_subset hx).1)))

/-- In the nonnegative-curvature branch, the logarithmic phase derivative grows
at least at the curvature-lower-bound rate across the block. -/
theorem Complex.logarithmicPhaseRealPhase_deriv_growth_of_nonneg_curvature_integer_block
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    {T x y : ℝ}
    (hcurvature_lower :
      ∀ z : ℝ,
        z ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
          T *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹ ≤
            ‖deriv
              (deriv
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
              z‖)
    (hx : x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ))
    (hy : y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ))
    (hxy : x ≤ y) :
    (T *
        ((((b + 1 : ℕ) : ℝ) *
          (((b + 1 : ℕ) : ℝ)))⁻¹) *
        (y - x) ≤
      deriv
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
      deriv
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x := by
  let C : ℝ :=
    T *
      ((((b + 1 : ℕ) : ℝ) *
        (((b + 1 : ℕ) : ℝ)))⁻¹
  have hcont :
      ContinuousOn
        (fun z : ℝ =>
          deriv
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) z)
        (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) :=
    Complex.logarithmicPhaseRealPhase_deriv_continuousOn_integer_block t ha
  have hdiff :
      DifferentiableOn ℝ
        (fun z : ℝ =>
          deriv
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) z)
        (interior (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ))) :=
    Complex.logarithmicPhaseRealPhase_deriv_differentiableOn_interior_integer_block
      t ha
  have hlower :
      ∀ z : ℝ,
        z ∈ interior (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) →
          C ≤
            deriv
              (deriv
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
              z := by
    intro z hz
    have hz_closed :
        z ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) :=
      interior_subset hz
    have ha_pos : (0 : ℝ) < (a : ℝ) :=
      Nat.cast_pos.mpr (Nat.lt_of_succ_le ha)
    have hz_pos : 0 < z :=
      lt_of_lt_of_le ha_pos hz_closed.1
    have hzz_pos : 0 < z * z :=
      mul_pos hz_pos hz_pos
    have hinv_nonneg : 0 ≤ (z * z)⁻¹ :=
      inv_nonneg.mpr (le_of_lt hzz_pos)
    have hsecond_nonneg :
        0 ≤
          deriv
            (deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
            z := by
      have hprod_nonneg : 0 ≤ t * (z * z)⁻¹ :=
        mul_nonneg ht_nonneg hinv_nonneg
      exact
        Eq.subst
          (motive := fun r : ℝ => 0 ≤ r)
          (Complex.logarithmicPhaseRealPhase_secondDerivative_eq t hz_pos).symm
          hprod_nonneg
    have hnorm_eq :
        ‖deriv
          (deriv
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
          z‖ =
        deriv
          (deriv
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
          z :=
      Real.norm_of_nonneg hsecond_nonneg
    exact
      Eq.subst
        (motive := fun r : ℝ => C ≤ r)
        hnorm_eq
        (hcurvature_lower z hz_closed)
  exact
    Real.deriv_growth_from_second_derivative_lower_on_Icc
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      hcont hdiff hlower hx hy hxy

/-- In the nonpositive-curvature branch, the logarithmic phase derivative
decreases at least at the curvature-lower-bound rate across the block. -/
theorem Complex.logarithmicPhaseRealPhase_deriv_drop_of_nonpos_curvature_integer_block
    (t : ℝ)
    (ht_nonpos : t ≤ 0)
    {a b : ℕ}
    (ha : 1 ≤ a)
    {T x y : ℝ}
    (hcurvature_lower :
      ∀ z : ℝ,
        z ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
          T *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹ ≤
            ‖deriv
              (deriv
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
              z‖)
    (hx : x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ))
    (hy : y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ))
    (hxy : x ≤ y) :
    (T *
        ((((b + 1 : ℕ) : ℝ) *
          (((b + 1 : ℕ) : ℝ)))⁻¹) *
        (y - x) ≤
      deriv
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x -
      deriv
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y := by
  let ψ : ℝ → ℝ :=
    fun u : ℝ =>
      -deriv
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) u
  let C : ℝ :=
    T *
      ((((b + 1 : ℕ) : ℝ) *
        (((b + 1 : ℕ) : ℝ)))⁻¹
  have hphase_cont :
      ContinuousOn
        (fun z : ℝ =>
          deriv
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) z)
        (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) :=
    Complex.logarithmicPhaseRealPhase_deriv_continuousOn_integer_block t ha
  have hcont :
      ContinuousOn ψ (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) :=
    hphase_cont.neg
  have hphase_diff :
      DifferentiableOn ℝ
        (fun z : ℝ =>
          deriv
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) z)
        (interior (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ))) :=
    Complex.logarithmicPhaseRealPhase_deriv_differentiableOn_interior_integer_block
      t ha
  have hdiff :
      DifferentiableOn ℝ ψ
        (interior (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ))) :=
    hphase_diff.neg
  have hlower :
      ∀ z : ℝ,
        z ∈ interior (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) →
          C ≤ deriv ψ z := by
    intro z hz
    have hz_closed :
        z ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) :=
      interior_subset hz
    have ha_pos : (0 : ℝ) < (a : ℝ) :=
      Nat.cast_pos.mpr (Nat.lt_of_succ_le ha)
    have hz_pos : 0 < z :=
      lt_of_lt_of_le ha_pos hz_closed.1
    have hzz_pos : 0 < z * z :=
      mul_pos hz_pos hz_pos
    have hinv_nonneg : 0 ≤ (z * z)⁻¹ :=
      inv_nonneg.mpr (le_of_lt hzz_pos)
    have hsecond_nonpos :
        deriv
          (deriv
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
          z ≤ 0 := by
      have hprod_nonpos : t * (z * z)⁻¹ ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg ht_nonpos hinv_nonneg
      exact
        Eq.subst
          (motive := fun r : ℝ => r ≤ 0)
          (Complex.logarithmicPhaseRealPhase_secondDerivative_eq t hz_pos).symm
          hprod_nonpos
    have hnorm_eq :
        ‖deriv
          (deriv
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
          z‖ =
        -deriv
          (deriv
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
          z :=
      Real.norm_of_nonpos hsecond_nonpos
    have hpsi_deriv :
        deriv ψ z =
          -deriv
            (deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
            z := by
      exact deriv_neg
        (fun u : ℝ =>
          deriv
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) u)
        z
    exact
      Eq.subst
        (motive := fun r : ℝ => C ≤ r)
        hpsi_deriv
        (Eq.subst
          (motive := fun r : ℝ => C ≤ r)
          hnorm_eq
          (hcurvature_lower z hz_closed))
  have hgrowth :
      C * (y - x) ≤ ψ y - ψ x :=
    Real.deriv_growth_from_second_derivative_lower_on_Icc
      ψ hcont hdiff hlower hx hy hxy
  have hdrop_eq :
      ψ y - ψ x =
        deriv
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x -
        deriv
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y := by
    calc
      ψ y - ψ x =
          (-deriv
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y) -
          (-deriv
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x) := by
        rfl
      _ =
          deriv
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x -
          deriv
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y := by
        exact neg_sub_neg
          (deriv
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y)
          (deriv
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)
  exact
    Eq.subst
      (motive := fun r : ℝ => C * (y - x) ≤ r)
      hdrop_eq
      hgrowth

/-- Oriented derivative separation supplied by the logarithmic phase curvature
on a positive integer block. -/
theorem Complex.logarithmicPhaseRealPhase_oriented_deriv_separation_integer_block
    (t : ℝ)
    {a b : ℕ}
    (ha : 1 ≤ a)
    {T x y : ℝ}
    (hcurvature_lower :
      ∀ z : ℝ,
        z ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
          T *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹ ≤
            ‖deriv
              (deriv
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
              z‖)
    (hx : x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ))
    (hy : y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ))
    (hxy : x ≤ y) :
    ((T *
        ((((b + 1 : ℕ) : ℝ) *
          (((b + 1 : ℕ) : ℝ)))⁻¹) *
        (y - x) ≤
      deriv
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
      deriv
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x) ∨
    ((T *
        ((((b + 1 : ℕ) : ℝ) *
          (((b + 1 : ℕ) : ℝ)))⁻¹) *
        (y - x) ≤
      deriv
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x -
      deriv
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y) := by
  by_cases ht_nonneg : 0 ≤ t
  · exact Or.inl
      (Complex.logarithmicPhaseRealPhase_deriv_growth_of_nonneg_curvature_integer_block
        t ht_nonneg ha hcurvature_lower hx hy hxy)
  · have ht_nonpos : t ≤ 0 :=
      le_of_lt (lt_of_not_ge ht_nonneg)
    exact Or.inr
      (Complex.logarithmicPhaseRealPhase_deriv_drop_of_nonpos_curvature_integer_block
        t ht_nonpos ha hcurvature_lower hx hy hxy)

/-- The real scalar logarithmic-phase derivative is monotone on every positive
integer block, with orientation determined by the sign of `t`. -/
theorem Complex.logarithmicPhaseRealPhase_deriv_monoOn_integer_block
    (t : ℝ)
    {a b : ℕ}
    (ha : 1 ≤ a) :
    MonotoneOn
      (fun x : ℝ =>
        deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)
      (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) ∨
    AntitoneOn
      (fun x : ℝ =>
        deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)
      (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) := by
  by_cases ht_nonneg : 0 ≤ t
  · exact Or.inl
      (fun x hx y hy hxy =>
        have ha_pos_nat : 0 < a :=
          Nat.lt_of_succ_le ha
        have ha_pos : (0 : ℝ) < (a : ℝ) :=
          Nat.cast_pos.mpr ha_pos_nat
        have hx_pos : 0 < x :=
          lt_of_lt_of_le ha_pos hx.1
        have hy_pos : 0 < y :=
          lt_of_lt_of_le ha_pos hy.1
        have hx_deriv :
            deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x =
              -t / x :=
          Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_deriv_eq
            t hx_pos
        have hy_deriv :
            deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y =
              -t / y :=
          Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_deriv_eq
            t hy_pos
        have hinv_le : y⁻¹ ≤ x⁻¹ :=
          inv_anti₀ hx_pos hxy
        have hneg_t_nonpos : -t ≤ 0 :=
          neg_nonpos.mpr ht_nonneg
        have hphase : -t / x ≤ -t / y := by
          have hmul :
              (-t) * x⁻¹ ≤ (-t) * y⁻¹ :=
            mul_le_mul_of_nonpos_left hinv_le hneg_t_nonpos
          exact Eq.subst
            (motive := fun left : ℝ => left ≤ -t / y)
            (div_eq_mul_inv (-t) x).symm
            (Eq.subst
              (motive := fun right : ℝ => (-t) * x⁻¹ ≤ right)
              (div_eq_mul_inv (-t) y).symm
              hmul)
        Eq.subst
          (motive := fun left : ℝ =>
            left ≤ deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y)
          hx_deriv.symm
          (Eq.subst
            (motive := fun right : ℝ => -t / x ≤ right)
            hy_deriv.symm
            hphase))
  · have ht_nonpos : t ≤ 0 :=
      le_of_lt (lt_of_not_ge ht_nonneg)
    exact Or.inr
      (fun x hx y hy hxy =>
        have ha_pos_nat : 0 < a :=
          Nat.lt_of_succ_le ha
        have ha_pos : (0 : ℝ) < (a : ℝ) :=
          Nat.cast_pos.mpr ha_pos_nat
        have hx_pos : 0 < x :=
          lt_of_lt_of_le ha_pos hx.1
        have hy_pos : 0 < y :=
          lt_of_lt_of_le ha_pos hy.1
        have hx_deriv :
            deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x =
              -t / x :=
          Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_deriv_eq
            t hx_pos
        have hy_deriv :
            deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y =
              -t / y :=
          Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_deriv_eq
            t hy_pos
        have hinv_le : y⁻¹ ≤ x⁻¹ :=
          inv_anti₀ hx_pos hxy
        have hneg_t_nonneg : 0 ≤ -t :=
          neg_nonneg.mpr ht_nonpos
        have hphase : -t / y ≤ -t / x := by
          have hmul :
              (-t) * y⁻¹ ≤ (-t) * x⁻¹ :=
            mul_le_mul_of_nonneg_left hinv_le hneg_t_nonneg
          exact Eq.subst
            (motive := fun left : ℝ => left ≤ -t / x)
            (div_eq_mul_inv (-t) y).symm
            (Eq.subst
              (motive := fun right : ℝ => (-t) * y⁻¹ ≤ right)
              (div_eq_mul_inv (-t) x).symm
              hmul)
        Eq.subst
          (motive := fun left : ℝ =>
            left ≤ deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)
          hy_deriv.symm
          (Eq.subst
            (motive := fun right : ℝ => -t / y ≤ right)
            hx_deriv.symm
            hphase))

/-- Coherent orientation package for the real scalar logarithmic phase:
monotone derivative with nonnegative curvature when `t ≥ 0`, and antitone
derivative with nonpositive curvature when `t ≤ 0`. -/
theorem Complex.logarithmicPhaseRealPhase_secondDerivative_orientationOn_integer_block
    (t : ℝ)
    {a b : ℕ}
    (ha : 1 ≤ a) :
    (MonotoneOn
        (fun x : ℝ =>
          deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)
        (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) ∧
      ∀ x : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
          0 ≤
            deriv
              (deriv
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
              x) ∨
    (AntitoneOn
        (fun x : ℝ =>
          deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)
        (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) ∧
      ∀ x : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
          deriv
            (deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
            x ≤ 0) := by
  by_cases ht_nonneg : 0 ≤ t
  · exact Or.inl
      (And.intro
        (fun x hx y hy hxy =>
          have ha_pos : (0 : ℝ) < (a : ℝ) :=
            Nat.cast_pos.mpr (Nat.lt_of_succ_le ha)
          have hx_pos : 0 < x := lt_of_lt_of_le ha_pos hx.1
          have hy_pos : 0 < y := lt_of_lt_of_le ha_pos hy.1
          have hx_deriv :
              deriv
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x =
                -t / x :=
            Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_deriv_eq
              t hx_pos
          have hy_deriv :
              deriv
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y =
                -t / y :=
            Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_deriv_eq
              t hy_pos
          have hinv_le : y⁻¹ ≤ x⁻¹ :=
            inv_anti₀ hx_pos hxy
          have hneg_t_nonpos : -t ≤ 0 :=
            neg_nonpos.mpr ht_nonneg
          have hphase : -t / x ≤ -t / y := by
            have hmul :
                (-t) * x⁻¹ ≤ (-t) * y⁻¹ :=
              mul_le_mul_of_nonpos_left hinv_le hneg_t_nonpos
            exact Eq.subst
              (motive := fun left : ℝ => left ≤ -t / y)
              (div_eq_mul_inv (-t) x).symm
              (Eq.subst
                (motive := fun right : ℝ => (-t) * x⁻¹ ≤ right)
                (div_eq_mul_inv (-t) y).symm
                hmul)
          Eq.subst
            (motive := fun left : ℝ =>
              left ≤ deriv
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y)
            hx_deriv.symm
            (Eq.subst
              (motive := fun right : ℝ => -t / x ≤ right)
              hy_deriv.symm
              hphase))
        (fun x hx =>
          have ha_pos : (0 : ℝ) < (a : ℝ) :=
            Nat.cast_pos.mpr (Nat.lt_of_succ_le ha)
          have hx_pos : 0 < x := lt_of_lt_of_le ha_pos hx.1
          have hxx_pos : 0 < x * x := mul_pos hx_pos hx_pos
          have hinv_nonneg : 0 ≤ (x * x)⁻¹ :=
            inv_nonneg.mpr (le_of_lt hxx_pos)
          have hprod_nonneg : 0 ≤ t * (x * x)⁻¹ :=
            mul_nonneg ht_nonneg hinv_nonneg
          Eq.subst
            (motive := fun r : ℝ => 0 ≤ r)
            (Complex.logarithmicPhaseRealPhase_secondDerivative_eq t hx_pos).symm
            hprod_nonneg))
  · have ht_nonpos : t ≤ 0 :=
      le_of_lt (lt_of_not_ge ht_nonneg)
    exact Or.inr
      (And.intro
        (fun x hx y hy hxy =>
          have ha_pos : (0 : ℝ) < (a : ℝ) :=
            Nat.cast_pos.mpr (Nat.lt_of_succ_le ha)
          have hx_pos : 0 < x := lt_of_lt_of_le ha_pos hx.1
          have hy_pos : 0 < y := lt_of_lt_of_le ha_pos hy.1
          have hx_deriv :
              deriv
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x =
                -t / x :=
            Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_deriv_eq
              t hx_pos
          have hy_deriv :
              deriv
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y =
                -t / y :=
            Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_deriv_eq
              t hy_pos
          have hinv_le : y⁻¹ ≤ x⁻¹ :=
            inv_anti₀ hx_pos hxy
          have hneg_t_nonneg : 0 ≤ -t :=
            neg_nonneg.mpr ht_nonpos
          have hphase : -t / y ≤ -t / x := by
            have hmul :
                (-t) * y⁻¹ ≤ (-t) * x⁻¹ :=
              mul_le_mul_of_nonneg_left hinv_le hneg_t_nonneg
            exact Eq.subst
              (motive := fun left : ℝ => left ≤ -t / x)
              (div_eq_mul_inv (-t) y).symm
              (Eq.subst
                (motive := fun right : ℝ => (-t) * y⁻¹ ≤ right)
                (div_eq_mul_inv (-t) x).symm
                hmul)
          Eq.subst
            (motive := fun left : ℝ =>
              left ≤ deriv
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)
            hy_deriv.symm
            (Eq.subst
              (motive := fun right : ℝ => -t / y ≤ right)
              hx_deriv.symm
              hphase))
        (fun x hx =>
          have ha_pos : (0 : ℝ) < (a : ℝ) :=
            Nat.cast_pos.mpr (Nat.lt_of_succ_le ha)
          have hx_pos : 0 < x := lt_of_lt_of_le ha_pos hx.1
          have hxx_pos : 0 < x * x := mul_pos hx_pos hx_pos
          have hinv_nonneg : 0 ≤ (x * x)⁻¹ :=
            inv_nonneg.mpr (le_of_lt hxx_pos)
          have hprod_nonpos : t * (x * x)⁻¹ ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg ht_nonpos hinv_nonneg
          Eq.subst
            (motive := fun r : ℝ => r ≤ 0)
            (Complex.logarithmicPhaseRealPhase_secondDerivative_eq t hx_pos).symm
            hprod_nonpos))

/-- Concrete second-derivative curvature lower bound for the real scalar
logarithmic phase on an integer block. -/
theorem Complex.logarithmicPhaseRealPhase_secondDerivative_curvature_lower
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    ∀ x : ℝ,
      x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        ‖t‖ *
            ((((b + 1 : ℕ) : ℝ) *
              (((b + 1 : ℕ) : ℝ)))⁻¹ ≤
          ‖deriv
            (deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
            x‖ := by
  intro x hx
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  let B : ℝ := ((b + 1 : ℕ) : ℝ)
  have ha_pos_nat : 0 < a :=
    Nat.lt_of_succ_le ha
  have ha_pos : (0 : ℝ) < (a : ℝ) :=
    Nat.cast_pos.mpr ha_pos_nat
  have hx_pos : (0 : ℝ) < x :=
    lt_of_lt_of_le ha_pos hx.1
  have hx_nonneg : 0 ≤ x :=
    le_of_lt hx_pos
  have hB_pos : (0 : ℝ) < B :=
    Nat.cast_pos.mpr (Nat.succ_pos b)
  have hB_nonneg : 0 ≤ B :=
    le_of_lt hB_pos
  have hx_le_B : x ≤ B :=
    hx.2
  have hxx_pos : 0 < x * x :=
    mul_pos hx_pos hx_pos
  have hxx_nonneg : 0 ≤ x * x :=
    le_of_lt hxx_pos
  have hxx_le_BB : x * x ≤ B * B :=
    mul_le_mul hx_le_B hx_le_B hx_nonneg hB_nonneg
  have hden_inv :
      (B * B)⁻¹ ≤ (x * x)⁻¹ :=
    inv_le_inv₀ hxx_pos hxx_le_BB
  have hscale :
      ‖t‖ * (B * B)⁻¹ ≤ ‖t‖ * (x * x)⁻¹ :=
    mul_le_mul_of_nonneg_left hden_inv (norm_nonneg t)
  have hpositive_mem_nhds : Set.Ioi (0 : ℝ) ∈ 𝓝 x :=
    isOpen_Ioi.mem_nhds hx_pos
  have hlocal :
      (fun y : ℝ => deriv φ y) =ᶠ[𝓝 x]
        (fun y : ℝ => -t / y) :=
    hpositive_mem_nhds.mono
      (fun y hy =>
        Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_deriv_eq
          t hy)
  have hinv :
      HasDerivAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) x :=
    hasDerivAt_inv (ne_of_gt hx_pos)
  have hdiv_raw :
      HasDerivAt (fun y : ℝ => -t * y⁻¹)
        ((-t) * (-(x ^ 2)⁻¹)) x :=
    hinv.const_mul (-t)
  have hdiv_fun :
      (fun y : ℝ => -t / y) = (fun y : ℝ => -t * y⁻¹) := by
    funext y
    exact div_eq_mul_inv (-t) y
  have hderiv_scalar :
      (-t) * (-(x ^ 2)⁻¹) = t * (x * x)⁻¹ := by
    have hpow : x ^ 2 = x * x :=
      pow_two x
    calc
      (-t) * (-(x ^ 2)⁻¹) =
          t * (x ^ 2)⁻¹ := by
        exact neg_mul_neg t ((x ^ 2)⁻¹)
      _ = t * (x * x)⁻¹ := by
        exact congrArg (fun r : ℝ => t * r⁻¹) hpow
  have hdiv :
      HasDerivAt (fun y : ℝ => -t / y) (t * (x * x)⁻¹) x :=
    Eq.subst
      (motive := fun f : ℝ → ℝ =>
        HasDerivAt f (t * (x * x)⁻¹) x)
      hdiv_fun.symm
      (hdiv_raw.congr_deriv hderiv_scalar)
  have hderiv_eq :
      deriv (deriv φ) x = t * (x * x)⁻¹ := by
    have hderiv_local :
        deriv (fun y : ℝ => deriv φ y) x =
          deriv (fun y : ℝ => -t / y) x :=
      hlocal.deriv_eq
    have hderiv_rhs :
        deriv (fun y : ℝ => -t / y) x = t * (x * x)⁻¹ :=
      hdiv.deriv
    exact Eq.trans hderiv_local hderiv_rhs
  have hnorm_second :
      ‖deriv (deriv φ) x‖ = ‖t‖ * (x * x)⁻¹ := by
    calc
      ‖deriv (deriv φ) x‖ =
          ‖t * (x * x)⁻¹‖ := by
        exact congrArg norm hderiv_eq
      _ = ‖t‖ * ‖(x * x)⁻¹‖ :=
        norm_mul t ((x * x)⁻¹)
      _ = ‖t‖ * ‖x * x‖⁻¹ := by
        exact congrArg (fun r : ℝ => ‖t‖ * r) (norm_inv (x * x))
      _ = ‖t‖ * (x * x)⁻¹ := by
        exact congrArg (fun r : ℝ => ‖t‖ * r⁻¹)
          (Real.norm_of_nonneg hxx_nonneg)
  exact
    Eq.subst
      (motive := fun r : ℝ =>
        ‖t‖ * (B * B)⁻¹ ≤ r)
      hnorm_second.symm
      hscale

/-- Reversing the frequency parameter negates the real logarithmic phase. -/
theorem Complex.logarithmicPhaseRealPhase_neg_parameter_eq_neg
    (t x : ℝ) :
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase (-t) x =
      -Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t x := by
  let L : ℝ := Real.log x
  have hleft :
      Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase (-t) x =
        t * L := by
    calc
      Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase (-t) x =
          -(-t) * L := by
        rfl
      _ = t * L := by
        exact congrArg (fun y : ℝ => y * L) (neg_neg t)
  have hright :
      -Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t x =
        t * L := by
    calc
      -Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t x =
          -(-t * L) := by
        rfl
      _ = -(-(t * L)) := by
        exact congrArg Neg.neg (neg_mul t L)
      _ = t * L :=
        neg_neg (t * L)
  exact Eq.trans hleft hright.symm

/-- Reversing the frequency conjugates each real-phase exponential term. -/
theorem Complex.logarithmicPhaseRealPhase_exp_neg_parameter_eq_conj
    (t : ℝ)
    (n : ℕ) :
    Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase (-t) n : ℂ)) =
      conj
        (Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))) := by
  let θ : ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n
  have hphase_neg :
      Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase (-t) n =
        -θ :=
    Complex.logarithmicPhaseRealPhase_neg_parameter_eq_neg t n
  have harg :
      Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase (-t) n : ℂ) =
        conj (Complex.I * (θ : ℂ)) := by
    calc
      Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase (-t) n : ℂ) =
          Complex.I * ((-θ : ℝ) : ℂ) := by
        exact congrArg (fun r : ℝ => Complex.I * (r : ℂ)) hphase_neg
      _ = Complex.I * (-(θ : ℂ)) := by
        exact congrArg (fun z : ℂ => Complex.I * z) (Complex.ofReal_neg θ)
      _ = -(Complex.I * (θ : ℂ)) := by
        exact mul_neg Complex.I (θ : ℂ)
      _ = (-Complex.I) * (θ : ℂ) := by
        exact (neg_mul Complex.I (θ : ℂ)).symm
      _ = conj Complex.I * conj (θ : ℂ) := by
        exact congrArg (fun z : ℂ => z * (θ : ℂ)) conj_I.symm
      _ = conj (Complex.I * (θ : ℂ)) := by
        exact (map_mul conj (Complex.I) (θ : ℂ)).symm
  calc
    Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase (-t) n : ℂ)) =
        Complex.exp (conj (Complex.I * (θ : ℂ))) := by
      exact congrArg Complex.exp harg
    _ = conj
        (Complex.exp (Complex.I * (θ : ℂ))) :=
      Complex.exp_conj (Complex.I * (θ : ℂ))

/-- Reversing the frequency preserves the norm of a logarithmic real-phase
block sum. -/
theorem Complex.logarithmicPhaseRealPhase_block_norm_neg_parameter_eq
    (t : ℝ)
    (a b : ℕ) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase (-t) n : ℂ))‖ =
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ := by
  have hsum :
      (∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase (-t) n : ℂ))) =
        conj
          (∑ n ∈ Finset.Icc a b,
            Complex.exp
              (Complex.I *
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))) := by
    calc
      (∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase (-t) n : ℂ))) =
          ∑ n ∈ Finset.Icc a b,
            conj
              (Complex.exp
                (Complex.I *
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))) := by
        exact Finset.sum_congr rfl
          (fun n hn =>
            Complex.logarithmicPhaseRealPhase_exp_neg_parameter_eq_conj t n)
      _ =
          conj
            (∑ n ∈ Finset.Icc a b,
              Complex.exp
                (Complex.I *
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))) := by
        exact (map_sum (starRingEnd ℂ)
          (fun n : ℕ =>
            Complex.exp
              (Complex.I *
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ)))
          (Finset.Icc a b)).symm
  exact Eq.trans
    (congrArg norm hsum)
    (RCLike.norm_conj
      (∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))))

/-- Shifted logarithmic phase used in the Weyl differencing step. -/
def Complex.logarithmicPhaseRealPhase_shiftedDifference
    (t : ℝ)
    (h : ℕ)
    (x : ℝ) : ℝ :=
  Complex.realPhase_secondDerivative_vdc_shiftedDifference
    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) h x

/-- The derivative of the shifted logarithmic phase difference is the
difference of the endpoint derivatives. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_deriv_eq
    (t : ℝ)
    {h : ℕ}
    {x : ℝ}
    (hx : 0 < x) :
    deriv (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) x =
      deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (x + h) -
        deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  have hh_nonneg : (0 : ℝ) ≤ ((h : ℕ) : ℝ) :=
    Nat.cast_nonneg h
  have hx_shift_pos : 0 < x + h :=
    lt_of_lt_of_le hx (le_add_of_nonneg_right hh_nonneg)
  have hleft :
      HasDerivAt (fun y : ℝ => φ (y + h))
        (deriv φ (x + h)) x := by
    have hid : HasDerivAt (fun y : ℝ => y) 1 x :=
      hasDerivAt_id x
    have hshift : HasDerivAt (fun y : ℝ => y + h) 1 x :=
      hid.add_const h
    have hphase :
        HasDerivAt φ (deriv φ (x + h)) (x + h) :=
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_hasDerivAt
        t hx_shift_pos)
    have hcomp :
        HasDerivAt (fun y : ℝ => φ (y + h))
          ((deriv φ (x + h)) * 1) x :=
      hphase.comp x hshift
    exact Eq.subst
      (motive := fun d : ℝ =>
        HasDerivAt (fun y : ℝ => φ (y + h)) d x)
      (mul_one (deriv φ (x + h)))
      hcomp
  have hright :
      HasDerivAt φ (deriv φ x) x :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_hasDerivAt
      t hx
  have hsub :
      HasDerivAt
        (fun y : ℝ => φ (y + h) - φ y)
        (deriv φ (x + h) - deriv φ x)
        x :=
    hleft.sub hright
  exact hsub.deriv

/-- A summation index in the shifted-correlation range lies in the parent
real block. -/
theorem Nat.cast_mem_parent_Icc_of_mem_shifted_Icc
    {a b h n : ℕ}
    (hn : n ∈ Finset.Icc a (b - h)) :
    (n : ℝ) ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) := by
  have hn_bounds : a ≤ n ∧ n ≤ b - h :=
    Finset.mem_Icc.mp hn
  have hn_le_b : n ≤ b := by
    have hb_sub_le : b - h ≤ b :=
      Nat.sub_le b h
    exact le_trans hn_bounds.2 hb_sub_le
  exact
    And.intro
      (Nat.cast_le.mpr hn_bounds.1)
      (Nat.cast_le.mpr (le_trans hn_le_b (Nat.le_succ b)))

/-- A shifted summation index in the shifted-correlation range lies in the
parent real block. -/
theorem Nat.cast_add_mem_parent_Icc_of_mem_shifted_Icc
    {a b h n : ℕ}
    (hh : h ≤ b - a)
    (hn : n ∈ Finset.Icc a (b - h)) :
    ((n : ℝ) + h) ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) := by
  have hn_bounds : a ≤ n ∧ n ≤ b - h :=
    Finset.mem_Icc.mp hn
  have h_le_b : h ≤ b :=
    le_trans hh (Nat.sub_le b a)
  have hn_add_le_sub_add : n + h ≤ (b - h) + h :=
    Nat.add_le_add_right hn_bounds.2 h
  have hsub_add_eq : (b - h) + h = b :=
    Nat.sub_add_cancel h_le_b
  have hn_add_le_b : n + h ≤ b :=
    Eq.subst
      (motive := fun r : ℕ => n + h ≤ r)
      hsub_add_eq
      hn_add_le_sub_add
  have ha_le_n_add : a ≤ n + h :=
    le_trans hn_bounds.1 (Nat.le_add_right n h)
  have hcast_add :
      (((n + h : ℕ) : ℝ)) = (n : ℝ) + h :=
    Nat.cast_add n h
  exact
    Eq.subst
      (motive := fun x : ℝ =>
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ))
      hcast_add
      (And.intro
        (Nat.cast_le.mpr ha_le_n_add)
        (Nat.cast_le.mpr (le_trans hn_add_le_b (Nat.le_succ b))))

/-- The right endpoint of the shifted real interval transports to the right
endpoint of the parent interval. -/
theorem Nat.cast_shifted_endpoint_add_le_parent_endpoint
    {a b h : ℕ}
    (hh : h ≤ b - a) :
    (((b - h + 1 : ℕ) : ℝ) + h) ≤ ((b + 1 : ℕ) : ℝ) := by
  have h_le_b : h ≤ b :=
    le_trans hh (Nat.sub_le b a)
  have hend_nat :
      (b - h + 1) + h = b + 1 := by
    calc
      (b - h + 1) + h = (b - h + h) + 1 :=
        add_right_comm (b - h) 1 h
      _ = b + 1 :=
        congrArg (fun n : ℕ => n + 1) (Nat.sub_add_cancel h_le_b)
  have hend_cast :
      (((b - h + 1) + h : ℕ) : ℝ) = ((b + 1 : ℕ) : ℝ) :=
    congrArg (fun n : ℕ => (n : ℝ)) hend_nat
  have hleft_cast :
      (((b - h + 1) + h : ℕ) : ℝ) =
        ((b - h + 1 : ℕ) : ℝ) + h :=
    Nat.cast_add (b - h + 1) h
  exact
    Eq.subst
      (motive := fun r : ℝ =>
        r ≤ ((b + 1 : ℕ) : ℝ))
      hleft_cast
      (le_of_eq hend_cast)

/-- A point in the shifted real interval lies in the parent real block. -/
theorem Real.mem_parent_Icc_of_mem_shifted_Icc
    {a b h : ℕ}
    {x : ℝ}
    (hx : x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)) :
    x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) := by
  have hright_nat : b - h + 1 ≤ b + 1 :=
    Nat.succ_le_succ (Nat.sub_le b h)
  exact
    And.intro hx.1
      (le_trans hx.2 (Nat.cast_le.mpr hright_nat))

/-- A shifted point in the shifted real interval lies in the parent real
block. -/
theorem Real.add_nat_mem_parent_Icc_of_mem_shifted_Icc
    {a b h : ℕ}
    {x : ℝ}
    (hh : h ≤ b - a)
    (hx : x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)) :
    x + h ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) := by
  have hh_nonneg : (0 : ℝ) ≤ ((h : ℕ) : ℝ) :=
    Nat.cast_nonneg h
  have hleft : (a : ℝ) ≤ x + h :=
    le_trans hx.1 (le_add_of_nonneg_right hh_nonneg)
  have hright :
      x + h ≤ ((b + 1 : ℕ) : ℝ) :=
    le_trans
      (add_le_add_right hx.2 ((h : ℕ) : ℝ))
      (Nat.cast_shifted_endpoint_add_le_parent_endpoint hh)
  exact And.intro hleft hright

/-- Derivative lower bound for a shifted logarithmic phase difference in the
positive-frequency branch. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_deriv_lower_of_growth
    (t : ℝ)
    {a b h : ℕ}
    {x : ℝ}
    (ha : 1 ≤ a)
    (hx : x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ))
    (hx_shift :
      x + h ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ))
    (hderiv_growth :
      ∀ u v : ℝ,
        u ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        v ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        u ≤ v →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (v - u) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) v -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) u)) :
    (‖t‖ *
        ((((b + 1 : ℕ) : ℝ) *
          (((b + 1 : ℕ) : ℝ)))⁻¹) *
        ((h : ℕ) : ℝ) ≤
      deriv (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) x := by
  have ha_pos : (0 : ℝ) < (a : ℝ) :=
    Nat.cast_pos.mpr (Nat.lt_of_succ_le ha)
  have hx_pos : 0 < x :=
    lt_of_lt_of_le ha_pos hx.1
  have hh_nonneg : (0 : ℝ) ≤ ((h : ℕ) : ℝ) :=
    Nat.cast_nonneg h
  have hx_le_shift : x ≤ x + h :=
    le_add_of_nonneg_right hh_nonneg
  have hgrowth :
      (‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          ((x + h) - x) ≤
        deriv
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) (x + h) -
        deriv
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x :=
    hderiv_growth x (x + h) hx hx_shift hx_le_shift
  have hdiff :
      (x + h) - x = ((h : ℕ) : ℝ) := by
    calc
      (x + h) - x = h :=
        add_sub_cancel_left x ((h : ℕ) : ℝ)
  have hderiv_eq :
      deriv (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) x =
        deriv
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) (x + h) -
        deriv
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_deriv_eq t hx_pos
  exact
    Eq.subst
      (motive := fun left : ℝ =>
        left ≤ deriv (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) x)
      (congrArg
        (fun r : ℝ =>
          ‖t‖ *
            ((((b + 1 : ℕ) : ℝ) *
              (((b + 1 : ℕ) : ℝ)))⁻¹) *
            r)
        hdiff)
      (Eq.subst
        (motive := fun right : ℝ =>
          ‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              ((x + h) - x) ≤ right)
        hderiv_eq.symm
        hgrowth)

/-- Integer-index form of the shifted-difference derivative lower bound on a
shifted-correlation packet. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_deriv_lower_of_growth_at_nat
    (t : ℝ)
    {a b h n : ℕ}
    (ha : 1 ≤ a)
    (hh : h ≤ b - a)
    (hn : n ∈ Finset.Icc a (b - h))
    (hderiv_growth :
      ∀ u v : ℝ,
        u ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        v ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        u ≤ v →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (v - u) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) v -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) u)) :
    (‖t‖ *
        ((((b + 1 : ℕ) : ℝ) *
          (((b + 1 : ℕ) : ℝ)))⁻¹) *
        ((h : ℕ) : ℝ) ≤
      deriv (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) n := by
  have hn_parent :
      (n : ℝ) ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) :=
    Nat.cast_mem_parent_Icc_of_mem_shifted_Icc hn
  have hn_shift_parent :
      ((n : ℝ) + h) ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) :=
    Nat.cast_add_mem_parent_Icc_of_mem_shifted_Icc hh hn
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_deriv_lower_of_growth
      t ha hn_parent hn_shift_parent hderiv_growth

/-- Real-interval form of the shifted-difference derivative lower bound on a
shifted-correlation packet. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_deriv_lower_on_shifted_Icc
    (t : ℝ)
    {a b h : ℕ}
    (ha : 1 ≤ a)
    (hh : h ≤ b - a)
    {x : ℝ}
    (hx : x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ))
    (hderiv_growth :
      ∀ u v : ℝ,
        u ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        v ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        u ≤ v →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (v - u) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) v -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) u)) :
    (‖t‖ *
        ((((b + 1 : ℕ) : ℝ) *
          (((b + 1 : ℕ) : ℝ)))⁻¹) *
        ((h : ℕ) : ℝ) ≤
      deriv (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) x := by
  have hx_parent :
      x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) :=
    Real.mem_parent_Icc_of_mem_shifted_Icc hx
  have hx_shift_parent :
      x + h ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) :=
    Real.add_nat_mem_parent_Icc_of_mem_shifted_Icc hh hx
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_deriv_lower_of_growth
      t ha hx_parent hx_shift_parent hderiv_growth

/-- Normed real-interval form of the shifted-difference derivative lower
bound. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_deriv_norm_lower_on_shifted_Icc
    (t : ℝ)
    {a b h : ℕ}
    (ha : 1 ≤ a)
    (hh : h ≤ b - a)
    {x : ℝ}
    (hx : x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ))
    (hderiv_growth :
      ∀ u v : ℝ,
        u ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        v ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        u ≤ v →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (v - u) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) v -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) u)) :
    (‖t‖ *
        ((((b + 1 : ℕ) : ℝ) *
          (((b + 1 : ℕ) : ℝ)))⁻¹) *
        ((h : ℕ) : ℝ) ≤
      ‖deriv (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) x‖ := by
  have hlower :
      (‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          ((h : ℕ) : ℝ) ≤
        deriv (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) x) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_deriv_lower_on_shifted_Icc
      t ha hh hx hderiv_growth
  exact
    le_trans hlower
      (le_abs_self
        (deriv (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) x))

/-- The shifted-difference lower-derivative scale is positive for nonzero
shift and nonzero logarithmic frequency. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_lowerParameter_pos
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {b h : ℕ}
    (hpos : 1 ≤ h) :
    0 <
      ‖t‖ *
        ((((b + 1 : ℕ) : ℝ) *
          (((b + 1 : ℕ) : ℝ)))⁻¹) *
        ((h : ℕ) : ℝ) := by
  have ht_pos : 0 < ‖t‖ :=
    lt_of_lt_of_le zero_lt_one ht
  have hB_pos : 0 < (((b + 1 : ℕ) : ℝ)) :=
    Nat.cast_pos.mpr (Nat.succ_pos b)
  have hBB_pos :
      0 <
        (((b + 1 : ℕ) : ℝ) *
          (((b + 1 : ℕ) : ℝ))) :=
    mul_pos hB_pos hB_pos
  have hBB_inv_pos :
      0 <
        ((((b + 1 : ℕ) : ℝ) *
          (((b + 1 : ℕ) : ℝ)))⁻¹) :=
    inv_pos.mpr hBB_pos
  have hh_pos : 0 < ((h : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.lt_of_succ_le hpos)
  exact
    mul_pos
      (mul_pos ht_pos hBB_inv_pos)
      hh_pos

/-- Shifted correlation sum appearing in Weyl differencing for the logarithmic
real phase. -/
def Complex.logarithmicPhaseRealPhase_shiftedCorrelation
    (t : ℝ)
    (h a b : ℕ) : ℂ :=
  Complex.realPhase_secondDerivative_vdc_shiftedCorrelation
    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) h a b

/-- Trivial cardinality bound for a shifted logarithmic correlation. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedCorrelation_norm_le_card
    (t : ℝ)
    (h a b : ℕ) :
    ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖ ≤
      ((Finset.Icc a (b - h)).card : ℝ) := by
  exact
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelation_norm_le_card
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      h a b

/-- Finite first-derivative estimate for a shifted correlation packet, with
the actual Kusmin-Landau hypotheses exposed.

The lower bound on the derivative of the shifted phase is not enough by
itself: the adjacent shifted increments must also remain separated from
`2πℤ`, and the reduced increments must be monotone. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedCorrelation_bound_of_firstDerivative_data
    (t : ℝ)
    {a b h : ℕ}
    {lam : ℝ}
    (ha : 1 ≤ a)
    (habh : a ≤ b - h)
    (hlam_pos : 0 < lam)
    (hderiv_antitone :
      AntitoneOn
        (fun x : ℝ =>
          ‖deriv (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) x‖)
        (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)))
    (hderiv_lower :
      ∀ x : ℝ,
        x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ) →
          lam ≤
            ‖deriv (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) x‖)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) a (b - h))
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) a (b - h))
    (hsep :
      Complex.realPhase_integerIncrementSeparatedOn
        (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) a (b - h) lam) :
    ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖ ≤
      4 * (lam⁻¹ + 1) + 4 * Real.pi * lam⁻¹ := by
  exact
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelation_bound_of_firstDerivative_data
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      ha habh hlam_pos hderiv_antitone hderiv_lower
      hinc_mono hred_mono hsep

/-- Shifted-correlation bound where the derivative lower bound is supplied by
the positive-curvature growth of the parent logarithmic phase.  The only
remaining hypotheses are the genuinely separate finite-difference data:
monotonicity and separation of shifted adjacent increments. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedCorrelation_bound_of_growth_and_firstDerivative_data
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b h : ℕ}
    (ha : 1 ≤ a)
    (hpos : 1 ≤ h)
    (hh : h ≤ b - a)
    (habh : a ≤ b - h)
    (hderiv_growth :
      ∀ u v : ℝ,
        u ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        v ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        u ≤ v →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (v - u) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) v -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) u))
    (hderiv_antitone :
      AntitoneOn
        (fun x : ℝ =>
          ‖deriv (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) x‖)
        (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)))
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) a (b - h))
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) a (b - h))
    (hsep :
      Complex.realPhase_integerIncrementSeparatedOn
        (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) a (b - h)
        (‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          ((h : ℕ) : ℝ))) :
    ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖ ≤
      4 *
          ((‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              ((h : ℕ) : ℝ))⁻¹ +
            1) +
        4 * Real.pi *
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              ((h : ℕ) : ℝ))⁻¹ := by
  let lam : ℝ :=
    ‖t‖ *
        ((((b + 1 : ℕ) : ℝ) *
          (((b + 1 : ℕ) : ℝ)))⁻¹) *
      ((h : ℕ) : ℝ)
  have hlam_pos : 0 < lam :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_lowerParameter_pos
      t ht hpos
  have hderiv_lower :
      ∀ x : ℝ,
        x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ) →
          lam ≤
            ‖deriv (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) x‖ :=
    fun x hx =>
      Complex.logarithmicPhaseRealPhase_shiftedDifference_deriv_norm_lower_on_shifted_Icc
        t ha hh hx hderiv_growth
  exact
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelation_bound_of_curvatureScale_data
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      ht ha hpos habh hderiv_antitone hderiv_lower
      hinc_mono hred_mono hsep

/-- Concrete endpoint data for a nonempty logarithmic derivative-frequency
packet in the positive-frequency long branch.

This specializes the generic packet endpoint lemma to
`φ(x) = -t log x` and records the exact derivative-growth hypothesis needed by
the remaining logarithmic B-process. -/
theorem Complex.logarithmicPhaseRealPhase_nonempty_derivPacket_endpoint_data_of_growth
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    {m : ℤ}
    (hp :
      (Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m).Nonempty)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ∃ p q : ℕ,
      p ∈ Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m ∧
      q ∈ Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m ∧
      (p : ℝ) ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) ∧
      (q : ℝ) ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) ∧
      p ≤ q ∧
      (‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          ((q : ℝ) - (p : ℝ)) ≤
        deriv
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (q : ℝ) -
        deriv
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (p : ℝ)) ∧
      deriv
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) q -
        deriv
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) p < 1 ∧
      ((Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m).card : ℝ) ≤
        (((q + 1 : ℕ) : ℝ) - (p : ℝ)) := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  let p : ℕ :=
    (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).min' hp
  let q : ℕ :=
    (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).max' hp
  have hp_mem :
      p ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_min_mem φ hp
  have hq_mem :
      q ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_max_mem φ hp
  have hp_block_nat : p ∈ Finset.Icc a b :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block φ hp_mem
  have hq_block_nat : q ∈ Finset.Icc a b :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block φ hq_mem
  have hp_bounds_nat : a ≤ p ∧ p ≤ b :=
    Finset.mem_Icc.mp hp_block_nat
  have hq_bounds_nat : a ≤ q ∧ q ≤ b :=
    Finset.mem_Icc.mp hq_block_nat
  have hp_interval :
      (p : ℝ) ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) :=
    And.intro
      (Nat.cast_le.mpr hp_bounds_nat.1)
      (Nat.cast_le.mpr
        (le_trans hp_bounds_nat.2 (Nat.le_succ b)))
  have hq_interval :
      (q : ℝ) ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) :=
    And.intro
      (Nat.cast_le.mpr hq_bounds_nat.1)
      (Nat.cast_le.mpr
        (le_trans hq_bounds_nat.2 (Nat.le_succ b)))
  have hp_le_q : p ≤ q :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_min_le_of_mem
      φ hp hq_mem
  have hpq_real : (p : ℝ) ≤ (q : ℝ) :=
    Nat.cast_le.mpr hp_le_q
  have hgrowth :
      (‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          ((q : ℝ) - (p : ℝ)) ≤
        deriv φ (q : ℝ) - deriv φ (p : ℝ)) :=
    hderiv_growth (p : ℝ) (q : ℝ) hp_interval hq_interval hpq_real
  have hwindow :
      deriv φ q - deriv φ p < 1 :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_deriv_sub_lt_one
      φ hp_mem hq_mem
  have hendpoint_card :
      ((Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).card : ℝ) ≤
        (((q + 1 : ℕ) : ℝ) - (p : ℝ)) :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_card_le_endpoint_span
      φ hp
  exact Exists.intro p
    (Exists.intro q
      (And.intro hp_mem
        (And.intro hq_mem
          (And.intro hp_interval
            (And.intro hq_interval
              (And.intro hp_le_q
                (And.intro hgrowth
                  (And.intro hwindow hendpoint_card))))))))

/-- The endpoint span of one nonempty logarithmic derivative packet has
curvature-scale product strictly below one. -/
theorem Complex.logarithmicPhaseRealPhase_nonempty_derivPacket_scaled_span_lt_one
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    {p q : ℕ}
    {k : ℤ}
    (hp_mem :
      p ∈ Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b k)
    (hq_mem :
      q ∈ Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b k)
    (hgrowth :
      (‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          ((q : ℝ) - (p : ℝ)) ≤
        deriv
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (q : ℝ) -
        deriv
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (p : ℝ))) :
    ‖t‖ *
        ((((b + 1 : ℕ) : ℝ) *
          (((b + 1 : ℕ) : ℝ)))⁻¹) *
        ((q : ℝ) - (p : ℝ)) < 1 := by
  have hwindow :
      deriv
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        q -
        deriv
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) p < 1 :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_deriv_sub_lt_one
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      hp_mem hq_mem
  exact lt_of_le_of_lt hgrowth hwindow

/-- Arithmetic conversion from curvature-scaled endpoint span below one to
the reciprocal curvature-scale endpoint bound. -/
theorem Real.logarithmicPhaseRealPhase_span_le_curvatureScale_add_one
    {t : ℝ}
    (ht : 1 ≤ ‖t‖)
    {b p q : ℕ}
    (hscaled :
      ‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          ((q : ℝ) - (p : ℝ)) < 1) :
    (((q + 1 : ℕ) : ℝ) - (p : ℝ)) ≤
      ((((b + 1 : ℕ) : ℝ) * (((b + 1 : ℕ) : ℝ))) / ‖t‖ + 1) := by
  let A : ℝ := ‖t‖
  let B : ℝ := ((b + 1 : ℕ) : ℝ)
  let Bsq : ℝ := B * B
  let x : ℝ := (q : ℝ) - (p : ℝ)
  have hA_pos : 0 < A :=
    lt_of_lt_of_le zero_lt_one ht
  have hB_pos : 0 < B :=
    Nat.cast_pos.mpr (Nat.succ_pos b)
  have hBsq_pos : 0 < Bsq :=
    mul_pos hB_pos hB_pos
  have hcoef_pos : 0 < A * Bsq⁻¹ :=
    mul_pos hA_pos (inv_pos.mpr hBsq_pos)
  have hx_le_curvature : x ≤ Bsq / A := by
    match lt_or_ge 0 x with
    | Or.inl hx_pos =>
        have hscaled_local :
            (A * Bsq⁻¹) * x < 1 := by
          exact hscaled
        have hscaled_comm :
            x * (A * Bsq⁻¹) < 1 :=
          Eq.subst
            (motive := fun r : ℝ => r < 1)
            (mul_comm (A * Bsq⁻¹) x)
            hscaled_local
        have hx_lt_recip :
            x < 1 / (A * Bsq⁻¹) :=
          (lt_div_iff₀ hcoef_pos).mpr hscaled_comm
        have hrecip_eq :
            1 / (A * Bsq⁻¹) = Bsq / A := by
          calc
            1 / (A * Bsq⁻¹) = (A * Bsq⁻¹)⁻¹ :=
              one_div (A * Bsq⁻¹)
            _ = (Bsq⁻¹)⁻¹ * A⁻¹ :=
              mul_inv_rev A Bsq⁻¹
            _ = Bsq * A⁻¹ :=
              congrArg (fun y : ℝ => y * A⁻¹) (inv_inv Bsq)
            _ = Bsq / A :=
              (div_eq_mul_inv Bsq A).symm
        exact
          le_of_lt
            (Eq.subst
              (motive := fun y : ℝ => x < y)
              hrecip_eq
              hx_lt_recip)
    | Or.inr hx_nonpos =>
        have hcurv_nonneg : 0 ≤ Bsq / A :=
          div_nonneg (le_of_lt hBsq_pos) (le_of_lt hA_pos)
        exact le_trans hx_nonpos hcurv_nonneg
  have hspan_eq :
      (((q + 1 : ℕ) : ℝ) - (p : ℝ)) = x + 1 := by
    have hq_succ :
        ((q + 1 : ℕ) : ℝ) = (q : ℝ) + 1 :=
      Nat.cast_add_one q
    calc
      (((q + 1 : ℕ) : ℝ) - (p : ℝ)) =
          ((q : ℝ) + 1) - (p : ℝ) :=
        congrArg (fun y : ℝ => y - (p : ℝ)) hq_succ
      _ = ((q : ℝ) + 1) + (-(p : ℝ)) :=
        sub_eq_add_neg ((q : ℝ) + 1) (p : ℝ)
      _ = (q : ℝ) + (1 + (-(p : ℝ))) :=
        add_assoc (q : ℝ) 1 (-(p : ℝ))
      _ = (q : ℝ) + ((-(p : ℝ)) + 1) :=
        congrArg (fun y : ℝ => (q : ℝ) + y) (add_comm 1 (-(p : ℝ)))
      _ = ((q : ℝ) + (-(p : ℝ))) + 1 :=
        (add_assoc (q : ℝ) (-(p : ℝ)) 1).symm
      _ = ((q : ℝ) - (p : ℝ)) + 1 :=
        congrArg (fun y : ℝ => y + 1)
          (sub_eq_add_neg (q : ℝ) (p : ℝ)).symm
      _ = x + 1 :=
        rfl
  have hsum_le :
      x + 1 ≤ Bsq / A + 1 :=
    add_le_add_right hx_le_curvature 1
  exact
    Eq.subst
      (motive := fun y : ℝ => y ≤ Bsq / A + 1)
      hspan_eq.symm
      hsum_le

/-- A nonempty logarithmic derivative packet is bounded by the reciprocal
curvature scale plus one. -/
theorem Complex.logarithmicPhaseRealPhase_nonempty_derivPacket_card_le_curvatureScale_add_one
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    {m : ℤ}
    (hp :
      (Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m).Nonempty)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ((Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m).card : ℝ) ≤
      ((((b + 1 : ℕ) : ℝ) * (((b + 1 : ℕ) : ℝ))) / ‖t‖ + 1) := by
  match
    Complex.logarithmicPhaseRealPhase_nonempty_derivPacket_endpoint_data_of_growth
      t ht hp ha hab hderiv_growth with
  | ⟨p, q, hp_mem, hq_mem, hp_interval, hq_interval, hp_le_q,
      hgrowth, hwindow, hendpoint_card⟩ =>
      have hscaled :
          ‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              ((q : ℝ) - (p : ℝ)) < 1 :=
        Complex.logarithmicPhaseRealPhase_nonempty_derivPacket_scaled_span_lt_one
          t ht hp_mem hq_mem hgrowth
      have hendpoint_bound :
          (((q + 1 : ℕ) : ℝ) - (p : ℝ)) ≤
            ((((b + 1 : ℕ) : ℝ) * (((b + 1 : ℕ) : ℝ))) / ‖t‖ + 1) :=
        Real.logarithmicPhaseRealPhase_span_le_curvatureScale_add_one
          ht hscaled
      exact le_trans hendpoint_card hendpoint_bound

/-- Packet-sum bound for one nonempty logarithmic derivative packet by the
reciprocal curvature scale plus one. -/
theorem Complex.logarithmicPhaseRealPhase_nonempty_packetSum_le_curvatureScale_add_one
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    {m : ℤ}
    (hp :
      (Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m).Nonempty)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖Complex.realPhase_secondDerivative_vdc_packetSum
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b m‖ ≤
      ((((b + 1 : ℕ) : ℝ) * (((b + 1 : ℕ) : ℝ))) / ‖t‖ + 1) := by
  exact le_trans
    (Complex.realPhase_secondDerivative_vdc_packetSum_norm_le_card
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b m)
    (Complex.logarithmicPhaseRealPhase_nonempty_derivPacket_card_le_curvatureScale_add_one
      t ht hp ha hab hderiv_growth)

/-- An active logarithmic derivative packet is nonempty. -/
theorem Complex.logarithmicPhaseRealPhase_activeDerivPacket_nonempty
    (t : ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈
        Complex.realPhase_secondDerivative_vdc_activeDerivPackets
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b) :
    (Complex.realPhase_secondDerivative_vdc_derivPacket
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b m).Nonempty := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  have hexists :
      ∃ n : ℕ,
        n ∈ Finset.Icc a b ∧
          Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ n = m :=
    Finset.mem_image.mp hm
  match hexists with
  | ⟨n, hn_block, hn_index⟩ =>
      have hn_packet :
          n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m :=
        (Complex.mem_realPhase_secondDerivative_vdc_derivPacket_iff_index_eq
          φ).mpr
          (And.intro hn_block hn_index)
      exact ⟨n, hn_packet⟩

/-- Uniform reciprocal-curvature-scale packet-sum bound over active
logarithmic derivative packets. -/
theorem Complex.logarithmicPhaseRealPhase_active_packetSum_le_curvatureScale_add_one
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈
        Complex.realPhase_secondDerivative_vdc_activeDerivPackets
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖Complex.realPhase_secondDerivative_vdc_packetSum
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b m‖ ≤
      ((((b + 1 : ℕ) : ℝ) * (((b + 1 : ℕ) : ℝ))) / ‖t‖ + 1) := by
  exact
    Complex.logarithmicPhaseRealPhase_nonempty_packetSum_le_curvatureScale_add_one
      t ht
      (Complex.logarithmicPhaseRealPhase_activeDerivPacket_nonempty t hm)
      ha hab hderiv_growth

/-- Assembly of logarithmic derivative-packet majorants into the original
block estimate. -/
theorem Complex.logarithmicPhaseRealPhase_packet_majorants_assemble
    (t : ℝ)
    {a b : ℕ}
    (majorant : ℤ → ℝ)
    (hmajorant_nonneg :
      ∀ m : ℤ,
        m ∈
          Complex.realPhase_secondDerivative_vdc_activeDerivPackets
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b →
          0 ≤ majorant m)
    (hpacket :
      ∀ m : ℤ,
        m ∈
          Complex.realPhase_secondDerivative_vdc_activeDerivPackets
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b →
          ‖Complex.realPhase_secondDerivative_vdc_packetSum
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m‖ ≤ majorant m)
    {target : ℝ}
    (hsum :
      (∑ m ∈
        Complex.realPhase_secondDerivative_vdc_activeDerivPackets
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b,
        majorant m) ≤ target) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      target := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  let packets : Finset ℤ :=
    Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b
  have hpacket_sum :
      ‖∑ m ∈ packets,
        Complex.realPhase_secondDerivative_vdc_packetSum φ a b m‖ ≤
        ∑ m ∈ packets, majorant m := by
    have htriangle :
        ‖∑ m ∈ packets,
          Complex.realPhase_secondDerivative_vdc_packetSum φ a b m‖ ≤
          ∑ m ∈ packets,
            ‖Complex.realPhase_secondDerivative_vdc_packetSum φ a b m‖ :=
      norm_sum_le
        packets
        (fun m : ℤ =>
          Complex.realPhase_secondDerivative_vdc_packetSum φ a b m)
    have hpoint :
        (∑ m ∈ packets,
          ‖Complex.realPhase_secondDerivative_vdc_packetSum φ a b m‖) ≤
          ∑ m ∈ packets, majorant m :=
      Finset.sum_le_sum
        (fun m hm => hpacket m hm)
    exact le_trans htriangle hpoint
  have hnorm_eq :
      ‖∑ m ∈ packets,
        Complex.realPhase_secondDerivative_vdc_packetSum φ a b m‖ =
      ‖∑ n ∈ Finset.Icc a b,
        Complex.exp (Complex.I * (φ n : ℂ))‖ :=
    Complex.realPhase_secondDerivative_vdc_activePacketSums_norm_eq_block_norm
      φ a b
  exact
    Eq.subst
      (motive := fun left : ℝ => left ≤ target)
      hnorm_eq
      (le_trans hpacket_sum hsum)

/-- Active derivative-frequency membership is witnessed by an actual integer
sample in the original block. -/
theorem Complex.logarithmicPhaseRealPhase_activeDerivPacket_witness
    (t : ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈
        Complex.realPhase_secondDerivative_vdc_activeDerivPackets
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b) :
    ∃ n : ℕ,
      n ∈ Finset.Icc a b ∧
        Complex.realPhase_secondDerivative_vdc_derivPacketIndex
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          n = m := by
  exact Finset.mem_image.mp hm

/-- The witnessing sample for an active logarithmic derivative packet lies in
the parent real interval. -/
theorem Complex.logarithmicPhaseRealPhase_activeDerivPacket_witness_mem_Icc
    {a b n : ℕ}
    (hn : n ∈ Finset.Icc a b) :
    (n : ℝ) ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) := by
  have hn_bounds : a ≤ n ∧ n ≤ b :=
    Finset.mem_Icc.mp hn
  exact And.intro
    (Nat.cast_le.mpr hn_bounds.1)
    (Nat.cast_le.mpr
      (Nat.le_trans hn_bounds.2 (Nat.le_succ b)))

/-- The floor packet index is below the derivative value plus half a unit. -/
theorem Complex.realPhase_secondDerivative_vdc_derivPacketIndex_cast_le
    (φ : ℝ → ℝ)
    (n : ℕ) :
    ((Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ n : ℤ) : ℝ) ≤
      deriv φ n + (1 / 2 : ℝ) := by
  exact Int.floor_le (deriv φ n + (1 / 2 : ℝ))

/-- The derivative value minus half a unit is below the floor packet index. -/
theorem Complex.realPhase_secondDerivative_vdc_deriv_sub_half_le_index_cast
    (φ : ℝ → ℝ)
    (n : ℕ) :
    deriv φ n - (1 / 2 : ℝ) ≤
      ((Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ n : ℤ) : ℝ) := by
  have hfloor :
      deriv φ n + (1 / 2 : ℝ) <
        ((Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ n : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one (deriv φ n + (1 / 2 : ℝ))
  have hsub_lt :
      deriv φ n + (1 / 2 : ℝ) - 1 <
        ((Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ n : ℤ) : ℝ) :=
    (sub_lt_iff_lt_add).mpr hfloor
  have hleft :
      deriv φ n + (1 / 2 : ℝ) - 1 =
        deriv φ n - (1 / 2 : ℝ) := by
    have hhalf_sub_one :
        (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) :=
      half_sub (1 : ℝ)
    calc
      deriv φ n + (1 / 2 : ℝ) - 1 =
          deriv φ n + ((1 / 2 : ℝ) - 1) :=
        add_sub_assoc (deriv φ n) (1 / 2 : ℝ) 1
      _ = deriv φ n + (-(1 / 2 : ℝ)) := by
        exact congrArg (fun r : ℝ => deriv φ n + r) hhalf_sub_one
      _ = deriv φ n - (1 / 2 : ℝ) :=
        (sub_eq_add_neg (deriv φ n) (1 / 2 : ℝ)).symm
  exact le_of_lt
    (Eq.subst
      (motive := fun r : ℝ =>
        r <
          ((Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ n : ℤ) : ℝ))
      hleft
      hsub_lt)

/-- Active logarithmic packet indices are bounded above by the right endpoint
derivative, with the unavoidable half-window slack. -/
theorem Complex.logarithmicPhaseRealPhase_activeDerivPacket_index_upper
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    {m : ℤ}
    (hm :
      m ∈
        Complex.realPhase_secondDerivative_vdc_activeDerivPackets
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b) :
    (m : ℝ) ≤
      -(‖t‖ / (((b + 1 : ℕ) : ℝ))) + (1 / 2 : ℝ) := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  match
    Complex.logarithmicPhaseRealPhase_activeDerivPacket_witness t hm with
  | ⟨n, hn_block, hn_index⟩ =>
      have hn_Icc :
          (n : ℝ) ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) :=
        Complex.logarithmicPhaseRealPhase_activeDerivPacket_witness_mem_Icc
          hn_block
      have hneg_lower :
          ‖t‖ / (((b + 1 : ℕ) : ℝ)) ≤ -deriv φ n :=
        Complex.logarithmicPhaseRealPhase_neg_deriv_lower_on_integer_block
          t ht_nonneg ha hn_Icc
      have hderiv_upper :
          deriv φ n ≤ -(‖t‖ / (((b + 1 : ℕ) : ℝ))) := by
        have hneg :
            -(-deriv φ n) ≤ -(‖t‖ / (((b + 1 : ℕ) : ℝ))) :=
          neg_le_neg hneg_lower
        exact
          Eq.subst
            (motive := fun left : ℝ =>
              left ≤ -(‖t‖ / (((b + 1 : ℕ) : ℝ))))
            (neg_neg (deriv φ n))
            hneg
      have hindex_le :
          ((Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ n : ℤ) : ℝ) ≤
            deriv φ n + (1 / 2 : ℝ) :=
        Complex.realPhase_secondDerivative_vdc_derivPacketIndex_cast_le φ n
      have hderiv_half :
          deriv φ n + (1 / 2 : ℝ) ≤
            -(‖t‖ / (((b + 1 : ℕ) : ℝ))) + (1 / 2 : ℝ) :=
        add_le_add_right hderiv_upper (1 / 2 : ℝ)
      exact
        Eq.subst
          (motive := fun k : ℤ =>
            (k : ℝ) ≤
              -(‖t‖ / (((b + 1 : ℕ) : ℝ))) + (1 / 2 : ℝ))
          hn_index
          (le_trans hindex_le hderiv_half)

/-- Active logarithmic packet indices are bounded below by the left endpoint
derivative, with the unavoidable half-window slack. -/
theorem Complex.logarithmicPhaseRealPhase_activeDerivPacket_index_lower
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    {m : ℤ}
    (hm :
      m ∈
        Complex.realPhase_secondDerivative_vdc_activeDerivPackets
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b) :
    -(‖t‖ / (a : ℝ)) - (1 / 2 : ℝ) ≤ (m : ℝ) := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  match
    Complex.logarithmicPhaseRealPhase_activeDerivPacket_witness t hm with
  | ⟨n, hn_block, hn_index⟩ =>
      have hn_Icc :
          (n : ℝ) ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) :=
        Complex.logarithmicPhaseRealPhase_activeDerivPacket_witness_mem_Icc
          hn_block
      have hneg_upper :
          -deriv φ n ≤ ‖t‖ / (a : ℝ) :=
        Complex.logarithmicPhaseRealPhase_neg_deriv_upper_on_integer_block
          t ht_nonneg ha hn_Icc
      have hderiv_lower :
          -(‖t‖ / (a : ℝ)) ≤ deriv φ n := by
        exact neg_le.mp hneg_upper
      have hderiv_sub :
          -(‖t‖ / (a : ℝ)) - (1 / 2 : ℝ) ≤
            deriv φ n - (1 / 2 : ℝ) :=
        sub_le_sub_right hderiv_lower (1 / 2 : ℝ)
      have hsub_le_index :
          deriv φ n - (1 / 2 : ℝ) ≤
            ((Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ n : ℤ) : ℝ) :=
        Complex.realPhase_secondDerivative_vdc_deriv_sub_half_le_index_cast φ n
      exact
        Eq.subst
          (motive := fun k : ℤ =>
            -(‖t‖ / (a : ℝ)) - (1 / 2 : ℝ) ≤ (k : ℝ))
          hn_index
          (le_trans hderiv_sub hsub_le_index)

/-- Stationary point for the logarithmic phase frequency equation
`φ'(x) = m`, in the negative-frequency branch. -/
def Complex.logarithmicPhaseRealPhase_stationaryPoint
    (t : ℝ)
    (m : ℤ) : ℝ :=
  ‖t‖ / (-(m : ℝ))

/-- Negative integer frequencies have positive denominator in the stationary
point formula. -/
theorem Int.neg_cast_pos_of_lt_zero
    {m : ℤ}
    (hm : m < 0) :
    0 < -(m : ℝ) := by
  have hcast_neg : (m : ℝ) < 0 :=
    show (m : ℝ) < ((0 : ℤ) : ℝ)
    exact Int.cast_lt.mpr hm
  exact neg_pos.mpr hcast_neg

/-- For nonzero logarithmic frequency and negative packet index, the
stationary point is positive. -/
theorem Complex.logarithmicPhaseRealPhase_stationaryPoint_pos
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {m : ℤ}
    (hm : m < 0) :
    0 < Complex.logarithmicPhaseRealPhase_stationaryPoint t m := by
  have ht_pos : 0 < ‖t‖ :=
    lt_of_lt_of_le zero_lt_one ht
  have hden_pos : 0 < -(m : ℝ) :=
    Int.neg_cast_pos_of_lt_zero hm
  show 0 < ‖t‖ / (-(m : ℝ))
  exact div_pos ht_pos hden_pos

/-- The stationary point solves the reciprocal derivative equation. -/
theorem Real.logarithmicPhase_stationaryPoint_reciprocal_identity
    {T μ : ℝ}
    (hT : 0 < T)
    (hμ : 0 < μ) :
    T / (T / μ) = μ := by
  have hT_ne : T ≠ 0 :=
    ne_of_gt hT
  have hμ_ne : μ ≠ 0 :=
    ne_of_gt hμ
  calc
    T / (T / μ) = T * (T / μ)⁻¹ :=
      div_eq_mul_inv T (T / μ)
    _ = T * (T * μ⁻¹)⁻¹ := by
      exact congrArg (fun r : ℝ => T * r⁻¹) (div_eq_mul_inv T μ)
    _ = T * ((μ⁻¹)⁻¹ * T⁻¹) := by
      exact congrArg (fun r : ℝ => T * r) (mul_inv_rev T μ⁻¹)
    _ = T * (μ * T⁻¹) := by
      exact congrArg
        (fun r : ℝ => T * (r * T⁻¹))
        (inv_inv μ)
    _ = μ * (T * T⁻¹) := by
      calc
        T * (μ * T⁻¹) = (T * μ) * T⁻¹ :=
          (mul_assoc T μ T⁻¹).symm
        _ = (μ * T) * T⁻¹ := by
          exact congrArg (fun r : ℝ => r * T⁻¹) (mul_comm T μ)
        _ = μ * (T * T⁻¹) :=
          mul_assoc μ T T⁻¹
    _ = μ * 1 := by
      exact congrArg (fun r : ℝ => μ * r) (mul_inv_cancel₀ hT_ne)
    _ = μ :=
      mul_one μ

/-- At a negative integer frequency, the logarithmic stationary point has
derivative exactly equal to that frequency. -/
theorem Complex.logarithmicPhaseRealPhase_deriv_stationaryPoint_eq
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {m : ℤ}
    (hm : m < 0) :
    deriv
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      (Complex.logarithmicPhaseRealPhase_stationaryPoint t m) =
      (m : ℝ) := by
  let x : ℝ := Complex.logarithmicPhaseRealPhase_stationaryPoint t m
  have hx_pos : 0 < x :=
    Complex.logarithmicPhaseRealPhase_stationaryPoint_pos t ht hm
  have hderiv :
      deriv
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x =
        -‖t‖ / x :=
    Complex.logarithmicPhaseRealPhase_deriv_eq_neg_norm_div
      t ht_nonneg hx_pos
  have hT_pos : 0 < ‖t‖ :=
    lt_of_lt_of_le zero_lt_one ht
  have hden_pos : 0 < -(m : ℝ) :=
    Int.neg_cast_pos_of_lt_zero hm
  have hrecip :
      ‖t‖ / x = -(m : ℝ) := by
    show ‖t‖ / (‖t‖ / (-(m : ℝ))) = -(m : ℝ)
    exact
      Real.logarithmicPhase_stationaryPoint_reciprocal_identity
        hT_pos hden_pos
  have hneg :
      -(‖t‖ / x) = (m : ℝ) := by
    calc
      -(‖t‖ / x) = -(-(m : ℝ)) := by
        exact congrArg Neg.neg hrecip
      _ = (m : ℝ) :=
        neg_neg (m : ℝ)
  have hneg_div :
      -‖t‖ / x = -(‖t‖ / x) :=
    neg_div ‖t‖ x
  exact Eq.trans hderiv (Eq.trans hneg_div hneg)

/-- Active logarithmic derivative-packet frequencies whose stationary point
lies in the ambient real interval. -/
def Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets
    (t : ℝ)
    (a b : ℕ) : Finset ℤ :=
  (Complex.realPhase_secondDerivative_vdc_activeDerivPackets
    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
    a b).filter
    (fun m : ℤ =>
      (m < 0) ∧
        Complex.logarithmicPhaseRealPhase_stationaryPoint t m ∈
          Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ))

/-- Active logarithmic derivative-packet frequencies whose stationary point is
outside the ambient interval.  These are the endpoint tails in the B-process
decomposition. -/
def Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets
    (t : ℝ)
    (a b : ℕ) : Finset ℤ :=
  (Complex.realPhase_secondDerivative_vdc_activeDerivPackets
    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
    a b).filter
    (fun m : ℤ =>
      ¬ ((m < 0) ∧
          Complex.logarithmicPhaseRealPhase_stationaryPoint t m ∈
            Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)))

/-- Endpoint packets with nonnegative packet index form the right endpoint
tail. -/
def Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets
    (t : ℝ)
    (a b : ℕ) : Finset ℤ :=
  (Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b).filter
    (fun m : ℤ => 0 ≤ m)

/-- Endpoint packets with negative packet index and stationary point left of
the block form the left endpoint tail. -/
def Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets
    (t : ℝ)
    (a b : ℕ) : Finset ℤ :=
  (Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b).filter
    (fun m : ℤ =>
      m < 0 ∧
        Complex.logarithmicPhaseRealPhase_stationaryPoint t m < (a : ℝ))

/-- Endpoint packets with negative packet index and stationary point to the
right of the block form the far-right endpoint tail. -/
def Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets
    (t : ℝ)
    (a b : ℕ) : Finset ℤ :=
  (Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b).filter
    (fun m : ℤ =>
      m < 0 ∧
        ((b + 1 : ℕ) : ℝ) <
          Complex.logarithmicPhaseRealPhase_stationaryPoint t m)

/-- The stationary and endpoint packet sets partition the active logarithmic
derivative frequencies. -/
theorem Complex.logarithmicPhaseRealPhase_activeDerivPackets_eq_stationary_union_endpoint
    (t : ℝ)
    (a b : ℕ) :
    Complex.realPhase_secondDerivative_vdc_activeDerivPackets
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b =
      Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b ∪
        Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b := by
  exact Finset.ext
    (fun m =>
      Iff.intro
        (fun hm =>
          match Classical.em
              ((m < 0) ∧
                Complex.logarithmicPhaseRealPhase_stationaryPoint t m ∈
                  Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) with
          | Or.inl hstat =>
              Finset.mem_union.mpr
                (Or.inl
                  (Finset.mem_filter.mpr
                    (And.intro hm hstat)))
          | Or.inr hnot =>
              Finset.mem_union.mpr
                (Or.inr
                  (Finset.mem_filter.mpr
                    (And.intro hm hnot))))
        (fun hm =>
          match Finset.mem_union.mp hm with
          | Or.inl hleft =>
              (Finset.mem_filter.mp hleft).1
          | Or.inr hright =>
              (Finset.mem_filter.mp hright).1))

/-- The stationary and endpoint packet sets are disjoint. -/
theorem Complex.logarithmicPhaseRealPhase_stationary_endpoint_disjoint
    (t : ℝ)
    (a b : ℕ) :
    Disjoint
      (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b)
      (Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b) := by
  exact Finset.disjoint_left.mpr
    (fun m hm_stat hm_end =>
      have hstat :
          (m < 0) ∧
            Complex.logarithmicPhaseRealPhase_stationaryPoint t m ∈
              Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) :=
        (Finset.mem_filter.mp hm_stat).2
      have hnot :
          ¬ ((m < 0) ∧
              Complex.logarithmicPhaseRealPhase_stationaryPoint t m ∈
                Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) :=
        (Finset.mem_filter.mp hm_end).2
      hnot hstat)

/-- A stationary filtered packet is active. -/
theorem Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets_mem_active
    (t : ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b) :
    m ∈
      Complex.realPhase_secondDerivative_vdc_activeDerivPackets
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b :=
  (Finset.mem_filter.mp hm).1

/-- A stationary filtered packet has a negative derivative frequency. -/
theorem Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets_index_neg
    (t : ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b) :
    m < 0 :=
  ((Finset.mem_filter.mp hm).2).1

/-- A stationary filtered packet has its explicit stationary point in the
ambient block interval. -/
theorem Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets_point_mem_Icc
    (t : ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b) :
    Complex.logarithmicPhaseRealPhase_stationaryPoint t m ∈
      Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) :=
  ((Finset.mem_filter.mp hm).2).2

/-- A stationary active frequency is bounded below by the reciprocal image of
the left endpoint. -/
theorem Complex.logarithmicPhaseRealPhase_stationaryActive_index_lower
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b) :
    -(‖t‖ / (a : ℝ)) ≤ (m : ℝ) := by
  have hm_neg :
      m < 0 :=
    Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets_index_neg
      t hm
  have hpoint :
      Complex.logarithmicPhaseRealPhase_stationaryPoint t m ∈
        Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) :=
    Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets_point_mem_Icc
      t hm
  have hden_pos : 0 < -(m : ℝ) :=
    Int.neg_cast_pos_of_lt_zero hm_neg
  have ha_pos : 0 < (a : ℝ) :=
    Nat.cast_pos.mpr (Nat.lt_of_succ_le ha)
  have ha_le_div :
      (a : ℝ) ≤ ‖t‖ / (-(m : ℝ)) := by
    exact hpoint.1
  have hprod_le :
      (a : ℝ) * (-(m : ℝ)) ≤ ‖t‖ :=
    (le_div_iff₀ hden_pos).mp ha_le_div
  have hneg_le :
      -(m : ℝ) ≤ ‖t‖ / (a : ℝ) :=
    (le_div_iff₀ ha_pos).mpr
      (Eq.subst
        (motive := fun left : ℝ => left ≤ ‖t‖)
        (mul_comm (a : ℝ) (-(m : ℝ)))
        hprod_le)
  have hflip :
      -(‖t‖ / (a : ℝ)) ≤ - (-(m : ℝ)) :=
    neg_le_neg hneg_le
  exact
    Eq.subst
      (motive := fun right : ℝ => -(‖t‖ / (a : ℝ)) ≤ right)
      (neg_neg (m : ℝ))
      hflip

/-- A stationary active frequency is bounded above by the reciprocal image of
the successor-right endpoint. -/
theorem Complex.logarithmicPhaseRealPhase_stationaryActive_index_upper
    (t : ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b) :
    (m : ℝ) ≤ -(‖t‖ / (((b + 1 : ℕ) : ℝ))) := by
  have hm_neg :
      m < 0 :=
    Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets_index_neg
      t hm
  have hpoint :
      Complex.logarithmicPhaseRealPhase_stationaryPoint t m ∈
        Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) :=
    Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets_point_mem_Icc
      t hm
  have hden_pos : 0 < -(m : ℝ) :=
    Int.neg_cast_pos_of_lt_zero hm_neg
  have hB_pos : 0 < (((b + 1 : ℕ) : ℝ)) :=
    Nat.cast_pos.mpr (Nat.succ_pos b)
  have hdiv_le :
      ‖t‖ / (-(m : ℝ)) ≤ (((b + 1 : ℕ) : ℝ)) := by
    exact hpoint.2
  have hT_le_prod :
      ‖t‖ ≤ (((b + 1 : ℕ) : ℝ)) * (-(m : ℝ)) :=
    (div_le_iff₀ hden_pos).mp hdiv_le
  have hscale_le :
      ‖t‖ / (((b + 1 : ℕ) : ℝ)) ≤ -(m : ℝ) :=
    (div_le_iff₀ hB_pos).mpr
      (Eq.subst
        (motive := fun right : ℝ => ‖t‖ ≤ right)
        (mul_comm (((b + 1 : ℕ) : ℝ)) (-(m : ℝ)))
        hT_le_prod)
  have hflip :
      - (-(m : ℝ)) ≤ -(‖t‖ / (((b + 1 : ℕ) : ℝ))) :=
    neg_le_neg hscale_le
  exact
    Eq.subst
      (motive := fun left : ℝ =>
        left ≤ -(‖t‖ / (((b + 1 : ℕ) : ℝ))))
      (neg_neg (m : ℝ))
      hflip

/-- Stationary active frequencies lie in the reciprocal image interval of the
ambient block. -/
theorem Complex.logarithmicPhaseRealPhase_stationaryActive_mem_reciprocalImageInterval
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b) :
    (m : ℝ) ∈
      Set.Icc
        (-(‖t‖ / (a : ℝ)))
        (-(‖t‖ / (((b + 1 : ℕ) : ℝ)))) :=
  And.intro
    (Complex.logarithmicPhaseRealPhase_stationaryActive_index_lower
      t ht ha hm)
    (Complex.logarithmicPhaseRealPhase_stationaryActive_index_upper
      t hm)

/-- Sample union attached to an arbitrary derivative-frequency packet family. -/
def Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (packets : Finset ℤ) : Finset ℕ :=
  packets.biUnion
    (fun m : ℤ => Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m)

/-- A subfamily of active derivative packets inherits pairwise disjointness. -/
theorem Complex.realPhase_secondDerivative_vdc_packetFamily_pairwiseDisjoint
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {packets : Finset ℤ}
    (hpackets :
      packets ⊆ Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b) :
    ∀ m₁ ∈ packets,
      ∀ m₂ ∈ packets,
        m₁ ≠ m₂ →
          Disjoint
            (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m₁)
            (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m₂) := by
  intro m₁ hm₁ m₂ hm₂ hne
  exact
    Complex.realPhase_secondDerivative_vdc_activeDerivPackets_pairwiseDisjoint
      φ a b m₁ (hpackets hm₁) m₂ (hpackets hm₂) hne

/-- The sum over a packet family expands exactly as the sample sum over its
sample union. -/
theorem Complex.realPhase_secondDerivative_vdc_packetFamilyUnion_sum_eq_packetSums
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {packets : Finset ℤ}
    (hpackets :
      packets ⊆ Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b) :
    (∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion φ a b packets,
      Complex.exp (Complex.I * (φ n : ℂ))) =
    ∑ m ∈ packets,
      Complex.realPhase_secondDerivative_vdc_packetSum φ a b m := by
  exact
    Finset.sum_biUnion
      (Complex.realPhase_secondDerivative_vdc_packetFamily_pairwiseDisjoint
        φ hpackets)

/-- Upward closure of the zero derivative-frequency packet inside the block. -/
theorem Complex.logarithmicPhaseRealPhase_zeroDerivPacket_upwardClosed
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b n k : ℕ}
    (ha : 1 ≤ a)
    (hn :
      n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b 0)
    (hk_block : k ∈ Finset.Icc a b)
    (hnk : n ≤ k) :
    k ∈ Complex.realPhase_secondDerivative_vdc_derivPacket
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b 0 := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  have hn_block : n ∈ Finset.Icc a b :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block φ hn
  have hn_one : 1 ≤ n :=
    le_trans ha (Finset.mem_Icc.mp hn_block).1
  have hk_one : 1 ≤ k :=
    le_trans ha (Finset.mem_Icc.mp hk_block).1
  have hn_pos_nat : 0 < n :=
    Nat.lt_of_succ_le hn_one
  have hk_pos_nat : 0 < k :=
    Nat.lt_of_succ_le hk_one
  have hn_pos : 0 < (n : ℝ) :=
    Nat.cast_pos.mpr hn_pos_nat
  have hk_pos : 0 < (k : ℝ) :=
    Nat.cast_pos.mpr hk_pos_nat
  have hT_nonneg : 0 ≤ ‖t‖ :=
    norm_nonneg t
  have hwindow_lower_n :
      ((0 : ℤ) : ℝ) - (1 / 2 : ℝ) ≤ deriv φ n :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_lower φ hn
  have hzero_left :
      ((0 : ℤ) : ℝ) - (1 / 2 : ℝ) = -(1 / 2 : ℝ) := by
    calc
      ((0 : ℤ) : ℝ) - (1 / 2 : ℝ) =
          (0 : ℝ) - (1 / 2 : ℝ) := by
        exact congrArg (fun r : ℝ => r - (1 / 2 : ℝ)) Int.cast_zero
      _ = -(1 / 2 : ℝ) :=
        zero_sub (1 / 2 : ℝ)
  have hderiv_n :
      deriv φ n = -(‖t‖ / (n : ℝ)) :=
    Complex.logarithmicPhaseRealPhase_deriv_eq_neg_norm_div_parenthesized
      t ht_nonneg hn_pos
  have hneg_bound_n :
      -(1 / 2 : ℝ) ≤ -(‖t‖ / (n : ℝ)) :=
    Eq.subst
      (motive := fun right : ℝ => -(1 / 2 : ℝ) ≤ right)
      hderiv_n
      (Eq.subst
        (motive := fun left : ℝ => left ≤ deriv φ n)
        hzero_left
        hwindow_lower_n)
  have hscale_n :
      ‖t‖ / (n : ℝ) ≤ (1 / 2 : ℝ) := by
    have hflip :
        - (-(‖t‖ / (n : ℝ))) ≤ - (-(1 / 2 : ℝ)) :=
      neg_le_neg hneg_bound_n
    exact
      Eq.subst
        (motive := fun left : ℝ => left ≤ (1 / 2 : ℝ))
        (neg_neg (‖t‖ / (n : ℝ)))
        (Eq.subst
          (motive := fun right : ℝ =>
            - (-(‖t‖ / (n : ℝ))) ≤ right)
          (neg_neg (1 / 2 : ℝ))
          hflip)
  have hrecip_kn : (k : ℝ)⁻¹ ≤ (n : ℝ)⁻¹ :=
    inv_anti₀ hn_pos (Nat.cast_le.mpr hnk)
  have hscale_kn :
      ‖t‖ / (k : ℝ) ≤ ‖t‖ / (n : ℝ) := by
    have hmul :
        ‖t‖ * (k : ℝ)⁻¹ ≤ ‖t‖ * (n : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left hrecip_kn hT_nonneg
    exact
      Eq.subst
        (motive := fun left : ℝ => left ≤ ‖t‖ / (n : ℝ))
        (div_eq_mul_inv ‖t‖ (k : ℝ)).symm
        (Eq.subst
          (motive := fun right : ℝ => ‖t‖ * (k : ℝ)⁻¹ ≤ right)
          (div_eq_mul_inv ‖t‖ (n : ℝ)).symm
          hmul)
  have hscale_k :
      ‖t‖ / (k : ℝ) ≤ (1 / 2 : ℝ) :=
    le_trans hscale_kn hscale_n
  have hderiv_k :
      deriv φ k = -(‖t‖ / (k : ℝ)) :=
    Complex.logarithmicPhaseRealPhase_deriv_eq_neg_norm_div_parenthesized
      t ht_nonneg hk_pos
  have hlower_k_raw :
      -(1 / 2 : ℝ) ≤ -(‖t‖ / (k : ℝ)) := by
    have hflip :
        - (1 / 2 : ℝ) ≤ - (‖t‖ / (k : ℝ)) :=
      neg_le_neg hscale_k
    exact hflip
  have hlower_k :
      ((0 : ℤ) : ℝ) - (1 / 2 : ℝ) ≤ deriv φ k :=
    Eq.subst
      (motive := fun right : ℝ =>
        ((0 : ℤ) : ℝ) - (1 / 2 : ℝ) ≤ right)
      hderiv_k
      (Eq.subst
        (motive := fun left : ℝ => left ≤ -(‖t‖ / (k : ℝ)))
        hzero_left.symm
        hlower_k_raw)
  have hscale_k_nonneg :
      0 ≤ ‖t‖ / (k : ℝ) :=
    div_nonneg hT_nonneg (le_of_lt hk_pos)
  have hderiv_k_nonpos :
      deriv φ k ≤ 0 :=
    Eq.subst
      (motive := fun left : ℝ => left ≤ 0)
      hderiv_k.symm
      (neg_nonpos.mpr hscale_k_nonneg)
  have hhalf_pos : (0 : ℝ) < (1 / 2 : ℝ) :=
    half_pos zero_lt_one
  have hzero_lt_upper :
      (0 : ℝ) < ((0 : ℤ) : ℝ) + (1 / 2 : ℝ) := by
    have hupper_eq :
        ((0 : ℤ) : ℝ) + (1 / 2 : ℝ) = (1 / 2 : ℝ) := by
      calc
        ((0 : ℤ) : ℝ) + (1 / 2 : ℝ) =
            (0 : ℝ) + (1 / 2 : ℝ) := by
          exact congrArg (fun r : ℝ => r + (1 / 2 : ℝ)) Int.cast_zero
        _ = (1 / 2 : ℝ) :=
          zero_add (1 / 2 : ℝ)
    exact
      Eq.subst
        (motive := fun right : ℝ => (0 : ℝ) < right)
        hupper_eq.symm
        hhalf_pos
  have hupper_k :
      deriv φ k < ((0 : ℤ) : ℝ) + (1 / 2 : ℝ) :=
    lt_of_le_of_lt hderiv_k_nonpos hzero_lt_upper
  exact
    (Complex.mem_realPhase_secondDerivative_vdc_derivPacket_iff φ).mpr
      (And.intro hk_block (And.intro hlower_k hupper_k))

/-- A nonempty zero derivative-frequency packet reaches the right endpoint of the
ambient block. -/
theorem Complex.logarithmicPhaseRealPhase_zeroDerivPacket_nonempty_rightEndpoint
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hp :
      (Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b 0).Nonempty) :
    b ∈ Complex.realPhase_secondDerivative_vdc_derivPacket
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b 0 := by
  match hp with
  | ⟨n, hn⟩ =>
      have hn_block : n ∈ Finset.Icc a b :=
        Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          hn
      have hn_bounds : a ≤ n ∧ n ≤ b :=
        Finset.mem_Icc.mp hn_block
      have hb_block : b ∈ Finset.Icc a b :=
        Finset.mem_Icc.mpr (And.intro (le_trans hn_bounds.1 hn_bounds.2) le_rfl)
      exact
        Complex.logarithmicPhaseRealPhase_zeroDerivPacket_upwardClosed
          t ht ht_nonneg ha hn hb_block hn_bounds.2

/-- A nonempty upward-closed zero packet is exactly the interval from its least
sample to the right endpoint. -/
theorem Complex.logarithmicPhaseRealPhase_zeroDerivPacket_nonempty_eq_min_Icc
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hp :
      (Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b 0).Nonempty) :
    Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b 0 =
      Finset.Icc
        ((Complex.realPhase_secondDerivative_vdc_derivPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b 0).min' hp)
        b := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  let packet : Finset ℕ :=
    Complex.realPhase_secondDerivative_vdc_derivPacket φ a b 0
  let c : ℕ := packet.min' hp
  have hc_mem : c ∈ packet :=
    Finset.min'_mem packet hp
  have hc_block : c ∈ Finset.Icc a b :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block φ hc_mem
  have hc_bounds : a ≤ c ∧ c ≤ b :=
    Finset.mem_Icc.mp hc_block
  exact Finset.ext
    (fun n =>
      Iff.intro
        (fun hn =>
          have hn_min : c ≤ n :=
            Finset.min'_le packet n hn
          have hn_block : n ∈ Finset.Icc a b :=
            Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block φ hn
          have hn_bounds : a ≤ n ∧ n ≤ b :=
            Finset.mem_Icc.mp hn_block
          Finset.mem_Icc.mpr (And.intro hn_min hn_bounds.2))
        (fun hn_interval =>
          have hn_bounds : c ≤ n ∧ n ≤ b :=
            Finset.mem_Icc.mp hn_interval
          have hn_block : n ∈ Finset.Icc a b :=
            Finset.mem_Icc.mpr
              (And.intro (le_trans hc_bounds.1 hn_bounds.1) hn_bounds.2)
          Complex.logarithmicPhaseRealPhase_zeroDerivPacket_upwardClosed
            t ht ht_nonneg ha hc_mem hn_block hn_bounds.1))

/-- The zero derivative-frequency packet is a genuine terminal endpoint interval.

This is the exact reconstruction needed before the endpoint Abel estimate can be
applied: no norm comparison with a larger set is used. -/
theorem Complex.logarithmicPhaseRealPhase_zeroDerivPacket_eq_terminalInterval
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    ∃ c : ℕ,
      a ≤ c ∧ c ≤ b + 1 ∧
      Complex.realPhase_secondDerivative_vdc_derivPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b 0 =
        Finset.Icc c b := by
  let packet : Finset ℕ :=
    Complex.realPhase_secondDerivative_vdc_derivPacket
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b 0
  match packet.eq_empty_or_nonempty with
  | Or.inl hempty =>
      have hinterval_empty : Finset.Icc (b + 1) b = (∅ : Finset ℕ) :=
        Finset.eq_empty_iff_forall_not_mem.mpr
          (fun n hn =>
            have hn_bounds : b + 1 ≤ n ∧ n ≤ b :=
              Finset.mem_Icc.mp hn
            have hb_lt_n : b < n :=
              Nat.lt_of_succ_le hn_bounds.1
            have hnot : ¬ n ≤ b :=
              not_le_of_gt hb_lt_n
            hnot hn_bounds.2)
      have hpacket_empty :
          Complex.realPhase_secondDerivative_vdc_derivPacket
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              a b 0 =
            ∅ := by
        exact hempty
      exact Exists.intro (b + 1)
        (And.intro
          (Nat.le_trans hab (Nat.le_succ b))
          (And.intro le_rfl
            (Eq.trans hpacket_empty hinterval_empty.symm)))
  | Or.inr hp =>
      let c : ℕ := packet.min' hp
      have hc_mem :
          c ∈ Complex.realPhase_secondDerivative_vdc_derivPacket
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b 0 := by
        exact Finset.min'_mem packet hp
      have hc_block : c ∈ Finset.Icc a b :=
        Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          hc_mem
      have hc_bounds : a ≤ c ∧ c ≤ b :=
        Finset.mem_Icc.mp hc_block
      have hpacket :
          Complex.realPhase_secondDerivative_vdc_derivPacket
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              a b 0 =
            Finset.Icc c b := by
        exact
          Complex.logarithmicPhaseRealPhase_zeroDerivPacket_nonempty_eq_min_Icc
            t ht ht_nonneg ha hp
      exact Exists.intro c
        (And.intro hc_bounds.1
          (And.intro (Nat.le_trans hc_bounds.2 (Nat.le_succ b)) hpacket))

/-- A finite subset of an integer block that is downward closed is an initial
interval.  This is the finite-order owner lemma used by the left endpoint
packet reconstruction; all analytic input is isolated in the downward-closure
hypothesis. -/
theorem Finset.exists_eq_Ico_of_subset_Icc_downwardClosed
    {S : Finset ℕ}
    {a b : ℕ}
    (hS_block : S ⊆ Finset.Icc a b)
    (hdown :
      ∀ n k : ℕ,
        n ∈ S →
        k ∈ Finset.Icc a b →
        k ≤ n →
          k ∈ S) :
    ∃ c : ℕ, a ≤ c ∧ c ≤ b + 1 ∧ S = Finset.Ico a c := by
  match S.eq_empty_or_nonempty with
  | Or.inl hS_empty =>
      have hIco_empty : Finset.Ico a a = (∅ : Finset ℕ) :=
        Finset.eq_empty_iff_forall_not_mem.mpr
          (fun n hn =>
            have hn_bounds : a ≤ n ∧ n < a :=
              Finset.mem_Ico.mp hn
            not_lt_of_ge hn_bounds.1 hn_bounds.2)
      exact Exists.intro a
        (And.intro le_rfl
          (And.intro (Nat.le_trans hab (Nat.le_succ b))
            (Eq.trans hS_empty hIco_empty.symm)))
  | Or.inr hS_nonempty =>
      let m : ℕ := S.max' hS_nonempty
      let c : ℕ := m + 1
      have hm_mem : m ∈ S :=
        Finset.max'_mem S hS_nonempty
      have hm_block : m ∈ Finset.Icc a b :=
        hS_block hm_mem
      have hm_bounds : a ≤ m ∧ m ≤ b :=
        Finset.mem_Icc.mp hm_block
      have hc_left : a ≤ c :=
        Nat.le_trans hm_bounds.1 (Nat.le_succ m)
      have hc_right : c ≤ b + 1 :=
        Nat.succ_le_succ hm_bounds.2
      have hS_eq : S = Finset.Ico a c :=
        Finset.ext
          (fun n =>
            Iff.intro
              (fun hn =>
                have hn_block : n ∈ Finset.Icc a b :=
                  hS_block hn
                have hn_bounds : a ≤ n ∧ n ≤ b :=
                  Finset.mem_Icc.mp hn_block
                have hn_le_m : n ≤ m :=
                  Finset.le_max' S n hn
                have hn_lt_c : n < c :=
                  Nat.lt_succ_of_le hn_le_m
                Finset.mem_Ico.mpr (And.intro hn_bounds.1 hn_lt_c))
              (fun hn_interval =>
                have hn_bounds : a ≤ n ∧ n < c :=
                  Finset.mem_Ico.mp hn_interval
                have hn_le_m : n ≤ m :=
                  Nat.le_of_lt_succ hn_bounds.2
                have hn_block : n ∈ Finset.Icc a b :=
                  Finset.mem_Icc.mpr
                    (And.intro hn_bounds.1
                      (Nat.le_trans hn_le_m hm_bounds.2))
                hdown m n hm_mem hn_block hn_le_m))
      exact Exists.intro c
        (And.intro hc_left (And.intro hc_right hS_eq))

/-- A finite subset of an integer block that is upward closed is a terminal
interval.  This is the finite-order owner lemma used by the far-right endpoint
packet reconstruction; all analytic input is isolated in the upward-closure
hypothesis. -/
theorem Finset.exists_eq_Icc_of_subset_Icc_upwardClosed
    {S : Finset ℕ}
    {a b : ℕ}
    (hS_block : S ⊆ Finset.Icc a b)
    (hup :
      ∀ n k : ℕ,
        n ∈ S →
        k ∈ Finset.Icc a b →
        n ≤ k →
          k ∈ S) :
    ∃ c : ℕ, a ≤ c ∧ c ≤ b + 1 ∧ S = Finset.Icc c b := by
  match S.eq_empty_or_nonempty with
  | Or.inl hS_empty =>
      have hIcc_empty : Finset.Icc (b + 1) b = (∅ : Finset ℕ) :=
        Finset.eq_empty_iff_forall_not_mem.mpr
          (fun n hn =>
            have hn_bounds : b + 1 ≤ n ∧ n ≤ b :=
              Finset.mem_Icc.mp hn
            have hb_lt_n : b < n :=
              Nat.lt_of_succ_le hn_bounds.1
            not_le_of_gt hb_lt_n hn_bounds.2)
      exact Exists.intro (b + 1)
        (And.intro (Nat.le_trans hab (Nat.le_succ b))
          (And.intro le_rfl
            (Eq.trans hS_empty hIcc_empty.symm)))
  | Or.inr hS_nonempty =>
      let c : ℕ := S.min' hS_nonempty
      have hc_mem : c ∈ S :=
        Finset.min'_mem S hS_nonempty
      have hc_block : c ∈ Finset.Icc a b :=
        hS_block hc_mem
      have hc_bounds : a ≤ c ∧ c ≤ b :=
        Finset.mem_Icc.mp hc_block
      have hc_right : c ≤ b + 1 :=
        Nat.le_trans hc_bounds.2 (Nat.le_succ b)
      have hS_eq : S = Finset.Icc c b :=
        Finset.ext
          (fun n =>
            Iff.intro
              (fun hn =>
                have hn_block : n ∈ Finset.Icc a b :=
                  hS_block hn
                have hn_bounds : a ≤ n ∧ n ≤ b :=
                  Finset.mem_Icc.mp hn_block
                have hc_le_n : c ≤ n :=
                  Finset.min'_le S n hn
                Finset.mem_Icc.mpr (And.intro hc_le_n hn_bounds.2))
              (fun hn_interval =>
                have hn_bounds : c ≤ n ∧ n ≤ b :=
                  Finset.mem_Icc.mp hn_interval
                have hn_block : n ∈ Finset.Icc a b :=
                  Finset.mem_Icc.mpr
                    (And.intro
                      (Nat.le_trans hc_bounds.1 hn_bounds.1)
                      hn_bounds.2)
                hup c n hc_mem hn_block hn_bounds.1))
      exact Exists.intro c
        (And.intro hc_bounds.1 (And.intro hc_right hS_eq))

/-- The logarithmic derivative-packet index is monotone in the sample variable
on the positive branch `t ≥ 0`. -/
theorem Complex.logarithmicPhaseRealPhase_derivPacketIndex_mono
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b k n : ℕ}
    (ha : 1 ≤ a)
    (hk_block : k ∈ Finset.Icc a b)
    (hn_block : n ∈ Finset.Icc a b)
    (hkn : k ≤ n) :
    Complex.realPhase_secondDerivative_vdc_derivPacketIndex
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) k ≤
      Complex.realPhase_secondDerivative_vdc_derivPacketIndex
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) n := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  have hk_one : 1 ≤ k :=
    le_trans ha (Finset.mem_Icc.mp hk_block).1
  have hn_one : 1 ≤ n :=
    le_trans ha (Finset.mem_Icc.mp hn_block).1
  have hk_pos_nat : 0 < k :=
    Nat.lt_of_succ_le hk_one
  have hn_pos_nat : 0 < n :=
    Nat.lt_of_succ_le hn_one
  have hk_pos : 0 < (k : ℝ) :=
    Nat.cast_pos.mpr hk_pos_nat
  have hn_pos : 0 < (n : ℝ) :=
    Nat.cast_pos.mpr hn_pos_nat
  have hT_nonneg : 0 ≤ ‖t‖ :=
    norm_nonneg t
  have hrecip :
      (n : ℝ)⁻¹ ≤ (k : ℝ)⁻¹ :=
    inv_anti₀ hk_pos (Nat.cast_le.mpr hkn)
  have hscale :
      ‖t‖ / (n : ℝ) ≤ ‖t‖ / (k : ℝ) := by
    have hmul :
        ‖t‖ * (n : ℝ)⁻¹ ≤ ‖t‖ * (k : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left hrecip hT_nonneg
    exact
      Eq.subst
        (motive := fun left : ℝ => left ≤ ‖t‖ / (k : ℝ))
        (div_eq_mul_inv ‖t‖ (n : ℝ)).symm
        (Eq.subst
          (motive := fun right : ℝ => ‖t‖ * (n : ℝ)⁻¹ ≤ right)
          (div_eq_mul_inv ‖t‖ (k : ℝ)).symm
          hmul)
  have hderiv_k :
      deriv φ k = -(‖t‖ / (k : ℝ)) :=
    Complex.logarithmicPhaseRealPhase_deriv_eq_neg_norm_div_parenthesized
      t ht_nonneg hk_pos
  have hderiv_n :
      deriv φ n = -(‖t‖ / (n : ℝ)) :=
    Complex.logarithmicPhaseRealPhase_deriv_eq_neg_norm_div_parenthesized
      t ht_nonneg hn_pos
  have hderiv_le :
      deriv φ k ≤ deriv φ n := by
    have hneg :
        -(‖t‖ / (k : ℝ)) ≤ -(‖t‖ / (n : ℝ)) :=
      neg_le_neg hscale
    exact
      Eq.subst
        (motive := fun left : ℝ => left ≤ deriv φ n)
        hderiv_k.symm
        (Eq.subst
          (motive := fun right : ℝ => -(‖t‖ / (k : ℝ)) ≤ right)
          hderiv_n.symm
          hneg)
  have hfloor_arg :
      deriv φ k + (1 / 2 : ℝ) ≤ deriv φ n + (1 / 2 : ℝ) :=
    add_le_add_right hderiv_le (1 / 2 : ℝ)
  exact Int.floor_mono hfloor_arg

/-- The left endpoint packet-index set is downward closed inside the active
packet indices. -/
theorem Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets_index_downwardClosed
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    {m j : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b)
    (hj_active :
      j ∈
        Complex.realPhase_secondDerivative_vdc_activeDerivPackets
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b)
    (hjm : j ≤ m) :
    j ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b := by
  have hm_endpoint :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b :=
    (Finset.mem_filter.mp hm).1
  have hm_data :
      m < 0 ∧
        Complex.logarithmicPhaseRealPhase_stationaryPoint t m < (a : ℝ) :=
    (Finset.mem_filter.mp hm).2
  have hm_neg : m < 0 :=
    hm_data.1
  have hsp_m_left :
      Complex.logarithmicPhaseRealPhase_stationaryPoint t m < (a : ℝ) :=
    hm_data.2
  have hj_neg : j < 0 :=
    lt_of_le_of_lt hjm hm_neg
  have hT_nonneg : 0 ≤ ‖t‖ :=
    norm_nonneg t
  have hm_den_pos : 0 < -(m : ℝ) :=
    Int.neg_cast_pos_of_lt_zero hm_neg
  have hj_den_pos : 0 < -(j : ℝ) :=
    Int.neg_cast_pos_of_lt_zero hj_neg
  have hden_le : -(m : ℝ) ≤ -(j : ℝ) := by
    have hcast : (j : ℝ) ≤ (m : ℝ) :=
      Int.cast_le.mpr hjm
    exact neg_le_neg hcast
  have hrecip :
      (-(j : ℝ))⁻¹ ≤ (-(m : ℝ))⁻¹ :=
    inv_anti₀ hm_den_pos hden_le
  have hscale :
      ‖t‖ / (-(j : ℝ)) ≤ ‖t‖ / (-(m : ℝ)) := by
    have hmul :
        ‖t‖ * (-(j : ℝ))⁻¹ ≤ ‖t‖ * (-(m : ℝ))⁻¹ :=
      mul_le_mul_of_nonneg_left hrecip hT_nonneg
    exact
      Eq.subst
        (motive := fun left : ℝ =>
          left ≤ ‖t‖ / (-(m : ℝ)))
        (div_eq_mul_inv ‖t‖ (-(j : ℝ))).symm
        (Eq.subst
          (motive := fun right : ℝ =>
            ‖t‖ * (-(j : ℝ))⁻¹ ≤ right)
          (div_eq_mul_inv ‖t‖ (-(m : ℝ))).symm
          hmul)
  have hsp_j_le_m :
      Complex.logarithmicPhaseRealPhase_stationaryPoint t j ≤
        Complex.logarithmicPhaseRealPhase_stationaryPoint t m := by
    show ‖t‖ / (-(j : ℝ)) ≤ ‖t‖ / (-(m : ℝ))
    exact hscale
  have hsp_j_left :
      Complex.logarithmicPhaseRealPhase_stationaryPoint t j < (a : ℝ) :=
    lt_of_le_of_lt hsp_j_le_m hsp_m_left
  have hj_not_stationary :
      ¬ ((j < 0) ∧
          Complex.logarithmicPhaseRealPhase_stationaryPoint t j ∈
            Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) :=
    fun hstat =>
      have hleft_bound :
          (a : ℝ) ≤ Complex.logarithmicPhaseRealPhase_stationaryPoint t j :=
        hstat.2.1
      not_lt_of_ge hleft_bound hsp_j_left
  have hj_endpoint :
      j ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b :=
    Finset.mem_filter.mpr (And.intro hj_active hj_not_stationary)
  exact Finset.mem_filter.mpr
    (And.intro hj_endpoint (And.intro hj_neg hsp_j_left))

/-- The far-right endpoint packet-index set is interval-convex inside the
active packet indices. -/
theorem Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets_index_intervalConvex
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    {m j l : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b)
    (hl :
      l ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b)
    (hj_active :
      j ∈
        Complex.realPhase_secondDerivative_vdc_activeDerivPackets
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b)
    (hmj : m ≤ j)
    (hjl : j ≤ l) :
    j ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b := by
  have hm_data :
      m < 0 ∧
        ((b + 1 : ℕ) : ℝ) <
          Complex.logarithmicPhaseRealPhase_stationaryPoint t m :=
    (Finset.mem_filter.mp hm).2
  have hl_data :
      l < 0 ∧
        ((b + 1 : ℕ) : ℝ) <
          Complex.logarithmicPhaseRealPhase_stationaryPoint t l :=
    (Finset.mem_filter.mp hl).2
  have hm_neg : m < 0 :=
    hm_data.1
  have hl_neg : l < 0 :=
    hl_data.1
  have hsp_m_right :
      ((b + 1 : ℕ) : ℝ) <
        Complex.logarithmicPhaseRealPhase_stationaryPoint t m :=
    hm_data.2
  have hj_neg : j < 0 :=
    lt_of_le_of_lt hjl hl_neg
  have hT_nonneg : 0 ≤ ‖t‖ :=
    norm_nonneg t
  have hm_den_pos : 0 < -(m : ℝ) :=
    Int.neg_cast_pos_of_lt_zero hm_neg
  have hj_den_pos : 0 < -(j : ℝ) :=
    Int.neg_cast_pos_of_lt_zero hj_neg
  have hden_le : -(j : ℝ) ≤ -(m : ℝ) := by
    have hcast : (m : ℝ) ≤ (j : ℝ) :=
      Int.cast_le.mpr hmj
    exact neg_le_neg hcast
  have hrecip :
      (-(m : ℝ))⁻¹ ≤ (-(j : ℝ))⁻¹ :=
    inv_anti₀ hj_den_pos hden_le
  have hscale :
      ‖t‖ / (-(m : ℝ)) ≤ ‖t‖ / (-(j : ℝ)) := by
    have hmul :
        ‖t‖ * (-(m : ℝ))⁻¹ ≤ ‖t‖ * (-(j : ℝ))⁻¹ :=
      mul_le_mul_of_nonneg_left hrecip hT_nonneg
    exact
      Eq.subst
        (motive := fun left : ℝ =>
          left ≤ ‖t‖ / (-(j : ℝ)))
        (div_eq_mul_inv ‖t‖ (-(m : ℝ))).symm
        (Eq.subst
          (motive := fun right : ℝ =>
            ‖t‖ * (-(m : ℝ))⁻¹ ≤ right)
          (div_eq_mul_inv ‖t‖ (-(j : ℝ))).symm
          hmul)
  have hsp_m_le_j :
      Complex.logarithmicPhaseRealPhase_stationaryPoint t m ≤
        Complex.logarithmicPhaseRealPhase_stationaryPoint t j := by
    show ‖t‖ / (-(m : ℝ)) ≤ ‖t‖ / (-(j : ℝ))
    exact hscale
  have hsp_j_right :
      ((b + 1 : ℕ) : ℝ) <
        Complex.logarithmicPhaseRealPhase_stationaryPoint t j :=
    lt_of_lt_of_le hsp_m_right hsp_m_le_j
  have hj_not_stationary :
      ¬ ((j < 0) ∧
          Complex.logarithmicPhaseRealPhase_stationaryPoint t j ∈
            Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) :=
    fun hstat =>
      have hright_bound :
          Complex.logarithmicPhaseRealPhase_stationaryPoint t j ≤
            ((b + 1 : ℕ) : ℝ) :=
        hstat.2.2
      not_lt_of_ge hright_bound hsp_j_right
  have hj_endpoint :
      j ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b :=
    Finset.mem_filter.mpr (And.intro hj_active hj_not_stationary)
  exact Finset.mem_filter.mpr
    (And.intro hj_endpoint (And.intro hj_neg hsp_j_right))

/-- The left endpoint packet-family union is downward closed in the ambient
block.  The proof is the concrete logarithmic monotonicity argument: moving
left increases the reciprocal derivative scale, so the floor-selected packet
remains in the negative left endpoint tail. -/
theorem Complex.logarithmicPhaseRealPhase_endpointLeftPacketFamilyUnion_downwardClosed
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b n k : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hn :
      n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b
          (Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b))
    (hk_block : k ∈ Finset.Icc a b)
    (hkn : k ≤ n) :
    k ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b
        (Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b) := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  have hmember :
      ∃ m : ℤ,
        m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b ∧
          n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m :=
    Finset.mem_biUnion.mp hn
  match hmember with
  | ⟨m, hm_left, hn_packet⟩ =>
      have hn_block : n ∈ Finset.Icc a b :=
        Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block φ hn_packet
      let j : ℤ := Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ k
      have hj_active :
          j ∈ Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b :=
        Complex.realPhase_secondDerivative_vdc_derivPacketIndex_mem_active φ hk_block
      have hk_packet :
          k ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b j :=
        Complex.realPhase_secondDerivative_vdc_mem_own_derivPacket φ hk_block
      have hn_index :
          Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ n = m :=
        have hn_pair :
            n ∈ Finset.Icc a b ∧
              Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ n = m :=
          (Complex.mem_realPhase_secondDerivative_vdc_derivPacket_iff_index_eq φ).mp
            hn_packet
        hn_pair.2
      have hindex_le_raw :
          Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ k ≤
            Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ n :=
        Complex.logarithmicPhaseRealPhase_derivPacketIndex_mono
          t ht_nonneg ha hk_block hn_block hkn
      have hj_le_m : j ≤ m :=
        Eq.subst
          (motive := fun right : ℤ => j ≤ right)
          hn_index
          hindex_le_raw
      have hj_left :
          j ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b :=
        Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets_index_downwardClosed
          t ht ht_nonneg ha hm_left hj_active hj_le_m
      exact Finset.mem_biUnion.mpr
        (Exists.intro j (And.intro hj_left hk_packet))

/-- The far-right endpoint packet-family union is upward closed in the ambient
block.  The proof is the concrete logarithmic monotonicity argument: moving
right decreases the reciprocal derivative scale, so the floor-selected packet
remains in the negative far-right endpoint tail. -/
theorem Complex.logarithmicPhaseRealPhase_endpointFarRightPacketFamilyUnion_intervalConvex
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b n k l : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hn :
      n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b
          (Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b))
    (hl :
      l ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b
          (Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b))
    (hk_block : k ∈ Finset.Icc a b)
    (hnk : n ≤ k)
    (hkl : k ≤ l) :
    k ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b
        (Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b) := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  have hn_member :
      ∃ m : ℤ,
        m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b ∧
          n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m :=
    Finset.mem_biUnion.mp hn
  have hl_member :
      ∃ r : ℤ,
        r ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b ∧
          l ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b r :=
    Finset.mem_biUnion.mp hl
  match hn_member with
  | ⟨m, hm_far, hn_packet⟩ =>
      match hl_member with
      | ⟨r, hr_far, hl_packet⟩ =>
          have hn_block : n ∈ Finset.Icc a b :=
            Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block φ hn_packet
          have hl_block : l ∈ Finset.Icc a b :=
            Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block φ hl_packet
          let j : ℤ := Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ k
          have hj_active :
              j ∈ Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b :=
            Complex.realPhase_secondDerivative_vdc_derivPacketIndex_mem_active φ hk_block
          have hk_packet :
              k ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b j :=
            Complex.realPhase_secondDerivative_vdc_mem_own_derivPacket φ hk_block
          have hn_index :
              Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ n = m :=
            have hn_pair :
                n ∈ Finset.Icc a b ∧
                  Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ n = m :=
              (Complex.mem_realPhase_secondDerivative_vdc_derivPacket_iff_index_eq φ).mp
                hn_packet
            hn_pair.2
          have hl_index :
              Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ l = r :=
            have hl_pair :
                l ∈ Finset.Icc a b ∧
                  Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ l = r :=
              (Complex.mem_realPhase_secondDerivative_vdc_derivPacket_iff_index_eq φ).mp
                hl_packet
            hl_pair.2
          have hm_le_j_raw :
              Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ n ≤
                Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ k :=
            Complex.logarithmicPhaseRealPhase_derivPacketIndex_mono
              t ht_nonneg ha hn_block hk_block hnk
          have hj_le_r_raw :
              Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ k ≤
                Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ l :=
            Complex.logarithmicPhaseRealPhase_derivPacketIndex_mono
              t ht_nonneg ha hk_block hl_block hkl
          have hm_le_j : m ≤ j :=
            Eq.subst
              (motive := fun left : ℤ => left ≤ j)
              hn_index
              hm_le_j_raw
          have hj_le_r : j ≤ r :=
            Eq.subst
              (motive := fun right : ℤ => j ≤ right)
              hl_index
              hj_le_r_raw
          have hj_far :
              j ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b :=
            Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets_index_intervalConvex
              t ht ht_nonneg ha hm_far hr_far hj_active hm_le_j hj_le_r
          exact Finset.mem_biUnion.mpr
            (Exists.intro j (And.intro hj_far hk_packet))

/-- A finite subset of an integer block that is interval-convex is a bounded
integer interval. -/
theorem Finset.exists_eq_Ico_of_subset_Icc_intervalConvex
    {S : Finset ℕ}
    {a b : ℕ}
    (hS_block : S ⊆ Finset.Icc a b)
    (hconvex :
      ∀ n k l : ℕ,
        n ∈ S →
        l ∈ S →
        k ∈ Finset.Icc a b →
        n ≤ k →
        k ≤ l →
          k ∈ S) :
    ∃ c d : ℕ,
      a ≤ c ∧ c ≤ d ∧ d ≤ b + 1 ∧ S = Finset.Ico c d := by
  match S.eq_empty_or_nonempty with
  | Or.inl hS_empty =>
      have hIco_empty : Finset.Ico a a = (∅ : Finset ℕ) :=
        Finset.eq_empty_iff_forall_not_mem.mpr
          (fun n hn =>
            have hn_bounds : a ≤ n ∧ n < a :=
              Finset.mem_Ico.mp hn
            not_lt_of_ge hn_bounds.1 hn_bounds.2)
      exact Exists.intro a
        (Exists.intro a
          (And.intro le_rfl
            (And.intro le_rfl
              (And.intro
                (Nat.le_trans hab (Nat.le_succ b))
                (Eq.trans hS_empty hIco_empty.symm)))))
  | Or.inr hS_nonempty =>
      let c : ℕ := S.min' hS_nonempty
      let r : ℕ := S.max' hS_nonempty
      let d : ℕ := r + 1
      have hc_mem : c ∈ S :=
        Finset.min'_mem S hS_nonempty
      have hr_mem : r ∈ S :=
        Finset.max'_mem S hS_nonempty
      have hc_block : c ∈ Finset.Icc a b :=
        hS_block hc_mem
      have hr_block : r ∈ Finset.Icc a b :=
        hS_block hr_mem
      have hc_bounds : a ≤ c ∧ c ≤ b :=
        Finset.mem_Icc.mp hc_block
      have hr_bounds : a ≤ r ∧ r ≤ b :=
        Finset.mem_Icc.mp hr_block
      have hc_le_r : c ≤ r :=
        Finset.min'_le S r hr_mem
      have hc_le_d : c ≤ d :=
        Nat.le_trans hc_le_r (Nat.le_succ r)
      have hd_right : d ≤ b + 1 :=
        Nat.succ_le_succ hr_bounds.2
      have hS_eq : S = Finset.Ico c d :=
        Finset.ext
          (fun n =>
            Iff.intro
              (fun hn =>
                have hc_le_n : c ≤ n :=
                  Finset.min'_le S n hn
                have hn_le_r : n ≤ r :=
                  Finset.le_max' S n hn
                have hn_lt_d : n < d :=
                  Nat.lt_succ_of_le hn_le_r
                Finset.mem_Ico.mpr (And.intro hc_le_n hn_lt_d))
              (fun hn_interval =>
                have hn_bounds : c ≤ n ∧ n < d :=
                  Finset.mem_Ico.mp hn_interval
                have hn_le_r : n ≤ r :=
                  Nat.le_of_lt_succ hn_bounds.2
                have hn_block : n ∈ Finset.Icc a b :=
                  Finset.mem_Icc.mpr
                    (And.intro
                      (Nat.le_trans hc_bounds.1 hn_bounds.1)
                      (Nat.le_trans hn_le_r hr_bounds.2))
                hconvex c n r hc_mem hr_mem hn_block hn_bounds.1 hn_le_r))
      exact Exists.intro c
        (Exists.intro d
          (And.intro hc_bounds.1
            (And.intro hc_le_d
              (And.intro hd_right hS_eq))))

/-- A closed natural interval is the corresponding successor-right half-open
interval. -/
theorem Finset.Icc_eq_Ico_succ_right
    {c b : ℕ}
    (hcb : c ≤ b) :
    Finset.Icc c b = Finset.Ico c (b + 1) := by
  exact Finset.ext
    (fun n =>
      Iff.intro
        (fun hn =>
          have hn_bounds : c ≤ n ∧ n ≤ b :=
            Finset.mem_Icc.mp hn
          have hn_lt_succ : n < b + 1 :=
            Nat.lt_succ_of_le hn_bounds.2
          Finset.mem_Ico.mpr (And.intro hn_bounds.1 hn_lt_succ))
        (fun hn =>
          have hn_bounds : c ≤ n ∧ n < b + 1 :=
            Finset.mem_Ico.mp hn
          have hn_le_b : n ≤ b :=
            Nat.lt_succ_iff.mp hn_bounds.2
          Finset.mem_Icc.mpr (And.intro hn_bounds.1 hn_le_b)))

/-- A nonempty half-open natural interval is the corresponding closed interval
ending at the predecessor of its right endpoint. -/
theorem Finset.Ico_eq_Icc_pred_right
    {c d : ℕ}
    (hcd : c < d) :
    Finset.Ico c d = Finset.Icc c (d - 1) := by
  exact Finset.ext
    (fun n =>
      Iff.intro
        (fun hn =>
          have hn_bounds : c ≤ n ∧ n < d :=
            Finset.mem_Ico.mp hn
          have hn_le_pred : n ≤ d - 1 :=
            Nat.le_pred_of_lt hn_bounds.2
          Finset.mem_Icc.mpr (And.intro hn_bounds.1 hn_le_pred))
        (fun hn =>
          have hn_bounds : c ≤ n ∧ n ≤ d - 1 :=
            Finset.mem_Icc.mp hn
          have hn_lt_d : n < d :=
            Nat.lt_of_le_pred hn_bounds.2
          Finset.mem_Ico.mpr (And.intro hn_bounds.1 hn_lt_d)))

/-- Early finite split of a logarithmic block into stationary and endpoint
derivative-frequency packet contributions.

This is the finite, non-analytic decomposition needed by the local B-process
owner below.  It is deliberately placed before the interval B-process theorem
so the analytic sink can consume the real packet split instead of a false
shifted-correlation shortcut. -/
theorem Complex.logarithmicPhaseRealPhase_block_norm_le_stationary_endpoint_packet_norms_early
    (t : ℝ)
    (a b : ℕ) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ +
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  let stationary : Finset ℤ :=
    Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b
  let endpoint : Finset ℤ :=
    Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b
  let packet : ℤ → ℂ :=
    fun m : ℤ => Complex.realPhase_secondDerivative_vdc_packetSum φ a b m
  have hpartition :
      Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b =
        stationary ∪ endpoint :=
    Complex.logarithmicPhaseRealPhase_activeDerivPackets_eq_stationary_union_endpoint
      t a b
  have hdisjoint : Disjoint stationary endpoint :=
    Complex.logarithmicPhaseRealPhase_stationary_endpoint_disjoint t a b
  have hpacket_sum :
      (∑ m ∈ Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b,
        packet m) =
        (∑ m ∈ stationary, packet m) + ∑ m ∈ endpoint, packet m := by
    have hchange :
        (∑ m ∈ Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b,
          packet m) =
          ∑ m ∈ stationary ∪ endpoint, packet m :=
      congrArg (fun s : Finset ℤ => ∑ m ∈ s, packet m) hpartition
    have hunion :
        (∑ m ∈ stationary ∪ endpoint, packet m) =
          (∑ m ∈ stationary, packet m) + ∑ m ∈ endpoint, packet m :=
      Finset.sum_union hdisjoint
    exact Eq.trans hchange hunion
  have hactive_eq_block :
      (∑ m ∈ Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b,
        packet m) =
      ∑ n ∈ Finset.Icc a b,
        Complex.exp (Complex.I * (φ n : ℂ)) :=
    Complex.realPhase_secondDerivative_vdc_activePacketSums_eq_block_sum φ a b
  have hblock_eq :
      (∑ n ∈ Finset.Icc a b,
        Complex.exp (Complex.I * (φ n : ℂ))) =
        (∑ m ∈ stationary, packet m) + ∑ m ∈ endpoint, packet m :=
    Eq.trans hactive_eq_block.symm hpacket_sum
  have htriangle :
      ‖(∑ m ∈ stationary, packet m) + ∑ m ∈ endpoint, packet m‖ ≤
        ‖∑ m ∈ stationary, packet m‖ + ‖∑ m ∈ endpoint, packet m‖ :=
    norm_add_le
      (∑ m ∈ stationary, packet m)
      (∑ m ∈ endpoint, packet m)
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        ‖z‖ ≤
          ‖∑ m ∈ stationary, packet m‖ +
          ‖∑ m ∈ endpoint, packet m‖)
      hblock_eq.symm
      htriangle

/-- A natural sample in a restricted subblock lies in the ambient real block. -/
theorem Nat.cast_mem_ambient_Icc_of_mem_subblock_Icc
    {a b c r n : ℕ}
    (hc_left : a ≤ c)
    (hr_right : r ≤ b)
    (hn : n ∈ Finset.Icc c r) :
    (n : ℝ) ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) := by
  have hn_bounds : c ≤ n ∧ n ≤ r :=
    Finset.mem_Icc.mp hn
  exact
    And.intro
      (Nat.cast_le.mpr (Nat.le_trans hc_left hn_bounds.1))
      (Nat.cast_le.mpr
        (Nat.le_trans hn_bounds.2
          (Nat.le_trans hr_right (Nat.le_succ b))))

/-- A real point in a restricted subblock interval lies in the ambient block. -/
theorem Real.mem_ambient_Icc_of_mem_subblock_Icc
    {a b c r : ℕ}
    {x : ℝ}
    (hc_left : a ≤ c)
    (hr_right : r ≤ b)
    (hx : x ∈ Set.Icc (c : ℝ) ((r + 1 : ℕ) : ℝ)) :
    x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) := by
  exact
    And.intro
      (le_trans (Nat.cast_le.mpr hc_left) hx.1)
      (le_trans hx.2
        (Nat.cast_le.mpr
          (Nat.succ_le_succ hr_right)))

/-- Ambient logarithmic derivative growth restricts to any subblock. -/
theorem Complex.logarithmicPhaseRealPhase_deriv_growth_on_subblock
    (t : ℝ)
    {a b c r : ℕ}
    (hc_left : a ≤ c)
    (hr_right : r ≤ b)
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x))
    {x y : ℝ}
    (hx : x ∈ Set.Icc (c : ℝ) ((r + 1 : ℕ) : ℝ))
    (hy : y ∈ Set.Icc (c : ℝ) ((r + 1 : ℕ) : ℝ))
    (hxy : x ≤ y) :
      (‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          (y - x) ≤
        deriv
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
        deriv
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x) := by
  exact
    hderiv_growth x y
      (Real.mem_ambient_Icc_of_mem_subblock_Icc hc_left hr_right hx)
      (Real.mem_ambient_Icc_of_mem_subblock_Icc hc_left hr_right hy)
      hxy

/-- A nonnegative target is bounded by three copies of itself. -/
theorem Real.logarithmicPhase_target_le_three_mul
    {E : ℝ}
    (hE : 0 ≤ E) :
    E ≤ 3 * E := by
  have hone_le_three : (1 : ℝ) ≤ 3 := by
    have htwo_nonneg : 0 ≤ (2 : ℝ) :=
      Nat.cast_nonneg 2
    calc
      (1 : ℝ) ≤ 1 + 2 :=
        le_add_of_nonneg_right htwo_nonneg
      _ = 3 := rfl
  have hmul :
      1 * E ≤ 3 * E :=
    mul_le_mul_of_nonneg_right hone_le_three hE
  exact
    Eq.subst
      (motive := fun left : ℝ => left ≤ 3 * E)
      (one_mul E)
      hmul

/-- The local long condition implies the square-root long condition. -/
theorem Real.logarithmicPhase_Icc_long_implies_sqrt_long
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {b c r : ℕ}
    (hlong :
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) <
        (((r + 1 : ℕ) : ℝ) - (c : ℝ))) :
    Real.sqrt (1 + ‖t‖) <
      (((r + 1 : ℕ) : ℝ) - (c : ℝ)) := by
  let E : ℝ :=
    (((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))
  have hE_nonneg : 0 ≤ E :=
    Real.logarithmicPhase_endpoint_sqrt_target_nonneg t ht b
  have hsqrt_le_E :
      Real.sqrt (1 + ‖t‖) ≤ E :=
    le_add_of_nonneg_left
      (Real.secondDerivativeVdc_endpointScale_nonneg (b := b) ht)
  have hE_le_eighty : E ≤ 80 * E :=
    Real.logarithmicPhase_target_le_eighty_mul hE_nonneg
  exact lt_of_le_of_lt (le_trans hsqrt_le_E hE_le_eighty) hlong

/-- The local long condition implies the endpoint-scale long condition. -/
theorem Real.logarithmicPhase_Icc_long_implies_endpoint_long
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {b c r : ℕ}
    (hlong :
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) <
        (((r + 1 : ℕ) : ℝ) - (c : ℝ))) :
    (((b + 1 : ℕ) : ℝ) / ‖t‖) <
      (((r + 1 : ℕ) : ℝ) - (c : ℝ)) := by
  let E : ℝ :=
    (((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))
  have hE_nonneg : 0 ≤ E :=
    Real.logarithmicPhase_endpoint_sqrt_target_nonneg t ht b
  have hendpoint_le_E :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) ≤ E :=
    le_add_of_nonneg_right
      (Real.secondDerivativeVdc_sqrtScale_nonneg ht)
  have hE_le_eighty : E ≤ 80 * E :=
    Real.logarithmicPhase_target_le_eighty_mul hE_nonneg
  exact lt_of_le_of_lt (le_trans hendpoint_le_E hE_le_eighty) hlong

/-- The endpoint-plus-square-root target is monotone in the natural right
endpoint. -/
theorem Real.logarithmicPhase_endpoint_sqrt_target_mono_right
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {r b : ℕ}
    (hrb : r ≤ b) :
    (((r + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) ≤
      (((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) := by
  have hT_pos : 0 < ‖t‖ :=
    lt_of_lt_of_le zero_lt_one ht
  have hnum_le : ((r + 1 : ℕ) : ℝ) ≤ ((b + 1 : ℕ) : ℝ) :=
    Nat.cast_le.mpr (Nat.succ_le_succ hrb)
  have hdiv_le :
      ((r + 1 : ℕ) : ℝ) / ‖t‖ ≤ ((b + 1 : ℕ) : ℝ) / ‖t‖ :=
    (div_le_div_right hT_pos).mpr hnum_le
  exact add_le_add_right hdiv_le (Real.sqrt (1 + ‖t‖))

/-- Three subblock endpoint-plus-square-root targets are bounded by three
ambient targets. -/
theorem Real.logarithmicPhase_three_subblock_targets_le_three_ambient
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {r b : ℕ}
    (hrb : r ≤ b) :
    3 * (((r + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) ≤
      3 * (((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) := by
  exact mul_le_mul_of_nonneg_left
    (Real.logarithmicPhase_endpoint_sqrt_target_mono_right t ht hrb)
    (Nat.cast_nonneg 3)

/-- Long local packet budget for a logarithmic `Icc` subblock.

This is the nontrivial branch of the interval B-process.  The complementary
short branch is handled by the trivial unit-modulus cardinality estimate. -/
theorem Complex.logarithmicPhaseRealPhase_Icc_longPacketBudget_le_threeTarget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b c r : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hc_left : a ≤ c)
    (hcr : c ≤ r)
    (hr_right : r ≤ b)
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖∑ n ∈ Finset.Icc c r,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  have hc_one : 1 ≤ c :=
    Nat.le_trans ha hc_left
  have hlocal :
      ‖∑ n ∈ Finset.Icc c r,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
        80 * ((((r + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
    Complex.logarithmicPhaseRealPhase_curvature_integer_block_bound
      t ht hc_one hcr
  have htarget_mono :
      80 * ((((r + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) ≤
        80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
    mul_le_mul_of_nonneg_left
      (Real.logarithmicPhase_endpoint_sqrt_target_mono_right t ht hr_right)
      (Nat.cast_nonneg 80)
  exact le_trans hlocal htarget_mono

/-- Resonance-safe logarithmic B-process estimate on a half-open subinterval.

This is the actual analytic owner needed by the endpoint and stationary packet
wrappers.  It is not a pointwise shifted-correlation/Kusmin-Landau statement:
the proof must use the logarithmic packet decomposition and reciprocal
stationary-frequency geometry. -/
theorem Complex.logarithmicPhaseRealPhase_Icc_bProcess_le_threeTarget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b c r : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hc_left : a ≤ c)
    (hcr : c ≤ r)
    (hr_right : r ≤ b)
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖∑ n ∈ Finset.Icc c r,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_Icc_longPacketBudget_le_threeTarget
      t ht ht_nonneg ha hab hc_left hcr hr_right hderiv_growth

/-- Resonance-safe logarithmic B-process estimate on a half-open subinterval. -/
theorem Complex.logarithmicPhaseRealPhase_Ico_bProcess_le_threeTarget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b c d : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hc_left : a ≤ c)
    (hcd : c ≤ d)
    (hd_right : d ≤ b + 1)
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖∑ n ∈ Finset.Ico c d,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  by_cases hempty : c = d
  · have hIco_empty : Finset.Ico c d = (∅ : Finset ℕ) := by
      exact Finset.eq_empty_iff_forall_not_mem.mpr
        (fun n hn =>
          have hn_bounds : c ≤ n ∧ n < d :=
            Finset.mem_Ico.mp hn
          have hn_lt_c : n < c :=
            Eq.subst
              (motive := fun right : ℕ => n < right)
              hempty.symm
              hn_bounds.2
          not_lt_of_ge hn_bounds.1 hn_lt_c)
    have hsum_zero :
        (∑ n ∈ Finset.Ico c d, Complex.exp (Complex.I * (φ n : ℂ))) = 0 := by
      exact Eq.trans
        (congrArg
          (fun S : Finset ℕ =>
            ∑ n ∈ S, Complex.exp (Complex.I * (φ n : ℂ)))
          hIco_empty)
        Finset.sum_empty
    have htarget_nonneg :
        0 ≤ 80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
      mul_nonneg (Nat.cast_nonneg 80)
        (Real.logarithmicPhase_endpoint_sqrt_target_nonneg t ht b)
    have hzero_bound :
        ‖(0 : ℂ)‖ ≤
          80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
      Eq.subst
        (motive := fun left : ℝ =>
          left ≤
            80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
        (norm_zero : ‖(0 : ℂ)‖ = 0)
        htarget_nonneg
    exact
      Eq.subst
        (motive := fun z : ℂ =>
          ‖z‖ ≤
            80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
        hsum_zero.symm
        hzero_bound
  · have hcd_strict : c < d :=
      lt_of_le_of_ne hcd hempty
    let r : ℕ := d - 1
    have hIco_eq : Finset.Ico c d = Finset.Icc c r :=
      Finset.Ico_eq_Icc_pred_right hcd_strict
    have hcr : c ≤ r :=
      Nat.le_pred_of_lt hcd_strict
    have hr_le_b : r ≤ b := by
      have hd_pos : 0 < d :=
        lt_of_le_of_lt (Nat.zero_le c) hcd_strict
      have hd_pred_succ : r + 1 = d :=
        Nat.succ_pred_eq_of_pos hd_pos
      have hsucc_le : r + 1 ≤ b + 1 :=
        Eq.subst
          (motive := fun left : ℕ => left ≤ b + 1)
          hd_pred_succ.symm
          hd_right
      exact Nat.succ_le_succ_iff.mp hsucc_le
    have hlocal :
        ‖∑ n ∈ Finset.Icc c r, Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
          80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
      Complex.logarithmicPhaseRealPhase_Icc_bProcess_le_threeTarget
        t ht ht_nonneg ha hab hc_left hcr hr_le_b hderiv_growth
    exact
      Eq.subst
        (motive := fun S : Finset ℕ =>
          ‖∑ n ∈ S, Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
            80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
        hIco_eq.symm
        hlocal

/-- Resonance-safe sharp second-derivative estimate on a half-open subinterval
of the logarithmic block.  This is the single endpoint-interval analytic owner:
terminal, initial, and bounded endpoint packet intervals are all wrappers over
this theorem. -/
theorem Complex.logarithmicPhaseRealPhase_Ico_secondDerivative_le_threeTarget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b c d : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hc_left : a ≤ c)
    (hcd : c ≤ d)
    (hd_right : d ≤ b + 1)
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖∑ n ∈ Finset.Ico c d,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_Ico_bProcess_le_threeTarget
      t ht ht_nonneg ha hab hc_left hcd hd_right hderiv_growth

/-- Resonance-safe sharp endpoint second-derivative estimate on a terminal
subinterval.  This is the exact analytic owner theorem needed by the right zero
tail. -/
theorem Complex.logarithmicPhaseRealPhase_terminalInterval_secondDerivative_le_threeTarget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b c : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hc_left : a ≤ c)
    (hc_right : c ≤ b)
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖∑ n ∈ Finset.Icc c b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  have hIcc_eq : Finset.Icc c b = Finset.Ico c (b + 1) :=
    Finset.Icc_eq_Ico_succ_right hc_right
  have hIco :
      ‖∑ n ∈ Finset.Ico c (b + 1),
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
        80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
    Complex.logarithmicPhaseRealPhase_Ico_secondDerivative_le_threeTarget
      t ht ht_nonneg ha hab hc_left
      (Nat.le_trans hc_right (Nat.le_succ b))
      le_rfl hderiv_growth
  exact
    Eq.subst
      (motive := fun S : Finset ℕ =>
        ‖∑ n ∈ S,
          Complex.exp
            (Complex.I *
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
          80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
      hIcc_eq.symm
      hIco

/-- Resonance-safe sharp endpoint second-derivative estimate on an initial
subinterval.  This is the exact analytic owner theorem needed by the left
endpoint tail. -/
theorem Complex.logarithmicPhaseRealPhase_initialInterval_secondDerivative_le_threeTarget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b c : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hc_left : a < c)
    (hc_right : c ≤ b + 1)
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖∑ n ∈ Finset.Ico a c,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_Ico_secondDerivative_le_threeTarget
      t ht ht_nonneg ha hab le_rfl (le_of_lt hc_left) hc_right
      hderiv_growth

/-- Resonance-safe sharp second-derivative estimate on a bounded subinterval.
This is the analytic owner theorem consumed by the far-right negative endpoint
packet family after its interval reconstruction. -/
theorem Complex.logarithmicPhaseRealPhase_boundedInterval_secondDerivative_le_threeTarget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b c d : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hc_left : a ≤ c)
    (hcd : c ≤ d)
    (hd_right : d ≤ b + 1)
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖∑ n ∈ Finset.Ico c d,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_Ico_secondDerivative_le_threeTarget
      t ht ht_nonneg ha hab hc_left hcd hd_right hderiv_growth

/-- The stationary packet-index set is interval-convex inside the active
packet indices. -/
theorem Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets_index_intervalConvex
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    {m j l : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b)
    (hl :
      l ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b)
    (hj_active :
      j ∈
        Complex.realPhase_secondDerivative_vdc_activeDerivPackets
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b)
    (hmj : m ≤ j)
    (hjl : j ≤ l) :
    j ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b := by
  have hm_neg :
      m < 0 :=
    Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets_index_neg
      t hm
  have hl_neg :
      l < 0 :=
    Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets_index_neg
      t hl
  have hpoint_m :
      Complex.logarithmicPhaseRealPhase_stationaryPoint t m ∈
        Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) :=
    Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets_point_mem_Icc
      t hm
  have hpoint_l :
      Complex.logarithmicPhaseRealPhase_stationaryPoint t l ∈
        Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) :=
    Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets_point_mem_Icc
      t hl
  have hj_neg : j < 0 :=
    lt_of_le_of_lt hjl hl_neg
  have hT_nonneg : 0 ≤ ‖t‖ :=
    norm_nonneg t
  have hm_den_pos : 0 < -(m : ℝ) :=
    Int.neg_cast_pos_of_lt_zero hm_neg
  have hj_den_pos : 0 < -(j : ℝ) :=
    Int.neg_cast_pos_of_lt_zero hj_neg
  have hl_den_pos : 0 < -(l : ℝ) :=
    Int.neg_cast_pos_of_lt_zero hl_neg
  have hm_to_j_den : -(j : ℝ) ≤ -(m : ℝ) := by
    have hcast : (m : ℝ) ≤ (j : ℝ) :=
      Int.cast_le.mpr hmj
    exact neg_le_neg hcast
  have hj_to_l_den : -(l : ℝ) ≤ -(j : ℝ) := by
    have hcast : (j : ℝ) ≤ (l : ℝ) :=
      Int.cast_le.mpr hjl
    exact neg_le_neg hcast
  have hrecip_mj :
      (-(m : ℝ))⁻¹ ≤ (-(j : ℝ))⁻¹ :=
    inv_anti₀ hj_den_pos hm_to_j_den
  have hrecip_jl :
      (-(j : ℝ))⁻¹ ≤ (-(l : ℝ))⁻¹ :=
    inv_anti₀ hl_den_pos hj_to_l_den
  have hscale_mj :
      ‖t‖ / (-(m : ℝ)) ≤ ‖t‖ / (-(j : ℝ)) := by
    have hmul :
        ‖t‖ * (-(m : ℝ))⁻¹ ≤ ‖t‖ * (-(j : ℝ))⁻¹ :=
      mul_le_mul_of_nonneg_left hrecip_mj hT_nonneg
    exact
      Eq.subst
        (motive := fun left : ℝ => left ≤ ‖t‖ / (-(j : ℝ)))
        (div_eq_mul_inv ‖t‖ (-(m : ℝ))).symm
        (Eq.subst
          (motive := fun right : ℝ => ‖t‖ * (-(m : ℝ))⁻¹ ≤ right)
          (div_eq_mul_inv ‖t‖ (-(j : ℝ))).symm
          hmul)
  have hscale_jl :
      ‖t‖ / (-(j : ℝ)) ≤ ‖t‖ / (-(l : ℝ)) := by
    have hmul :
        ‖t‖ * (-(j : ℝ))⁻¹ ≤ ‖t‖ * (-(l : ℝ))⁻¹ :=
      mul_le_mul_of_nonneg_left hrecip_jl hT_nonneg
    exact
      Eq.subst
        (motive := fun left : ℝ => left ≤ ‖t‖ / (-(l : ℝ)))
        (div_eq_mul_inv ‖t‖ (-(j : ℝ))).symm
        (Eq.subst
          (motive := fun right : ℝ => ‖t‖ * (-(j : ℝ))⁻¹ ≤ right)
          (div_eq_mul_inv ‖t‖ (-(l : ℝ))).symm
          hmul)
  have hpoint_mj :
      Complex.logarithmicPhaseRealPhase_stationaryPoint t m ≤
        Complex.logarithmicPhaseRealPhase_stationaryPoint t j := by
    show ‖t‖ / (-(m : ℝ)) ≤ ‖t‖ / (-(j : ℝ))
    exact hscale_mj
  have hpoint_jl :
      Complex.logarithmicPhaseRealPhase_stationaryPoint t j ≤
        Complex.logarithmicPhaseRealPhase_stationaryPoint t l := by
    show ‖t‖ / (-(j : ℝ)) ≤ ‖t‖ / (-(l : ℝ))
    exact hscale_jl
  have hpoint_j :
      Complex.logarithmicPhaseRealPhase_stationaryPoint t j ∈
        Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) :=
    And.intro
      (le_trans hpoint_m.1 hpoint_mj)
      (le_trans hpoint_jl hpoint_l.2)
  exact Finset.mem_filter.mpr
    (And.intro hj_active (And.intro hj_neg hpoint_j))

/-- The stationary packet-family sample union is interval-convex in the
ambient block. -/
theorem Complex.logarithmicPhaseRealPhase_stationaryPacketFamilyUnion_intervalConvex
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b n k l : ℕ}
    (ha : 1 ≤ a)
    (hn :
      n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b
          (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b))
    (hl :
      l ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b
          (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b))
    (hk_block : k ∈ Finset.Icc a b)
    (hnk : n ≤ k)
    (hkl : k ≤ l) :
    k ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b
        (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b) := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  have hn_member :
      ∃ m : ℤ,
        m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b ∧
          n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m :=
    Finset.mem_biUnion.mp hn
  have hl_member :
      ∃ r : ℤ,
        r ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b ∧
          l ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b r :=
    Finset.mem_biUnion.mp hl
  match hn_member with
  | ⟨m, hm_stat, hn_packet⟩ =>
      match hl_member with
      | ⟨r, hr_stat, hl_packet⟩ =>
          have hn_block : n ∈ Finset.Icc a b :=
            Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block φ hn_packet
          have hl_block : l ∈ Finset.Icc a b :=
            Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block φ hl_packet
          let j : ℤ := Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ k
          have hj_active :
              j ∈ Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b :=
            Complex.realPhase_secondDerivative_vdc_derivPacketIndex_mem_active φ hk_block
          have hk_packet :
              k ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b j :=
            Complex.realPhase_secondDerivative_vdc_mem_own_derivPacket φ hk_block
          have hn_index :
              Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ n = m :=
            have hn_pair :
                n ∈ Finset.Icc a b ∧
                  Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ n = m :=
              (Complex.mem_realPhase_secondDerivative_vdc_derivPacket_iff_index_eq φ).mp
                hn_packet
            hn_pair.2
          have hl_index :
              Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ l = r :=
            have hl_pair :
                l ∈ Finset.Icc a b ∧
                  Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ l = r :=
              (Complex.mem_realPhase_secondDerivative_vdc_derivPacket_iff_index_eq φ).mp
                hl_packet
            hl_pair.2
          have hm_le_j_raw :
              Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ n ≤
                Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ k :=
            Complex.logarithmicPhaseRealPhase_derivPacketIndex_mono
              t ht_nonneg ha hn_block hk_block hnk
          have hj_le_r_raw :
              Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ k ≤
                Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ l :=
            Complex.logarithmicPhaseRealPhase_derivPacketIndex_mono
              t ht_nonneg ha hk_block hl_block hkl
          have hm_le_j : m ≤ j :=
            Eq.subst
              (motive := fun left : ℤ => left ≤ j)
              hn_index
              hm_le_j_raw
          have hj_le_r : j ≤ r :=
            Eq.subst
              (motive := fun right : ℤ => j ≤ right)
              hl_index
              hj_le_r_raw
          have hj_stat :
              j ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b :=
            Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets_index_intervalConvex
              t ht hm_stat hr_stat hj_active hm_le_j hj_le_r
          exact Finset.mem_biUnion.mpr
            (Exists.intro j (And.intro hj_stat hk_packet))

/-- The stationary packet-family sample union is a bounded natural interval
inside the ambient block.  This is the exact finite-order reconstruction needed
to apply the ambient second-derivative estimate to the stationary contribution
without summing crude packet-cardinality bounds. -/
theorem Complex.logarithmicPhaseRealPhase_stationaryPacketFamilyUnion_eq_boundedInterval
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    ∃ c d : ℕ,
      a ≤ c ∧ c ≤ d ∧ d ≤ b + 1 ∧
        Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b
          (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b) =
          Finset.Ico c d := by
  let S : Finset ℕ :=
    Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b
      (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b)
  have hS_block : S ⊆ Finset.Icc a b := by
    intro n hn
    have hmember :
        ∃ m : ℤ,
          m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b ∧
            n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              a b m :=
      Finset.mem_biUnion.mp hn
    match hmember with
    | ⟨m, hm, hn_packet⟩ =>
        exact
          Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            hn_packet
  have hconvex :
      ∀ n k l : ℕ,
        n ∈ S →
        l ∈ S →
        k ∈ Finset.Icc a b →
        n ≤ k →
        k ≤ l →
          k ∈ S :=
    fun n k l hn hl hk_block hnk hkl =>
      Complex.logarithmicPhaseRealPhase_stationaryPacketFamilyUnion_intervalConvex
        t ht ht_nonneg ha hn hl hk_block hnk hkl
  exact Finset.exists_eq_Ico_of_subset_Icc_intervalConvex hS_block hconvex

/-- Three target units are bounded by ten target units for a nonnegative
target. -/
theorem Real.logarithmicPhase_three_target_le_ten
    {E : ℝ}
    (hE : 0 ≤ E) :
    3 * E ≤ 10 * E := by
  have hthree_le_ten : (3 : ℝ) ≤ 10 := by
    have hseven_nonneg : 0 ≤ (7 : ℝ) :=
      Nat.cast_nonneg 7
    calc
      (3 : ℝ) ≤ 3 + 7 :=
        le_add_of_nonneg_right hseven_nonneg
      _ = 10 := by
        have hnat : (3 + 7 : ℕ) = 10 :=
          rfl
        exact Eq.trans
          (Nat.cast_add 3 7).symm
          (Eq.trans
            (congrArg (fun n : ℕ => (n : ℝ)) hnat)
            Nat.cast_ofNat)
  exact mul_le_mul_of_nonneg_right hthree_le_ten hE

/-- Stationary packet sums are controlled by the true reciprocal frequency
count and the local B-process estimates.  This is the packet-sum owner; sample
unions are converted to it by disjoint packet-family summation. -/
theorem Complex.logarithmicPhaseRealPhase_stationaryPacketSum_frequencyCount_le_tenTarget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  match
    Complex.logarithmicPhaseRealPhase_stationaryPacketFamilyUnion_eq_boundedInterval
      t ht ht_nonneg ha hab with
  | ⟨c, d, hc_left, hcd, hd_right, hunion⟩ =>
      have hsample :
          ‖∑ n ∈
            Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
              φ a b
              (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b),
            Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
            80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
        have hinterval :
            ‖∑ n ∈ Finset.Ico c d,
              Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
              80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
          Complex.logarithmicPhaseRealPhase_Ico_secondDerivative_le_threeTarget
            t ht ht_nonneg ha hab hc_left hcd hd_right hderiv_growth
        exact
          Eq.subst
            (motive := fun S : Finset ℕ =>
              ‖∑ n ∈ S, Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
                80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
            hunion.symm
            hinterval
      have hsum :
          (∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
              φ a b
              (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b),
            Complex.exp (Complex.I * (φ n : ℂ))) =
          ∑ m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b,
            Complex.realPhase_secondDerivative_vdc_packetSum φ a b m :=
        Complex.realPhase_secondDerivative_vdc_packetFamilyUnion_sum_eq_packetSums
          φ
          (fun m hm =>
            Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets_mem_active
              t hm)
      exact
        Eq.subst
          (motive := fun z : ℂ =>
            ‖z‖ ≤
              80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
          hsum
          hsample

/-- Stationary packet-family sample sum controlled by the true reciprocal
frequency count and the local B-process estimates. -/
theorem Complex.logarithmicPhaseRealPhase_stationaryPacketFamilyUnion_frequencyCount_le_tenTarget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b
        (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b),
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  have hsum :
      (∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
          φ a b
          (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b),
        Complex.exp (Complex.I * (φ n : ℂ))) =
      ∑ m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum φ a b m :=
    Complex.realPhase_secondDerivative_vdc_packetFamilyUnion_sum_eq_packetSums
      φ
      (fun m hm =>
        Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets_mem_active
          t hm)
  have hpacket :
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum φ a b m‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
    Complex.logarithmicPhaseRealPhase_stationaryPacketSum_frequencyCount_le_tenTarget
      t ht ht_nonneg ha hab hlong_sqrt hderiv_growth
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        ‖z‖ ≤
          80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
      hsum.symm
      hpacket

/-- Analytic endpoint estimate for a nonempty terminal interval in the right
zero-packet tail. -/
theorem Complex.logarithmicPhaseRealPhase_endpointRightZeroNonemptyTerminalInterval_le_longTarget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b c : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hc_left : a ≤ c)
    (hc_right : c ≤ b)
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖∑ n ∈ Finset.Icc c b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_terminalInterval_secondDerivative_le_threeTarget
      t ht ht_nonneg ha hab hc_left hc_right hlong_endpoint hderiv_growth

/-- Analytic endpoint estimate for a nonempty initial interval in the left
endpoint tail. -/
theorem Complex.logarithmicPhaseRealPhase_endpointLeftNonemptyInitialInterval_le_longTarget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b c : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hc_left : a < c)
    (hc_right : c ≤ b + 1)
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖∑ n ∈ Finset.Ico a c,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_initialInterval_secondDerivative_le_threeTarget
      t ht ht_nonneg ha hab hc_left hc_right hlong_endpoint hderiv_growth

/-- Analytic endpoint estimate for a nonempty terminal interval in the far-right
endpoint tail. -/
theorem Complex.logarithmicPhaseRealPhase_endpointFarRightNonemptyTerminalInterval_le_longTarget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b c : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hc_left : a ≤ c)
    (hc_right : c ≤ b)
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖∑ n ∈ Finset.Icc c b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_terminalInterval_secondDerivative_le_threeTarget
      t ht ht_nonneg ha hab hc_left hc_right hlong_endpoint hderiv_growth

/-- Endpoint Abel estimate on the terminal interval attached to the zero packet. -/
theorem Complex.logarithmicPhaseRealPhase_endpointRightZeroTerminalInterval_le_longTarget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b c : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hc_left : a ≤ c)
    (hc_right : c ≤ b + 1)
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖∑ n ∈ Finset.Icc c b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  by_cases hc_empty : c = b + 1
  · have hIcc_empty : Finset.Icc c b = (∅ : Finset ℕ) := by
      exact Finset.eq_empty_iff_forall_not_mem.mpr
        (fun n hn =>
          have hn_bounds : c ≤ n ∧ n ≤ b :=
            Finset.mem_Icc.mp hn
          have hb_lt_n : b < n :=
            Eq.subst
              (motive := fun left : ℕ => left ≤ n → b < n)
              hc_empty.symm
              (fun hsucc_le => Nat.lt_of_succ_le hsucc_le)
              hn_bounds.1
          not_le_of_gt hb_lt_n hn_bounds.2)
    have hsum_zero :
        (∑ n ∈ Finset.Icc c b,
          Complex.exp
            (Complex.I *
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))) =
          0 := by
      exact Eq.trans
        (congrArg
          (fun S : Finset ℕ =>
            ∑ n ∈ S,
              Complex.exp
                (Complex.I *
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ)))
          hIcc_empty)
        Finset.sum_empty
    have htarget_nonneg :
        0 ≤ 80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
      mul_nonneg (Nat.cast_nonneg 80)
        (Real.logarithmicPhase_endpoint_sqrt_target_nonneg t ht b)
    have hzero_bound :
        ‖(0 : ℂ)‖ ≤
          80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
      Eq.subst
        (motive := fun left : ℝ =>
          left ≤
            80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
        (norm_zero : ‖(0 : ℂ)‖ = 0)
        htarget_nonneg
    exact
      Eq.subst
        (motive := fun z : ℂ =>
          ‖z‖ ≤ 80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
        hsum_zero.symm
        hzero_bound
  · have hc_le_b : c ≤ b :=
      Nat.le_of_lt_succ
        (lt_of_le_of_ne hc_right hc_empty)
    exact
      Complex.logarithmicPhaseRealPhase_endpointRightZeroNonemptyTerminalInterval_le_longTarget
        t ht ht_nonneg ha hab hc_left hc_le_b hlong_endpoint hderiv_growth

/-- The left endpoint packet family is a genuine initial endpoint interval. -/
theorem Complex.logarithmicPhaseRealPhase_endpointLeftPacketFamilyUnion_eq_initialInterval
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    ∃ c : ℕ,
      a ≤ c ∧ c ≤ b + 1 ∧
      Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b
          (Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b) =
        Finset.Ico a c := by
  let S : Finset ℕ :=
    Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b
      (Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b)
  have hS_block : S ⊆ Finset.Icc a b := by
    intro n hn
    have hmember :
        ∃ m : ℤ,
          m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b ∧
            n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              a b m :=
      Finset.mem_biUnion.mp hn
    match hmember with
    | ⟨m, hm, hn_packet⟩ =>
        exact
          Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            hn_packet
  have hdown :
      ∀ n k : ℕ,
        n ∈ S →
        k ∈ Finset.Icc a b →
        k ≤ n →
          k ∈ S :=
    fun n k hn hk_block hkn =>
      Complex.logarithmicPhaseRealPhase_endpointLeftPacketFamilyUnion_downwardClosed
        t ht ht_nonneg ha hab hn hk_block hkn
  exact Finset.exists_eq_Ico_of_subset_Icc_downwardClosed hS_block hdown

/-- Endpoint Abel estimate on the initial interval selected by the left endpoint
packet family. -/
theorem Complex.logarithmicPhaseRealPhase_endpointLeftInitialInterval_le_longTarget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b c : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hc_left : a ≤ c)
    (hc_right : c ≤ b + 1)
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖∑ n ∈ Finset.Ico a c,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  by_cases hc_empty : c = a
  · have hIco_empty : Finset.Ico a c = (∅ : Finset ℕ) := by
      exact Finset.eq_empty_iff_forall_not_mem.mpr
        (fun n hn =>
          have hn_bounds : a ≤ n ∧ n < c :=
            Finset.mem_Ico.mp hn
          have hn_lt_a : n < a :=
            Eq.subst
              (motive := fun right : ℕ => n < right)
              hc_empty
              hn_bounds.2
          not_lt_of_ge hn_bounds.1 hn_lt_a)
    have hsum_zero :
        (∑ n ∈ Finset.Ico a c,
          Complex.exp
            (Complex.I *
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))) =
          0 := by
      exact Eq.trans
        (congrArg
          (fun S : Finset ℕ =>
            ∑ n ∈ S,
              Complex.exp
                (Complex.I *
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ)))
          hIco_empty)
        Finset.sum_empty
    have htarget_nonneg :
        0 ≤ 80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
      mul_nonneg (Nat.cast_nonneg 80)
        (Real.logarithmicPhase_endpoint_sqrt_target_nonneg t ht b)
    have hzero_bound :
        ‖(0 : ℂ)‖ ≤
          80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
      Eq.subst
        (motive := fun left : ℝ =>
          left ≤
            80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
        (norm_zero : ‖(0 : ℂ)‖ = 0)
        htarget_nonneg
    exact
      Eq.subst
        (motive := fun z : ℂ =>
          ‖z‖ ≤ 80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
        hsum_zero.symm
        hzero_bound
  · have ha_lt_c : a < c :=
      lt_of_le_of_ne hc_left (Ne.symm hc_empty)
    exact
      Complex.logarithmicPhaseRealPhase_endpointLeftNonemptyInitialInterval_le_longTarget
        t ht ht_nonneg ha hab ha_lt_c hc_right hlong_endpoint hderiv_growth

/-- The far-right endpoint packet family is a genuine bounded interval.  It is
not generally terminal, because the zero derivative-frequency packet may occupy
the final right tail. -/
theorem Complex.logarithmicPhaseRealPhase_endpointFarRightPacketFamilyUnion_eq_boundedInterval
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    ∃ c d : ℕ,
      a ≤ c ∧ c ≤ d ∧ d ≤ b + 1 ∧
      Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b
          (Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b) =
        Finset.Ico c d := by
  let S : Finset ℕ :=
    Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b
      (Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b)
  have hS_block : S ⊆ Finset.Icc a b := by
    intro n hn
    have hmember :
        ∃ m : ℤ,
          m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b ∧
            n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              a b m :=
      Finset.mem_biUnion.mp hn
    match hmember with
    | ⟨m, hm, hn_packet⟩ =>
        exact
          Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            hn_packet
  have hconvex :
      ∀ n k l : ℕ,
        n ∈ S →
        l ∈ S →
        k ∈ Finset.Icc a b →
        n ≤ k →
        k ≤ l →
          k ∈ S :=
    fun n k l hn hl hk_block hnk hkl =>
      Complex.logarithmicPhaseRealPhase_endpointFarRightPacketFamilyUnion_intervalConvex
        t ht ht_nonneg ha hab hn hl hk_block hnk hkl
  exact Finset.exists_eq_Ico_of_subset_Icc_intervalConvex hS_block hconvex

/-- Endpoint Abel estimate on the terminal interval selected by the far-right
endpoint packet family. -/
theorem Complex.logarithmicPhaseRealPhase_endpointFarRightTerminalInterval_le_longTarget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b c : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hc_left : a ≤ c)
    (hc_right : c ≤ b + 1)
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖∑ n ∈ Finset.Icc c b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  by_cases hc_empty : c = b + 1
  · have hIcc_empty : Finset.Icc c b = (∅ : Finset ℕ) := by
      exact Finset.eq_empty_iff_forall_not_mem.mpr
        (fun n hn =>
          have hn_bounds : c ≤ n ∧ n ≤ b :=
            Finset.mem_Icc.mp hn
          have hb_lt_n : b < n :=
            Eq.subst
              (motive := fun left : ℕ => left ≤ n → b < n)
              hc_empty.symm
              (fun hsucc_le => Nat.lt_of_succ_le hsucc_le)
              hn_bounds.1
          not_le_of_gt hb_lt_n hn_bounds.2)
    have hsum_zero :
        (∑ n ∈ Finset.Icc c b,
          Complex.exp
            (Complex.I *
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))) =
          0 := by
      exact Eq.trans
        (congrArg
          (fun S : Finset ℕ =>
            ∑ n ∈ S,
              Complex.exp
                (Complex.I *
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ)))
          hIcc_empty)
        Finset.sum_empty
    have htarget_nonneg :
        0 ≤ 80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
      mul_nonneg (Nat.cast_nonneg 80)
        (Real.logarithmicPhase_endpoint_sqrt_target_nonneg t ht b)
    have hzero_bound :
        ‖(0 : ℂ)‖ ≤
          80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
      Eq.subst
        (motive := fun left : ℝ =>
          left ≤
            80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
        (norm_zero : ‖(0 : ℂ)‖ = 0)
        htarget_nonneg
    exact
      Eq.subst
        (motive := fun z : ℂ =>
          ‖z‖ ≤ 80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
        hsum_zero.symm
        hzero_bound
  · have hc_le_b : c ≤ b :=
      Nat.le_of_lt_succ
        (lt_of_le_of_ne hc_right hc_empty)
    exact
      Complex.logarithmicPhaseRealPhase_endpointFarRightNonemptyTerminalInterval_le_longTarget
        t ht ht_nonneg ha hab hc_left hc_le_b hlong_endpoint hderiv_growth

/-- Stationary packet-family sample sum controlled by the reciprocal-image
frequency count and the local B-process packet estimates. -/
theorem Complex.logarithmicPhaseRealPhase_stationaryPacketFamilyUnion_by_frequencyCount
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b
        (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b),
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      10 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_stationaryPacketFamilyUnion_frequencyCount_le_tenTarget
      t ht ht_nonneg ha hab hlong_sqrt hderiv_growth

/-- Sample-union estimate for the right endpoint zero packet. -/
theorem Complex.logarithmicPhaseRealPhase_endpointRightZeroPacketSampleUnion_le_longTarget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖∑ n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b 0,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  match
    Complex.logarithmicPhaseRealPhase_zeroDerivPacket_eq_terminalInterval
      t ht ht_nonneg ha hab with
  | ⟨c, hc_left, hc_right, hpacket_eq⟩ =>
      have hterminal :
          ‖∑ n ∈ Finset.Icc c b,
            Complex.exp
              (Complex.I *
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
            80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
        Complex.logarithmicPhaseRealPhase_endpointRightZeroTerminalInterval_le_longTarget
          t ht ht_nonneg ha hab hc_left hc_right hlong_endpoint hderiv_growth
      exact
        Eq.subst
          (motive := fun S : Finset ℕ =>
            ‖∑ n ∈ S,
              Complex.exp
                (Complex.I *
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
              80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
          hpacket_eq.symm
          hterminal

/-- Sample-union estimate for the left endpoint packet family. -/
theorem Complex.logarithmicPhaseRealPhase_endpointLeftPacketSampleUnion_le_longTarget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b
        (Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b),
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  match
    Complex.logarithmicPhaseRealPhase_endpointLeftPacketFamilyUnion_eq_initialInterval
      t ht ht_nonneg ha hab with
  | ⟨c, hc_left, hc_right, hpacket_eq⟩ =>
      have hinitial :
          ‖∑ n ∈ Finset.Ico a c,
            Complex.exp
              (Complex.I *
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
            80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
        Complex.logarithmicPhaseRealPhase_endpointLeftInitialInterval_le_longTarget
          t ht ht_nonneg ha hab hc_left hc_right hlong_endpoint hderiv_growth
      exact
        Eq.subst
          (motive := fun S : Finset ℕ =>
            ‖∑ n ∈ S,
              Complex.exp
                (Complex.I *
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
              80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
          hpacket_eq.symm
          hinitial

/-- Sample-union estimate for the far-right endpoint packet family. -/
theorem Complex.logarithmicPhaseRealPhase_endpointFarRightPacketSampleUnion_le_longTarget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b
        (Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b),
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  match
    Complex.logarithmicPhaseRealPhase_endpointFarRightPacketFamilyUnion_eq_boundedInterval
      t ht ht_nonneg ha hab with
  | ⟨c, d, hc_left, hcd, hd_right, hpacket_eq⟩ =>
      have hinterval :
          ‖∑ n ∈ Finset.Ico c d,
            Complex.exp
              (Complex.I *
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
            80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
        Complex.logarithmicPhaseRealPhase_boundedInterval_secondDerivative_le_threeTarget
          t ht ht_nonneg ha hab hc_left hcd hd_right hlong_endpoint hderiv_growth
      exact
        Eq.subst
          (motive := fun S : Finset ℕ =>
            ‖∑ n ∈ S,
              Complex.exp
                (Complex.I *
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
              80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
          hpacket_eq.symm
          hinterval

/-- Sample-union estimate for the stationary packet family. -/
theorem Complex.logarithmicPhaseRealPhase_stationaryPacketSampleUnion_le_longTarget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b
        (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b),
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      10 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_stationaryPacketFamilyUnion_by_frequencyCount
      t ht ht_nonneg ha hab hlong_sqrt hderiv_growth

/-- An endpoint filtered packet is active. -/
theorem Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets_mem_active
    (t : ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b) :
    m ∈
      Complex.realPhase_secondDerivative_vdc_activeDerivPackets
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b :=
  (Finset.mem_filter.mp hm).1

/-- Endpoint filtered packets are exactly the active packets that fail the
negative-frequency stationary-in-interval condition. -/
theorem Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets_not_stationary
    (t : ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b) :
    ¬ ((m < 0) ∧
        Complex.logarithmicPhaseRealPhase_stationaryPoint t m ∈
          Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) :=
  (Finset.mem_filter.mp hm).2

/-- A stationary filtered packet inherits the active packet nonemptiness
witness. -/
theorem Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPacket_nonempty
    (t : ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b) :
    (Complex.realPhase_secondDerivative_vdc_derivPacket
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b m).Nonempty :=
  Complex.logarithmicPhaseRealPhase_activeDerivPacket_nonempty t
    (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets_mem_active
      t hm)

/-- An endpoint filtered packet inherits the active packet nonemptiness
witness. -/
theorem Complex.logarithmicPhaseRealPhase_endpointActiveDerivPacket_nonempty
    (t : ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b) :
    (Complex.realPhase_secondDerivative_vdc_derivPacket
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b m).Nonempty :=
  Complex.logarithmicPhaseRealPhase_activeDerivPacket_nonempty t
    (Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets_mem_active
      t hm)

/-- A stationary filtered packet inherits the existing reciprocal-curvature
cardinality packet bound.  This is only a local packet estimate; the final
stationary contribution needs the sharper stationary-phase summation over
frequencies. -/
theorem Complex.logarithmicPhaseRealPhase_stationaryActive_packetSum_le_curvatureScale_add_one
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖Complex.realPhase_secondDerivative_vdc_packetSum
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b m‖ ≤
      ((((b + 1 : ℕ) : ℝ) * (((b + 1 : ℕ) : ℝ))) / ‖t‖ + 1) :=
  Complex.logarithmicPhaseRealPhase_active_packetSum_le_curvatureScale_add_one
    t ht
    (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets_mem_active
      t hm)
    ha hab hderiv_growth

/-- An endpoint filtered packet inherits the existing reciprocal-curvature
cardinality packet bound.  This is the fallback local estimate; the endpoint
tail proof still needs the stronger endpoint-distance first-derivative
estimate. -/
theorem Complex.logarithmicPhaseRealPhase_endpointActive_packetSum_le_curvatureScale_add_one
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖Complex.realPhase_secondDerivative_vdc_packetSum
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b m‖ ≤
      ((((b + 1 : ℕ) : ℝ) * (((b + 1 : ℕ) : ℝ))) / ‖t‖ + 1) :=
  Complex.logarithmicPhaseRealPhase_active_packetSum_le_curvatureScale_add_one
    t ht
    (Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets_mem_active
      t hm)
    ha hab hderiv_growth

/-- If an endpoint packet is not in the negative stationary interval class,
then either its frequency is nonnegative or its explicit stationary point lies
outside the ambient interval. -/
theorem Complex.logarithmicPhaseRealPhase_endpointActive_index_nonneg_or_stationaryPoint_outside
    (t : ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b) :
    0 ≤ m ∨
      (m < 0 ∧
        Complex.logarithmicPhaseRealPhase_stationaryPoint t m < (a : ℝ)) ∨
        (m < 0 ∧
          ((b + 1 : ℕ) : ℝ) <
            Complex.logarithmicPhaseRealPhase_stationaryPoint t m) := by
  have hnot :
      ¬ ((m < 0) ∧
          Complex.logarithmicPhaseRealPhase_stationaryPoint t m ∈
            Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) :=
    Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets_not_stationary
      t hm
  match le_or_gt 0 m with
  | Or.inl hm_nonneg =>
      exact Or.inl hm_nonneg
  | Or.inr hm_neg =>
      have hnot_mem :
          ¬ Complex.logarithmicPhaseRealPhase_stationaryPoint t m ∈
              Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) :=
        fun hmem => hnot (And.intro hm_neg hmem)
      match
        lt_or_ge
          (Complex.logarithmicPhaseRealPhase_stationaryPoint t m)
          (a : ℝ) with
      | Or.inl hleft =>
          exact Or.inr (Or.inl (And.intro hm_neg hleft))
      | Or.inr hleft_ge =>
          have hright_not :
              ¬ Complex.logarithmicPhaseRealPhase_stationaryPoint t m ≤
                  ((b + 1 : ℕ) : ℝ) :=
            fun hright_le =>
              hnot_mem (And.intro hleft_ge hright_le)
          exact Or.inr
            (Or.inr
              (And.intro hm_neg (lt_of_not_ge hright_not)))

/-- The three endpoint-tail classes cover all endpoint active packets. -/
theorem Complex.logarithmicPhaseRealPhase_endpointActive_eq_three_tails
    (t : ℝ)
    (a b : ℕ) :
    Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b =
      Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b ∪
        (Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b ∪
          Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b) := by
  exact Finset.ext
    (fun m =>
      Iff.intro
        (fun hm =>
          match
            Complex.logarithmicPhaseRealPhase_endpointActive_index_nonneg_or_stationaryPoint_outside
              t hm with
          | Or.inl hm_nonneg =>
              Finset.mem_union.mpr
                (Or.inl
                  (Finset.mem_filter.mpr
                    (And.intro hm hm_nonneg)))
          | Or.inr (Or.inl hleft_data) =>
              Finset.mem_union.mpr
                (Or.inr
                  (Finset.mem_union.mpr
                    (Or.inl
                      (Finset.mem_filter.mpr
                        (And.intro hm hleft_data)))))
          | Or.inr (Or.inr hright_data) =>
              Finset.mem_union.mpr
                (Or.inr
                  (Finset.mem_union.mpr
                    (Or.inr
                      (Finset.mem_filter.mpr
                        (And.intro hm hright_data)))))
        (fun hm =>
          match Finset.mem_union.mp hm with
          | Or.inl hright =>
              (Finset.mem_filter.mp hright).1
          | Or.inr hrest =>
              match Finset.mem_union.mp hrest with
              | Or.inl hleft =>
                  (Finset.mem_filter.mp hleft).1
              | Or.inr hfar =>
                  (Finset.mem_filter.mp hfar).1))

/-- The nonnegative-index endpoint tail is disjoint from the negative left
endpoint tail. -/
theorem Complex.logarithmicPhaseRealPhase_endpointRight_left_disjoint
    (t : ℝ)
    (a b : ℕ) :
    Disjoint
      (Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b)
      (Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b) := by
  exact Finset.disjoint_left.mpr
    (fun m hm_right hm_left =>
      have hm_nonneg : 0 ≤ m :=
        (Finset.mem_filter.mp hm_right).2
      have hm_neg : m < 0 :=
        ((Finset.mem_filter.mp hm_left).2).1
      not_lt_of_ge hm_nonneg hm_neg)

/-- The nonnegative-index endpoint tail is disjoint from the negative
far-right endpoint tail. -/
theorem Complex.logarithmicPhaseRealPhase_endpointRight_farRight_disjoint
    (t : ℝ)
    (a b : ℕ) :
    Disjoint
      (Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b)
      (Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b) := by
  exact Finset.disjoint_left.mpr
    (fun m hm_right hm_far =>
      have hm_nonneg : 0 ≤ m :=
        (Finset.mem_filter.mp hm_right).2
      have hm_neg : m < 0 :=
        ((Finset.mem_filter.mp hm_far).2).1
      not_lt_of_ge hm_nonneg hm_neg)

/-- The two negative endpoint tails are disjoint because the left endpoint is
not to the right of `b+1`. -/
theorem Complex.logarithmicPhaseRealPhase_endpointLeft_farRight_disjoint
    (t : ℝ)
    {a b : ℕ}
    (hab : a ≤ b) :
    Disjoint
      (Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b)
      (Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b) := by
  exact Finset.disjoint_left.mpr
    (fun m hm_left hm_far =>
      have hleft :
          Complex.logarithmicPhaseRealPhase_stationaryPoint t m < (a : ℝ) :=
        ((Finset.mem_filter.mp hm_left).2).2
      have hfar :
          ((b + 1 : ℕ) : ℝ) <
            Complex.logarithmicPhaseRealPhase_stationaryPoint t m :=
        ((Finset.mem_filter.mp hm_far).2).2
      have ha_le_B : (a : ℝ) ≤ ((b + 1 : ℕ) : ℝ) :=
        Nat.cast_le.mpr (Nat.le_trans hab (Nat.le_succ b))
      have hsp_lt_B :
          Complex.logarithmicPhaseRealPhase_stationaryPoint t m <
            ((b + 1 : ℕ) : ℝ) :=
        lt_of_lt_of_le hleft ha_le_B
      not_lt_of_ge (le_of_lt hsp_lt_B) hfar)

/-- A right endpoint-tail packet is an endpoint active packet. -/
theorem Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets_mem_endpoint
    (t : ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b) :
    m ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b :=
  (Finset.mem_filter.mp hm).1

/-- A right endpoint-tail packet has nonnegative packet index. -/
theorem Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets_index_nonneg
    (t : ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b) :
    0 ≤ m :=
  (Finset.mem_filter.mp hm).2

/-- A left endpoint-tail packet is an endpoint active packet. -/
theorem Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets_mem_endpoint
    (t : ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b) :
    m ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b :=
  (Finset.mem_filter.mp hm).1

/-- A left endpoint-tail packet has negative packet index. -/
theorem Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets_index_neg
    (t : ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b) :
    m < 0 :=
  ((Finset.mem_filter.mp hm).2).1

/-- A left endpoint-tail packet has its stationary point left of the block. -/
theorem Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets_stationaryPoint_lt_left
    (t : ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b) :
    Complex.logarithmicPhaseRealPhase_stationaryPoint t m < (a : ℝ) :=
  ((Finset.mem_filter.mp hm).2).2

/-- A far-right endpoint-tail packet is an endpoint active packet. -/
theorem Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets_mem_endpoint
    (t : ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b) :
    m ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b :=
  (Finset.mem_filter.mp hm).1

/-- A far-right endpoint-tail packet has negative packet index. -/
theorem Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets_index_neg
    (t : ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b) :
    m < 0 :=
  ((Finset.mem_filter.mp hm).2).1

/-- A far-right endpoint-tail packet has its stationary point to the right of
the block. -/
theorem Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets_right_lt_stationaryPoint
    (t : ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b) :
    ((b + 1 : ℕ) : ℝ) <
      Complex.logarithmicPhaseRealPhase_stationaryPoint t m :=
  ((Finset.mem_filter.mp hm).2).2

/-- A right endpoint-tail packet is active in the original derivative-packet
decomposition. -/
theorem Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets_mem_active
    (t : ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b) :
    m ∈
      Complex.realPhase_secondDerivative_vdc_activeDerivPackets
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b :=
  Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets_mem_active t
    (Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets_mem_endpoint
      t hm)

/-- A left endpoint-tail packet is active in the original derivative-packet
decomposition. -/
theorem Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets_mem_active
    (t : ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b) :
    m ∈
      Complex.realPhase_secondDerivative_vdc_activeDerivPackets
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b :=
  Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets_mem_active t
    (Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets_mem_endpoint
      t hm)

/-- A far-right endpoint-tail packet is active in the original derivative-packet
decomposition. -/
theorem Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets_mem_active
    (t : ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b) :
    m ∈
      Complex.realPhase_secondDerivative_vdc_activeDerivPackets
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b :=
  Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets_mem_active t
    (Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets_mem_endpoint
      t hm)

/-- Right endpoint-tail packets inherit nonemptiness of the derivative packet. -/
theorem Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPacket_nonempty
    (t : ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b) :
    (Complex.realPhase_secondDerivative_vdc_derivPacket
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b m).Nonempty :=
  Complex.logarithmicPhaseRealPhase_activeDerivPacket_nonempty t
    (Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets_mem_active
      t hm)

/-- Left endpoint-tail packets inherit nonemptiness of the derivative packet. -/
theorem Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPacket_nonempty
    (t : ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b) :
    (Complex.realPhase_secondDerivative_vdc_derivPacket
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b m).Nonempty :=
  Complex.logarithmicPhaseRealPhase_activeDerivPacket_nonempty t
    (Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets_mem_active
      t hm)

/-- Far-right endpoint-tail packets inherit nonemptiness of the derivative
packet. -/
theorem Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPacket_nonempty
    (t : ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b) :
    (Complex.realPhase_secondDerivative_vdc_derivPacket
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b m).Nonempty :=
  Complex.logarithmicPhaseRealPhase_activeDerivPacket_nonempty t
    (Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets_mem_active
      t hm)

/-- Right endpoint-tail packets inherit the local reciprocal-curvature packet
bound. -/
theorem Complex.logarithmicPhaseRealPhase_endpointRightActive_packetSum_le_curvatureScale_add_one
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖Complex.realPhase_secondDerivative_vdc_packetSum
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b m‖ ≤
      ((((b + 1 : ℕ) : ℝ) * (((b + 1 : ℕ) : ℝ))) / ‖t‖ + 1) :=
  Complex.logarithmicPhaseRealPhase_active_packetSum_le_curvatureScale_add_one
    t ht
    (Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets_mem_active
      t hm)
    ha hab hderiv_growth

/-- Left endpoint-tail packets inherit the local reciprocal-curvature packet
bound. -/
theorem Complex.logarithmicPhaseRealPhase_endpointLeftActive_packetSum_le_curvatureScale_add_one
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖Complex.realPhase_secondDerivative_vdc_packetSum
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b m‖ ≤
      ((((b + 1 : ℕ) : ℝ) * (((b + 1 : ℕ) : ℝ))) / ‖t‖ + 1) :=
  Complex.logarithmicPhaseRealPhase_active_packetSum_le_curvatureScale_add_one
    t ht
    (Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets_mem_active
      t hm)
    ha hab hderiv_growth

/-- Far-right endpoint-tail packets inherit the local reciprocal-curvature
packet bound. -/
theorem Complex.logarithmicPhaseRealPhase_endpointFarRightActive_packetSum_le_curvatureScale_add_one
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖Complex.realPhase_secondDerivative_vdc_packetSum
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b m‖ ≤
      ((((b + 1 : ℕ) : ℝ) * (((b + 1 : ℕ) : ℝ))) / ‖t‖ + 1) :=
  Complex.logarithmicPhaseRealPhase_active_packetSum_le_curvatureScale_add_one
    t ht
    (Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets_mem_active
      t hm)
    ha hab hderiv_growth

/-- A right endpoint-tail packet can exist only when the right endpoint
derivative scale is at most a half-window. -/
theorem Complex.logarithmicPhaseRealPhase_endpointRightActive_endpointScale_le_half
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b) :
    ‖t‖ / (((b + 1 : ℕ) : ℝ)) ≤ (1 / 2 : ℝ) := by
  have hm_endpoint :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b :=
    Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets_mem_endpoint
      t hm
  have hm_active :
      m ∈
        Complex.realPhase_secondDerivative_vdc_activeDerivPackets
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b :=
    Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets_mem_active
      t hm_endpoint
  have hm_nonneg : 0 ≤ m :=
    Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets_index_nonneg
      t hm
  have hm_cast_nonneg : (0 : ℝ) ≤ (m : ℝ) :=
    Int.cast_nonneg.mpr hm_nonneg
  have hupper :
      (m : ℝ) ≤
        -(‖t‖ / (((b + 1 : ℕ) : ℝ))) + (1 / 2 : ℝ) :=
    Complex.logarithmicPhaseRealPhase_activeDerivPacket_index_upper
      t ht_nonneg ha hm_active
  have hzero_le :
      (0 : ℝ) ≤ -(‖t‖ / (((b + 1 : ℕ) : ℝ))) + (1 / 2 : ℝ) :=
    le_trans hm_cast_nonneg hupper
  let scale : ℝ := ‖t‖ / (((b + 1 : ℕ) : ℝ))
  have hplus :
      scale + 0 ≤ scale + (-scale + (1 / 2 : ℝ)) :=
    add_le_add_left hzero_le scale
  have hcollapse :
      scale + (-scale + (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by
    calc
      scale + (-scale + (1 / 2 : ℝ)) =
          (scale + -scale) + (1 / 2 : ℝ) :=
        (add_assoc scale (-scale) (1 / 2 : ℝ)).symm
      _ = 0 + (1 / 2 : ℝ) := by
        exact congrArg (fun r : ℝ => r + (1 / 2 : ℝ))
          (add_neg_cancel scale)
      _ = (1 / 2 : ℝ) :=
        zero_add (1 / 2 : ℝ)
  exact
    Eq.subst
      (motive := fun right : ℝ => scale ≤ right)
      hcollapse
      (Eq.subst
        (motive := fun left : ℝ =>
          left ≤ scale + (-scale + (1 / 2 : ℝ)))
        (add_zero scale)
        hplus)

/-- A right endpoint-tail packet has packet index zero. -/
theorem Complex.logarithmicPhaseRealPhase_endpointRightActive_index_eq_zero
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b) :
    m = 0 := by
  have hm_nonneg : 0 ≤ m :=
    Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets_index_nonneg
      t hm
  let scale : ℝ := ‖t‖ / (((b + 1 : ℕ) : ℝ))
  have hscale_nonneg : 0 ≤ scale := by
    show 0 ≤ ‖t‖ / (((b + 1 : ℕ) : ℝ))
    have hnorm_nonneg : 0 ≤ ‖t‖ :=
      norm_nonneg t
    have hden_nonneg : 0 ≤ (((b + 1 : ℕ) : ℝ)) :=
      Nat.cast_nonneg (b + 1)
    exact div_nonneg hnorm_nonneg hden_nonneg
  have hupper :
      (m : ℝ) ≤ -scale + (1 / 2 : ℝ) :=
    Complex.logarithmicPhaseRealPhase_activeDerivPacket_index_upper
      t ht_nonneg ha
      (Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets_mem_active
        t hm)
  have hupper_half :
      (m : ℝ) ≤ (1 / 2 : ℝ) :=
    le_trans hupper
      (add_le_of_nonpos_left (neg_nonpos.mpr hscale_nonneg))
  have hhalf_lt_one : (1 / 2 : ℝ) < 1 :=
    one_half_lt_one
    have hm_cast_lt_one : (m : ℝ) < 1 :=
      lt_of_le_of_lt hupper_half hhalf_lt_one
    have hm_lt_one : m < 1 :=
      Int.cast_lt.mp
        (show (m : ℝ) < ((1 : ℤ) : ℝ) from hm_cast_lt_one)
  have hm_le_zero : m ≤ 0 :=
    Int.lt_add_one_iff.mp hm_lt_one
  exact le_antisymm hm_le_zero hm_nonneg

/-- The right endpoint-tail packet sum is controlled by the single zero
derivative-frequency packet. -/
theorem Complex.logarithmicPhaseRealPhase_endpointRightPacket_sum_norm_le_zero_packet
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a) :
    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      ‖Complex.realPhase_secondDerivative_vdc_packetSum
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b 0‖ := by
  let S :=
    Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b
  let F : ℤ → ℂ :=
    fun m =>
      Complex.realPhase_secondDerivative_vdc_packetSum
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m
  by_cases hzero : (0 : ℤ) ∈ S
  · have hS_singleton :
        S = ({(0 : ℤ)} : Finset ℤ) :=
      Finset.ext
        (fun m =>
          Iff.intro
            (fun hm =>
              have hm_zero : m = 0 :=
                Complex.logarithmicPhaseRealPhase_endpointRightActive_index_eq_zero
                  t ht_nonneg ha hm
              Eq.subst
                (motive := fun z : ℤ => z ∈ ({(0 : ℤ)} : Finset ℤ))
                hm_zero.symm
                (Finset.mem_singleton_self (0 : ℤ)))
            (fun hm_singleton =>
              have hm_zero : m = 0 :=
                Finset.mem_singleton.mp hm_singleton
              Eq.subst
                (motive := fun z : ℤ => z ∈ S)
                hm_zero.symm
                hzero))
    have hsum :
        (∑ m ∈ S, F m) = F 0 :=
      Eq.trans
        (congrArg (fun U : Finset ℤ => ∑ m ∈ U, F m) hS_singleton)
        (Finset.sum_singleton F 0)
    exact
      Eq.subst
        (motive := fun z : ℂ => ‖z‖ ≤ ‖F 0‖)
        hsum.symm
        (le_refl ‖F 0‖)
  · have hS_empty :
        S = (∅ : Finset ℤ) :=
      Finset.ext
        (fun m =>
          Iff.intro
            (fun hm =>
              have hm_zero : m = 0 :=
                Complex.logarithmicPhaseRealPhase_endpointRightActive_index_eq_zero
                  t ht_nonneg ha hm
              have hzero_mem : (0 : ℤ) ∈ S :=
                Eq.subst
                  (motive := fun z : ℤ => z ∈ S)
                  hm_zero
                  hm
              False.elim (hzero hzero_mem))
            (fun hm_empty =>
              False.elim (Finset.not_mem_empty m hm_empty)))
    have hsum :
        (∑ m ∈ S, F m) = 0 :=
      Eq.trans
        (congrArg (fun U : Finset ℤ => ∑ m ∈ U, F m) hS_empty)
        (Finset.sum_empty)
    have hzero_norm : ‖(0 : ℂ)‖ ≤ ‖F 0‖ :=
      Eq.subst
        (motive := fun left : ℝ => left ≤ ‖F 0‖)
        (norm_zero : ‖(0 : ℂ)‖ = 0)
        (norm_nonneg (F 0))
    exact
      Eq.subst
        (motive := fun z : ℂ => ‖z‖ ≤ ‖F 0‖)
        hsum.symm
        hzero_norm

/-- A sample in the zero derivative-frequency packet lies to the right of the
point where the endpoint derivative scale drops to one half. -/
theorem Complex.logarithmicPhaseRealPhase_zeroDerivPacket_sample_endpointScale_le_half
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b n : ℕ}
    (ha : 1 ≤ a)
    (hn :
      n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b 0) :
    ‖t‖ / (n : ℝ) ≤ (1 / 2 : ℝ) := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  have hn_block : n ∈ Finset.Icc a b :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block φ hn
  have hn_one : 1 ≤ n :=
    le_trans ha (Finset.mem_Icc.mp hn_block).1
  have hn_pos : 0 < n :=
    Nat.lt_of_succ_le hn_one
  have hwindow_lower :
      ((0 : ℤ) : ℝ) - (1 / 2 : ℝ) ≤ deriv φ n :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_lower φ hn
  have hleft :
      ((0 : ℤ) : ℝ) - (1 / 2 : ℝ) = -(1 / 2 : ℝ) := by
    calc
      ((0 : ℤ) : ℝ) - (1 / 2 : ℝ) =
          (0 : ℝ) - (1 / 2 : ℝ) := by
        exact congrArg (fun r : ℝ => r - (1 / 2 : ℝ)) Int.cast_zero
      _ = -(1 / 2 : ℝ) :=
        zero_sub (1 / 2 : ℝ)
  have hderiv :
      deriv φ n = -(‖t‖ / (n : ℝ)) :=
    Complex.logarithmicPhaseRealPhase_deriv_eq_neg_norm_div_parenthesized
      t ht_nonneg (Nat.cast_pos.mpr hn_pos)
  have hneg :
      -(1 / 2 : ℝ) ≤ -(‖t‖ / (n : ℝ)) :=
    Eq.subst
      (motive := fun right : ℝ => -(1 / 2 : ℝ) ≤ right)
      hderiv
      (Eq.subst
        (motive := fun left : ℝ => left ≤ deriv φ n)
        hleft
        hwindow_lower)
  have hflipped :
      - (-(‖t‖ / (n : ℝ))) ≤ - (-(1 / 2 : ℝ)) :=
    neg_le_neg hneg
  have hleft_neg :
      - (-(‖t‖ / (n : ℝ))) = ‖t‖ / (n : ℝ) :=
    neg_neg (‖t‖ / (n : ℝ))
  have hright_neg :
      - (-(1 / 2 : ℝ)) = (1 / 2 : ℝ) :=
    neg_neg (1 / 2 : ℝ)
  exact
    Eq.subst
      (motive := fun left : ℝ => left ≤ (1 / 2 : ℝ))
      hleft_neg
      (Eq.subst
        (motive := fun right : ℝ =>
          - (-(‖t‖ / (n : ℝ))) ≤ right)
        hright_neg
        hflipped)

/-- Real endpoint-cut form of the zero derivative-frequency packet condition. -/
theorem Complex.logarithmicPhaseRealPhase_zeroDerivPacket_sample_twice_norm_le
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b n : ℕ}
    (ha : 1 ≤ a)
    (hn :
      n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b 0) :
    2 * ‖t‖ ≤ (n : ℝ) := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  have hn_block : n ∈ Finset.Icc a b :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block φ hn
  have hn_one : 1 ≤ n :=
    le_trans ha (Finset.mem_Icc.mp hn_block).1
  have hn_pos_nat : 0 < n :=
    Nat.lt_of_succ_le hn_one
  have hn_pos : 0 < (n : ℝ) :=
    Nat.cast_pos.mpr hn_pos_nat
  have hscale :
      ‖t‖ / (n : ℝ) ≤ (1 / 2 : ℝ) :=
    Complex.logarithmicPhaseRealPhase_zeroDerivPacket_sample_endpointScale_le_half
      t ht_nonneg ha hn
  have hmul :
      ‖t‖ ≤ (1 / 2 : ℝ) * (n : ℝ) :=
    (div_le_iff₀ hn_pos).mp hscale
  have htwice :
      2 * ‖t‖ ≤ 2 * ((1 / 2 : ℝ) * (n : ℝ)) :=
    mul_le_mul_of_nonneg_left hmul zero_le_two
  have hcollapse :
      2 * ((1 / 2 : ℝ) * (n : ℝ)) = (n : ℝ) := by
    have hcoef : (2 : ℝ) * (1 / 2 : ℝ) = 1 := by
      calc
        (2 : ℝ) * (1 / 2 : ℝ) =
            (1 / 2 : ℝ) + (1 / 2 : ℝ) :=
          two_mul (1 / 2 : ℝ)
        _ = 1 :=
          add_halves (1 : ℝ)
    calc
      2 * ((1 / 2 : ℝ) * (n : ℝ)) =
          ((2 : ℝ) * (1 / 2 : ℝ)) * (n : ℝ) :=
        mul_assoc 2 (1 / 2 : ℝ) (n : ℝ)
      _ = 1 * (n : ℝ) := by
        exact congrArg (fun r : ℝ => r * (n : ℝ)) hcoef
      _ = (n : ℝ) :=
        one_mul (n : ℝ)
  exact
    Eq.subst
      (motive := fun right : ℝ => 2 * ‖t‖ ≤ right)
      hcollapse
      htwice

/-- The zero derivative-frequency packet is contained in the terminal endpoint
cut selected by `2‖t‖ ≤ n`. -/
theorem Complex.logarithmicPhaseRealPhase_zeroDerivPacket_subset_terminalCut
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a) :
    Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b 0 ⊆
      (Finset.Icc a b).filter
        (fun n : ℕ => 2 * ‖t‖ ≤ (n : ℝ)) := by
  intro n hn
  have hn_block :
      n ∈ Finset.Icc a b :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      hn
  have hn_cut :
      2 * ‖t‖ ≤ (n : ℝ) :=
    Complex.logarithmicPhaseRealPhase_zeroDerivPacket_sample_twice_norm_le
      t ht_nonneg ha hn
  exact Finset.mem_filter.mpr (And.intro hn_block hn_cut)

/-- The right endpoint zero derivative-frequency packet is controlled by the
endpoint contribution budget.

This is the endpoint first-derivative/Kusmin-Landau estimate specialized to the
only right-tail frequency that can occur in the positive long branch. -/
theorem Complex.logarithmicPhaseRealPhase_endpointRightZeroPacketContribution_le_longTarget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖Complex.realPhase_secondDerivative_vdc_packetSum
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b 0‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_endpointRightZeroPacketSampleUnion_le_longTarget
      t ht ht_nonneg ha hab hlong_endpoint hderiv_growth

/-- Left endpoint-tail packet sums reduce to the sharp endpoint
first-derivative estimate on the initial endpoint interval selected by the
packet cut. -/
theorem Complex.logarithmicPhaseRealPhase_endpointLeftPacketContribution_by_endpointInterval
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  have hnorm :
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ =
      ‖∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b
          (Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b),
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ :=
    congrArg norm
      (Complex.realPhase_secondDerivative_vdc_packetFamilyUnion_sum_eq_packetSums
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        (fun m hm =>
          Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets_mem_active
            t hm)).symm
  exact
    Eq.subst
      (motive := fun left : ℝ =>
        left ≤ 80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
      hnorm.symm
      (Complex.logarithmicPhaseRealPhase_endpointLeftPacketSampleUnion_le_longTarget
        t ht ht_nonneg ha hab hlong_endpoint hderiv_growth)

/-- Far-right endpoint-tail packet sums reduce to the sharp endpoint
first-derivative estimate on the terminal endpoint interval selected by the
packet cut. -/
theorem Complex.logarithmicPhaseRealPhase_endpointFarRightPacketContribution_by_endpointInterval
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  have hnorm :
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ =
      ‖∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b
          (Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b),
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ :=
    congrArg norm
      (Complex.realPhase_secondDerivative_vdc_packetFamilyUnion_sum_eq_packetSums
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        (fun m hm =>
          Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets_mem_active
            t hm)).symm
  exact
    Eq.subst
      (motive := fun left : ℝ =>
        left ≤ 80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
      hnorm.symm
      (Complex.logarithmicPhaseRealPhase_endpointFarRightPacketSampleUnion_le_longTarget
        t ht ht_nonneg ha hab hlong_endpoint hderiv_growth)

/-- Stationary packets are controlled by the square-root frequency budget:
the number of stationary derivative-frequency packets is at most the Weyl
length, and each such packet contributes through the local B-process packet
estimate. -/
theorem Complex.logarithmicPhaseRealPhase_stationaryPacketContribution_by_frequencyCount
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      10 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_stationaryPacketSum_frequencyCount_le_tenTarget
      t ht ht_nonneg ha hab hlong_sqrt hderiv_growth

/-- Left endpoint-tail packet indices lie within the half-window immediately
below the left endpoint derivative frequency. -/
theorem Complex.logarithmicPhaseRealPhase_endpointLeftActive_index_lt_leftEndpoint
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b) :
    (m : ℝ) < -(‖t‖ / (a : ℝ)) := by
  have hm_neg :
      m < 0 :=
    Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets_index_neg
      t hm
  have hsp_left :
      Complex.logarithmicPhaseRealPhase_stationaryPoint t m < (a : ℝ) :=
    Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets_stationaryPoint_lt_left
      t hm
  have hden_pos : 0 < -(m : ℝ) :=
    Int.neg_cast_pos_of_lt_zero hm_neg
  have hT_pos : 0 < ‖t‖ :=
    lt_of_lt_of_le zero_lt_one ht
  have ha_pos : 0 < (a : ℝ) :=
    lt_trans
      (Complex.logarithmicPhaseRealPhase_stationaryPoint_pos t ht hm_neg)
      hsp_left
  have hdiv_lt :
      ‖t‖ / (-(m : ℝ)) < (a : ℝ) := by
    exact hsp_left
  have hT_lt :
      ‖t‖ < (a : ℝ) * (-(m : ℝ)) :=
    (div_lt_iff₀ hden_pos).mp hdiv_lt
  have hdiv_left :
      ‖t‖ / (a : ℝ) < -(m : ℝ) :=
    (div_lt_iff₀ ha_pos).mpr
      (Eq.subst
        (motive := fun right : ℝ => ‖t‖ < right)
        (mul_comm (a : ℝ) (-(m : ℝ)))
        hT_lt)
  have hneg :
      - (-(m : ℝ)) < -(‖t‖ / (a : ℝ)) :=
    neg_lt_neg hdiv_left
  exact
    Eq.subst
      (motive := fun left : ℝ => left < -(‖t‖ / (a : ℝ)))
      (neg_neg (m : ℝ))
      hneg

/-- A sample in a left endpoint-tail packet has reciprocal scale still above
the left endpoint scale, up to the packet half-window. -/
theorem Complex.logarithmicPhaseRealPhase_endpointLeftPacket_sample_scale_lower
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b n : ℕ}
    {m : ℤ}
    (ha : 1 ≤ a)
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b)
    (hn :
      n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m) :
    ‖t‖ / (a : ℝ) - (1 / 2 : ℝ) < ‖t‖ / (n : ℝ) := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  have hn_block : n ∈ Finset.Icc a b :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block φ hn
  have hn_one : 1 ≤ n :=
    le_trans ha (Finset.mem_Icc.mp hn_block).1
  have hn_pos : 0 < n :=
    Nat.lt_of_succ_le hn_one
  have hindex :
      (m : ℝ) < -(‖t‖ / (a : ℝ)) :=
    Complex.logarithmicPhaseRealPhase_endpointLeftActive_index_lt_leftEndpoint
      t ht hm
  have hupper_packet :
      deriv φ n < (m : ℝ) + (1 / 2 : ℝ) :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_upper φ hn
  have hcenter_lt :
      (m : ℝ) + (1 / 2 : ℝ) <
        -(‖t‖ / (a : ℝ)) + (1 / 2 : ℝ) :=
    add_lt_add_right hindex (1 / 2 : ℝ)
  have hderiv_lt :
      deriv φ n < -(‖t‖ / (a : ℝ)) + (1 / 2 : ℝ) :=
    lt_trans hupper_packet hcenter_lt
  have hderiv :
      deriv φ n = -(‖t‖ / (n : ℝ)) :=
    Complex.logarithmicPhaseRealPhase_deriv_eq_neg_norm_div_parenthesized
      t ht_nonneg (Nat.cast_pos.mpr hn_pos)
  have hneg_lt :
      -(‖t‖ / (n : ℝ)) < -(‖t‖ / (a : ℝ)) + (1 / 2 : ℝ) :=
    Eq.subst
      (motive := fun left : ℝ =>
        left < -(‖t‖ / (a : ℝ)) + (1 / 2 : ℝ))
      hderiv
      hderiv_lt
  have hflipped :
      - (-(‖t‖ / (a : ℝ)) + (1 / 2 : ℝ)) < - (-(‖t‖ / (n : ℝ))) :=
    neg_lt_neg hneg_lt
  have hleft :
      - (-(‖t‖ / (a : ℝ)) + (1 / 2 : ℝ)) =
        ‖t‖ / (a : ℝ) - (1 / 2 : ℝ) := by
    calc
      - (-(‖t‖ / (a : ℝ)) + (1 / 2 : ℝ)) =
          - (-(‖t‖ / (a : ℝ))) - (1 / 2 : ℝ) :=
        neg_add (-(‖t‖ / (a : ℝ))) (1 / 2 : ℝ)
      _ = ‖t‖ / (a : ℝ) - (1 / 2 : ℝ) := by
        exact congrArg (fun r : ℝ => r - (1 / 2 : ℝ))
          (neg_neg (‖t‖ / (a : ℝ)))
  have hright :
      - (-(‖t‖ / (n : ℝ))) = ‖t‖ / (n : ℝ) :=
    neg_neg (‖t‖ / (n : ℝ))
  exact
    Eq.subst
      (motive := fun left : ℝ => left < ‖t‖ / (n : ℝ))
      hleft
      (Eq.subst
        (motive := fun right : ℝ =>
          - (-(‖t‖ / (a : ℝ)) + (1 / 2 : ℝ)) < right)
        hright
        hflipped)

/-- The left endpoint packet-family union is contained in the corresponding
left reciprocal-scale cut. -/
theorem Complex.logarithmicPhaseRealPhase_endpointLeftPacketFamilyUnion_subset_scaleCut
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a) :
    Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b
        (Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b)
      ⊆
      (Finset.Icc a b).filter
        (fun n : ℕ =>
          ‖t‖ / (a : ℝ) - (1 / 2 : ℝ) < ‖t‖ / (n : ℝ)) := by
  intro n hn
  have hmember :
      ∃ m : ℤ,
        m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b ∧
          n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m :=
    Finset.mem_biUnion.mp hn
  match hmember with
  | ⟨m, hm, hn_packet⟩ =>
      have hn_block :
          n ∈ Finset.Icc a b :=
        Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          hn_packet
      have hcut :
          ‖t‖ / (a : ℝ) - (1 / 2 : ℝ) < ‖t‖ / (n : ℝ) :=
        Complex.logarithmicPhaseRealPhase_endpointLeftPacket_sample_scale_lower
          t ht ht_nonneg ha hm hn_packet
      exact Finset.mem_filter.mpr (And.intro hn_block hcut)

/-- Far-right endpoint-tail packet indices lie above the right endpoint
derivative frequency. -/
theorem Complex.logarithmicPhaseRealPhase_endpointFarRightActive_rightEndpoint_lt_index
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b) :
    -(‖t‖ / (((b + 1 : ℕ) : ℝ))) < (m : ℝ) := by
  have hm_neg :
      m < 0 :=
    Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets_index_neg
      t hm
  have hright_sp :
      ((b + 1 : ℕ) : ℝ) <
        Complex.logarithmicPhaseRealPhase_stationaryPoint t m :=
    Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets_right_lt_stationaryPoint
      t hm
  have hden_pos : 0 < -(m : ℝ) :=
    Int.neg_cast_pos_of_lt_zero hm_neg
  have hB_pos : 0 < (((b + 1 : ℕ) : ℝ)) :=
    Nat.cast_pos.mpr (Nat.succ_pos b)
  have hB_lt :
      ((b + 1 : ℕ) : ℝ) < ‖t‖ / (-(m : ℝ)) := by
    exact hright_sp
  have hprod_lt :
      ((b + 1 : ℕ) : ℝ) * (-(m : ℝ)) < ‖t‖ :=
    (lt_div_iff₀ hden_pos).mp hB_lt
  have hneg_lt :
      -(m : ℝ) < ‖t‖ / (((b + 1 : ℕ) : ℝ)) :=
    (lt_div_iff₀ hB_pos).mpr
      (Eq.subst
        (motive := fun left : ℝ => left < ‖t‖)
        (mul_comm (((b + 1 : ℕ) : ℝ)) (-(m : ℝ)))
        hprod_lt)
  have hneg :
      -(‖t‖ / (((b + 1 : ℕ) : ℝ))) < -(-(m : ℝ)) :=
    neg_lt_neg hneg_lt
  exact
    Eq.subst
      (motive := fun right : ℝ =>
        -(‖t‖ / (((b + 1 : ℕ) : ℝ))) < right)
      (neg_neg (m : ℝ))
      hneg

/-- A sample in a far-right endpoint-tail packet has reciprocal scale below the
right endpoint scale, up to the packet half-window. -/
theorem Complex.logarithmicPhaseRealPhase_endpointFarRightPacket_sample_scale_upper
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b n : ℕ}
    {m : ℤ}
    (ha : 1 ≤ a)
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b)
    (hn :
      n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m) :
    ‖t‖ / (n : ℝ) <
      ‖t‖ / (((b + 1 : ℕ) : ℝ)) + (1 / 2 : ℝ) := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  have hn_block : n ∈ Finset.Icc a b :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block φ hn
  have hn_one : 1 ≤ n :=
    le_trans ha (Finset.mem_Icc.mp hn_block).1
  have hn_pos : 0 < n :=
    Nat.lt_of_succ_le hn_one
  have hindex :
      -(‖t‖ / (((b + 1 : ℕ) : ℝ))) < (m : ℝ) :=
    Complex.logarithmicPhaseRealPhase_endpointFarRightActive_rightEndpoint_lt_index
      t ht hm
  have hlower_packet :
      (m : ℝ) - (1 / 2 : ℝ) ≤ deriv φ n :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_lower φ hn
  have hcenter_lt :
      -(‖t‖ / (((b + 1 : ℕ) : ℝ))) - (1 / 2 : ℝ) <
        (m : ℝ) - (1 / 2 : ℝ) :=
    sub_lt_sub_right hindex (1 / 2 : ℝ)
  have hlt_deriv :
      -(‖t‖ / (((b + 1 : ℕ) : ℝ))) - (1 / 2 : ℝ) < deriv φ n :=
    lt_of_lt_of_le hcenter_lt hlower_packet
  have hderiv :
      deriv φ n = -(‖t‖ / (n : ℝ)) :=
    Complex.logarithmicPhaseRealPhase_deriv_eq_neg_norm_div_parenthesized
      t ht_nonneg (Nat.cast_pos.mpr hn_pos)
  have hlt_neg :
      -(‖t‖ / (((b + 1 : ℕ) : ℝ))) - (1 / 2 : ℝ) <
        -(‖t‖ / (n : ℝ)) :=
    Eq.subst
      (motive := fun right : ℝ =>
        -(‖t‖ / (((b + 1 : ℕ) : ℝ))) - (1 / 2 : ℝ) < right)
      hderiv
      hlt_deriv
  have hflipped :
      - (-(‖t‖ / (n : ℝ))) <
        - (-(‖t‖ / (((b + 1 : ℕ) : ℝ))) - (1 / 2 : ℝ)) :=
    neg_lt_neg hlt_neg
  have hleft :
      - (-(‖t‖ / (n : ℝ))) = ‖t‖ / (n : ℝ) :=
    neg_neg (‖t‖ / (n : ℝ))
  have hright :
      - (-(‖t‖ / (((b + 1 : ℕ) : ℝ))) - (1 / 2 : ℝ)) =
        ‖t‖ / (((b + 1 : ℕ) : ℝ)) + (1 / 2 : ℝ) := by
    calc
      - (-(‖t‖ / (((b + 1 : ℕ) : ℝ))) - (1 / 2 : ℝ)) =
          - (-(‖t‖ / (((b + 1 : ℕ) : ℝ))) + -(1 / 2 : ℝ)) := by
        exact congrArg Neg.neg
          (sub_eq_add_neg (-(‖t‖ / (((b + 1 : ℕ) : ℝ)))) (1 / 2 : ℝ))
      _ =
          - (-(‖t‖ / (((b + 1 : ℕ) : ℝ)))) - (-(1 / 2 : ℝ)) :=
        neg_add (-(‖t‖ / (((b + 1 : ℕ) : ℝ)))) (-(1 / 2 : ℝ))
      _ =
          ‖t‖ / (((b + 1 : ℕ) : ℝ)) - (-(1 / 2 : ℝ)) := by
        exact congrArg (fun r : ℝ => r - (-(1 / 2 : ℝ)))
          (neg_neg (‖t‖ / (((b + 1 : ℕ) : ℝ))))
      _ =
          ‖t‖ / (((b + 1 : ℕ) : ℝ)) + (1 / 2 : ℝ) :=
        sub_neg_eq_add (‖t‖ / (((b + 1 : ℕ) : ℝ))) (1 / 2 : ℝ)
  exact
    Eq.subst
      (motive := fun left : ℝ =>
        left < ‖t‖ / (((b + 1 : ℕ) : ℝ)) + (1 / 2 : ℝ))
      hleft
      (Eq.subst
        (motive := fun right : ℝ =>
          - (-(‖t‖ / (n : ℝ))) < right)
        hright
        hflipped)

/-- The far-right endpoint packet-family union is contained in the corresponding
right reciprocal-scale cut. -/
theorem Complex.logarithmicPhaseRealPhase_endpointFarRightPacketFamilyUnion_subset_scaleCut
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a) :
    Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b
        (Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b)
      ⊆
      (Finset.Icc a b).filter
        (fun n : ℕ =>
          ‖t‖ / (n : ℝ) <
            ‖t‖ / (((b + 1 : ℕ) : ℝ)) + (1 / 2 : ℝ)) := by
  intro n hn
  have hmember :
      ∃ m : ℤ,
        m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b ∧
          n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m :=
    Finset.mem_biUnion.mp hn
  match hmember with
  | ⟨m, hm, hn_packet⟩ =>
      have hn_block :
          n ∈ Finset.Icc a b :=
        Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          hn_packet
      have hcut :
          ‖t‖ / (n : ℝ) <
            ‖t‖ / (((b + 1 : ℕ) : ℝ)) + (1 / 2 : ℝ) :=
        Complex.logarithmicPhaseRealPhase_endpointFarRightPacket_sample_scale_upper
          t ht ht_nonneg ha hm hn_packet
      exact Finset.mem_filter.mpr (And.intro hn_block hcut)

/-- Finite majorant assembly over an arbitrary finite packet-index set.  This
is the common triangle-inequality spine for endpoint and stationary
subfamilies. -/
theorem Complex.logarithmicPhaseRealPhase_packetSet_sum_bound_of_majorants
    (t : ℝ)
    {a b : ℕ}
    (packets : Finset ℤ)
    (majorant : ℤ → ℝ)
    (hpacket :
      ∀ m : ℤ,
        m ∈ packets →
          ‖Complex.realPhase_secondDerivative_vdc_packetSum
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m‖ ≤ majorant m)
    {target : ℝ}
    (hsum :
      (∑ m ∈ packets, majorant m) ≤ target) :
    ‖∑ m ∈ packets,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤ target := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  have htriangle :
      ‖∑ m ∈ packets,
        Complex.realPhase_secondDerivative_vdc_packetSum φ a b m‖ ≤
        ∑ m ∈ packets,
          ‖Complex.realPhase_secondDerivative_vdc_packetSum φ a b m‖ :=
    norm_sum_le
      packets
      (fun m : ℤ =>
        Complex.realPhase_secondDerivative_vdc_packetSum φ a b m)
  have hpoint :
      (∑ m ∈ packets,
        ‖Complex.realPhase_secondDerivative_vdc_packetSum φ a b m‖) ≤
        ∑ m ∈ packets, majorant m :=
    Finset.sum_le_sum
      (fun m hm => hpacket m hm)
  exact le_trans htriangle (le_trans hpoint hsum)

/-- Finite assembly lemma for the endpoint-tail packet contribution.  The
analytic work is precisely the pointwise endpoint-tail majorant and the
summed-majorant bound. -/
theorem Complex.logarithmicPhaseRealPhase_endpointActivePackets_sum_bound_of_majorants
    (t : ℝ)
    {a b : ℕ}
    (majorant : ℤ → ℝ)
    (_hmajorant_nonneg :
      ∀ m : ℤ,
        m ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b →
          0 ≤ majorant m)
    (hpacket :
      ∀ m : ℤ,
        m ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b →
          ‖Complex.realPhase_secondDerivative_vdc_packetSum
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m‖ ≤ majorant m)
    {target : ℝ}
    (hsum :
      (∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b,
        majorant m) ≤ target) :
    ‖∑ m ∈
      Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤ target := by
  exact
    Complex.logarithmicPhaseRealPhase_packetSet_sum_bound_of_majorants
      t
      (Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b)
      majorant
      hpacket
      hsum

/-- Finite assembly lemma for the stationary packet contribution.  The
analytic work is precisely the local stationary-phase majorant and its
summation over stationary frequencies. -/
theorem Complex.logarithmicPhaseRealPhase_stationaryActivePackets_sum_bound_of_majorants
    (t : ℝ)
    {a b : ℕ}
    (majorant : ℤ → ℝ)
    (_hmajorant_nonneg :
      ∀ m : ℤ,
        m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b →
          0 ≤ majorant m)
    (hpacket :
      ∀ m : ℤ,
        m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b →
          ‖Complex.realPhase_secondDerivative_vdc_packetSum
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m‖ ≤ majorant m)
    {target : ℝ}
    (hsum :
      (∑ m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b,
        majorant m) ≤ target) :
    ‖∑ m ∈
      Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤ target := by
  exact
    Complex.logarithmicPhaseRealPhase_packetSet_sum_bound_of_majorants
      t
      (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b)
      majorant
      hpacket
      hsum

/-- Stationary packet sums are the sample sum over the stationary packet
family union. -/
theorem Complex.logarithmicPhaseRealPhase_stationaryPacketFamilyUnion_sum_eq
    (t : ℝ)
    (a b : ℕ) :
    (∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b
        (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b),
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))) =
    ∑ m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b,
      Complex.realPhase_secondDerivative_vdc_packetSum
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m := by
  exact
    Complex.realPhase_secondDerivative_vdc_packetFamilyUnion_sum_eq_packetSums
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      (fun m hm =>
        Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets_mem_active
          t hm)

/-- Right endpoint-tail packet sums are the sample sum over the right endpoint
packet-family union. -/
theorem Complex.logarithmicPhaseRealPhase_endpointRightPacketFamilyUnion_sum_eq
    (t : ℝ)
    (a b : ℕ) :
    (∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b
        (Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b),
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))) =
    ∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b,
      Complex.realPhase_secondDerivative_vdc_packetSum
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m := by
  exact
    Complex.realPhase_secondDerivative_vdc_packetFamilyUnion_sum_eq_packetSums
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      (fun m hm =>
        Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets_mem_active
          t hm)

/-- Left endpoint-tail packet sums are the sample sum over the left endpoint
packet-family union. -/
theorem Complex.logarithmicPhaseRealPhase_endpointLeftPacketFamilyUnion_sum_eq
    (t : ℝ)
    (a b : ℕ) :
    (∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b
        (Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b),
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))) =
    ∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b,
      Complex.realPhase_secondDerivative_vdc_packetSum
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m := by
  exact
    Complex.realPhase_secondDerivative_vdc_packetFamilyUnion_sum_eq_packetSums
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      (fun m hm =>
        Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets_mem_active
          t hm)

/-- Far-right endpoint-tail packet sums are the sample sum over the far-right
endpoint packet-family union. -/
theorem Complex.logarithmicPhaseRealPhase_endpointFarRightPacketFamilyUnion_sum_eq
    (t : ℝ)
    (a b : ℕ) :
    (∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b
        (Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b),
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))) =
    ∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b,
      Complex.realPhase_secondDerivative_vdc_packetSum
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m := by
  exact
    Complex.realPhase_secondDerivative_vdc_packetFamilyUnion_sum_eq_packetSums
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      (fun m hm =>
        Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets_mem_active
          t hm)

/-- Norm form of the right endpoint packet-family sample-union expansion. -/
theorem Complex.logarithmicPhaseRealPhase_endpointRightPacketFamilyUnion_norm_eq
    (t : ℝ)
    (a b : ℕ) :
    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b,
      Complex.realPhase_secondDerivative_vdc_packetSum
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m‖ =
    ‖∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b
        (Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b),
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ := by
  exact congrArg norm
    (Complex.logarithmicPhaseRealPhase_endpointRightPacketFamilyUnion_sum_eq
      t a b).symm

/-- Norm form of the left endpoint packet-family sample-union expansion. -/
theorem Complex.logarithmicPhaseRealPhase_endpointLeftPacketFamilyUnion_norm_eq
    (t : ℝ)
    (a b : ℕ) :
    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b,
      Complex.realPhase_secondDerivative_vdc_packetSum
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m‖ =
    ‖∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b
        (Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b),
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ := by
  exact congrArg norm
    (Complex.logarithmicPhaseRealPhase_endpointLeftPacketFamilyUnion_sum_eq
      t a b).symm

/-- Norm form of the far-right endpoint packet-family sample-union expansion. -/
theorem Complex.logarithmicPhaseRealPhase_endpointFarRightPacketFamilyUnion_norm_eq
    (t : ℝ)
    (a b : ℕ) :
    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b,
      Complex.realPhase_secondDerivative_vdc_packetSum
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m‖ =
    ‖∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b
        (Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b),
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ := by
  exact congrArg norm
    (Complex.logarithmicPhaseRealPhase_endpointFarRightPacketFamilyUnion_sum_eq
      t a b).symm

/-- Norm form of the stationary packet-family sample-union expansion. -/
theorem Complex.logarithmicPhaseRealPhase_stationaryPacketFamilyUnion_norm_eq
    (t : ℝ)
    (a b : ℕ) :
    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b,
      Complex.realPhase_secondDerivative_vdc_packetSum
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m‖ =
    ‖∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b
        (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b),
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ := by
  exact congrArg norm
    (Complex.logarithmicPhaseRealPhase_stationaryPacketFamilyUnion_sum_eq
      t a b).symm

/-- The active derivative-packet reconstruction splits the logarithmic block
into its stationary and endpoint packet contributions. -/
theorem Complex.logarithmicPhaseRealPhase_block_norm_le_stationary_endpoint_packet_norms
    (t : ℝ)
    (a b : ℕ) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ +
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  let stationary : Finset ℤ :=
    Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b
  let endpoint : Finset ℤ :=
    Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b
  let packet : ℤ → ℂ :=
    fun m : ℤ => Complex.realPhase_secondDerivative_vdc_packetSum φ a b m
  have hpartition :
      Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b =
        stationary ∪ endpoint :=
    Complex.logarithmicPhaseRealPhase_activeDerivPackets_eq_stationary_union_endpoint
      t a b
  have hdisjoint : Disjoint stationary endpoint :=
    Complex.logarithmicPhaseRealPhase_stationary_endpoint_disjoint t a b
  have hpacket_sum :
      (∑ m ∈ Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b,
        packet m) =
        (∑ m ∈ stationary, packet m) + ∑ m ∈ endpoint, packet m := by
    have hchange :
        (∑ m ∈ Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b,
          packet m) =
          ∑ m ∈ stationary ∪ endpoint, packet m :=
      congrArg (fun s : Finset ℤ => ∑ m ∈ s, packet m) hpartition
    have hunion :
        (∑ m ∈ stationary ∪ endpoint, packet m) =
          (∑ m ∈ stationary, packet m) + ∑ m ∈ endpoint, packet m :=
      Finset.sum_union hdisjoint
    exact Eq.trans hchange hunion
  have hactive_eq_block :
      (∑ m ∈ Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b,
        packet m) =
      ∑ n ∈ Finset.Icc a b,
        Complex.exp (Complex.I * (φ n : ℂ)) :=
    Complex.realPhase_secondDerivative_vdc_activePacketSums_eq_block_sum φ a b
  have hblock_eq :
      (∑ n ∈ Finset.Icc a b,
        Complex.exp (Complex.I * (φ n : ℂ))) =
        (∑ m ∈ stationary, packet m) + ∑ m ∈ endpoint, packet m :=
    Eq.trans hactive_eq_block.symm hpacket_sum
  have htriangle :
      ‖(∑ m ∈ stationary, packet m) + ∑ m ∈ endpoint, packet m‖ ≤
        ‖∑ m ∈ stationary, packet m‖ + ‖∑ m ∈ endpoint, packet m‖ :=
    norm_add_le
      (∑ m ∈ stationary, packet m)
      (∑ m ∈ endpoint, packet m)
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        ‖z‖ ≤
          ‖∑ m ∈ stationary, packet m‖ +
          ‖∑ m ∈ endpoint, packet m‖)
      hblock_eq.symm
      htriangle

/-- The endpoint packet contribution splits into the three endpoint tails. -/
theorem Complex.logarithmicPhaseRealPhase_endpointPacket_norm_le_three_tail_norms
    (t : ℝ)
    {a b : ℕ}
    (hab : a ≤ b) :
    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ +
      (‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ +
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖) := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  let right : Finset ℤ :=
    Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b
  let left : Finset ℤ :=
    Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b
  let far : Finset ℤ :=
    Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b
  let packet : ℤ → ℂ :=
    fun m : ℤ => Complex.realPhase_secondDerivative_vdc_packetSum φ a b m
  have hpartition :
      Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b =
        right ∪ (left ∪ far) :=
    Complex.logarithmicPhaseRealPhase_endpointActive_eq_three_tails t a b
  have hleft_far : Disjoint left far :=
    Complex.logarithmicPhaseRealPhase_endpointLeft_farRight_disjoint t hab
  have hright_left : Disjoint right left :=
    Complex.logarithmicPhaseRealPhase_endpointRight_left_disjoint t a b
  have hright_far : Disjoint right far :=
    Complex.logarithmicPhaseRealPhase_endpointRight_farRight_disjoint t a b
  have hright_rest : Disjoint right (left ∪ far) := by
    exact Finset.disjoint_left.mpr
      (fun m hm_right hm_rest =>
        match Finset.mem_union.mp hm_rest with
        | Or.inl hm_left =>
            (Finset.disjoint_left.mp hright_left) hm_right hm_left
        | Or.inr hm_far =>
            (Finset.disjoint_left.mp hright_far) hm_right hm_far)
  have hsum_endpoint :
      (∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b,
        packet m) =
        (∑ m ∈ right, packet m) +
          ((∑ m ∈ left, packet m) + ∑ m ∈ far, packet m) := by
    have hchange :
        (∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b,
          packet m) =
          ∑ m ∈ right ∪ (left ∪ far), packet m :=
      congrArg (fun s : Finset ℤ => ∑ m ∈ s, packet m) hpartition
    have houter :
        (∑ m ∈ right ∪ (left ∪ far), packet m) =
          (∑ m ∈ right, packet m) + ∑ m ∈ left ∪ far, packet m :=
      Finset.sum_union hright_rest
    have hinner :
        (∑ m ∈ left ∪ far, packet m) =
          (∑ m ∈ left, packet m) + ∑ m ∈ far, packet m :=
      Finset.sum_union hleft_far
    exact Eq.trans hchange (Eq.trans houter
      (congrArg (fun z : ℂ => (∑ m ∈ right, packet m) + z) hinner))
  have htriangle_inner :
      ‖(∑ m ∈ left, packet m) + ∑ m ∈ far, packet m‖ ≤
        ‖∑ m ∈ left, packet m‖ + ‖∑ m ∈ far, packet m‖ :=
    norm_add_le (∑ m ∈ left, packet m) (∑ m ∈ far, packet m)
  have htriangle_outer :
      ‖(∑ m ∈ right, packet m) +
          ((∑ m ∈ left, packet m) + ∑ m ∈ far, packet m)‖ ≤
        ‖∑ m ∈ right, packet m‖ +
          ‖(∑ m ∈ left, packet m) + ∑ m ∈ far, packet m‖ :=
    norm_add_le
      (∑ m ∈ right, packet m)
      ((∑ m ∈ left, packet m) + ∑ m ∈ far, packet m)
  have hcombined :
      ‖(∑ m ∈ right, packet m) +
          ((∑ m ∈ left, packet m) + ∑ m ∈ far, packet m)‖ ≤
        ‖∑ m ∈ right, packet m‖ +
          (‖∑ m ∈ left, packet m‖ + ‖∑ m ∈ far, packet m‖) :=
    le_trans htriangle_outer
      (add_le_add_left htriangle_inner ‖∑ m ∈ right, packet m‖)
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        ‖z‖ ≤
          ‖∑ m ∈ right, packet m‖ +
          (‖∑ m ∈ left, packet m‖ + ‖∑ m ∈ far, packet m‖))
      hsum_endpoint.symm
      hcombined

/-- Arithmetic for three endpoint-tail twentieth-budget estimates. -/
theorem Real.logarithmicPhase_three_twenty_targets_le_sixty
    {E : ℝ}
    (hE : 0 ≤ E) :
    20 * E + (20 * E + 20 * E) ≤ 60 * E := by
  have hthree_sum :
      20 * E + (20 * E + 20 * E) = 60 * E := by
    have hleft :
        20 * E + (20 * E + 20 * E) =
          (20 * E + 20 * E) + 20 * E :=
      (add_assoc (20 * E) (20 * E) (20 * E)).symm
    have hpair :
        20 * E + 20 * E = (20 + 20) * E :=
      (add_mul 20 20 E).symm
    have hforty : (20 + 20 : ℝ) = 40 := by
      have hnat : (20 + 20 : ℕ) = 40 := rfl
      exact Eq.trans (Nat.cast_add 20 20).symm
        (Eq.trans (congrArg (fun n : ℕ => (n : ℝ)) hnat) Nat.cast_ofNat)
    have hpair_forty : 20 * E + 20 * E = 40 * E :=
      Eq.trans hpair (congrArg (fun r : ℝ => r * E) hforty)
    have hsum :
        40 * E + 20 * E = (40 + 20) * E :=
      (add_mul 40 20 E).symm
    have hsixty : (40 + 20 : ℝ) = 60 := by
      have hnat : (40 + 20 : ℕ) = 60 := rfl
      exact Eq.trans (Nat.cast_add 40 20).symm
        (Eq.trans (congrArg (fun n : ℕ => (n : ℝ)) hnat) Nat.cast_ofNat)
    exact Eq.trans hleft (Eq.trans
      (congrArg (fun z : ℝ => z + 20 * E) hpair_forty)
      (Eq.trans hsum (congrArg (fun r : ℝ => r * E) hsixty)))
  exact le_of_eq hthree_sum

/-- Right endpoint-tail packet contribution. -/
theorem Complex.logarithmicPhaseRealPhase_endpointRightPacketContribution_le_longTarget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  exact le_trans
    (Complex.logarithmicPhaseRealPhase_endpointRightPacket_sum_norm_le_zero_packet
      t ht_nonneg ha)
    (Complex.logarithmicPhaseRealPhase_endpointRightZeroPacketContribution_le_longTarget
      t ht ht_nonneg ha hab hlong_endpoint hderiv_growth)

/-- Left endpoint-tail packet contribution. -/
theorem Complex.logarithmicPhaseRealPhase_endpointLeftPacketContribution_le_longTarget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_endpointLeftPacketContribution_by_endpointInterval
      t ht ht_nonneg ha hab hlong_endpoint hderiv_growth

/-- Far-right endpoint-tail packet contribution. -/
theorem Complex.logarithmicPhaseRealPhase_endpointFarRightPacketContribution_le_longTarget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_endpointFarRightPacketContribution_by_endpointInterval
      t ht ht_nonneg ha hab hlong_endpoint hderiv_growth

/-- Endpoint packet contribution in the positive long branch.

This is the endpoint-tail part of the B-process: after filtering active
derivative packets whose stationary point lies outside the block, the total
endpoint packet sum is controlled by the endpoint-plus-square-root scale. -/
theorem Complex.logarithmicPhaseRealPhase_endpointPacketContribution_le_longTarget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      60 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  let E : ℝ :=
    (((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))
  have hsplit :
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ +
      (‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ +
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖) :=
    Complex.logarithmicPhaseRealPhase_endpointPacket_norm_le_three_tail_norms
      t hab
  have hright :
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤ 20 * E :=
    Complex.logarithmicPhaseRealPhase_endpointRightPacketContribution_le_longTarget
      t ht ht_nonneg ha hab hlong_endpoint hderiv_growth
  have hleft :
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤ 20 * E :=
    Complex.logarithmicPhaseRealPhase_endpointLeftPacketContribution_le_longTarget
      t ht ht_nonneg ha hab hlong_endpoint hderiv_growth
  have hfar :
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤ 20 * E :=
    Complex.logarithmicPhaseRealPhase_endpointFarRightPacketContribution_le_longTarget
      t ht ht_nonneg ha hab hlong_endpoint hderiv_growth
  have htails :
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ +
      (‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ +
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖) ≤ 60 * E :=
    le_trans
      (add_le_add hright (add_le_add hleft hfar))
      (Real.logarithmicPhase_three_twenty_targets_le_sixty
        (Real.logarithmicPhase_endpoint_sqrt_target_nonneg t ht b))
  exact le_trans hsplit htails

/-- Stationary packet contribution in the positive long branch.

This is the stationary-frequency part of the B-process: active derivative
packets whose explicit stationary point lies inside the block have total
packet sum controlled by the endpoint-plus-square-root scale. -/
theorem Complex.logarithmicPhaseRealPhase_stationaryPacketContribution_le_longTarget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      10 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_stationaryPacketContribution_by_frequencyCount
      t ht ht_nonneg ha hab hlong_sqrt hderiv_growth

/-- The stationary and endpoint packet budgets assemble into the widened long target. -/
theorem Real.logarithmicPhase_twenty_sixty_targets_le_eighty
    (E : ℝ) :
    20 * E + 60 * E ≤ 80 * E := by
  have hleft :
      20 * E + 60 * E = (20 + 60) * E := by
    exact (add_mul 20 60 E).symm
  have hconst : (20 + 60 : ℝ) = 80 := by
    have hnat : (20 + 60 : ℕ) = 80 :=
      rfl
    have hcast_add :
        (((20 + 60 : ℕ) : ℝ) = (20 : ℝ) + 60) :=
      Nat.cast_add 20 60
    have hcast_value :
        (((20 + 60 : ℕ) : ℝ) = (80 : ℝ)) :=
      Eq.trans
        (congrArg (fun n : ℕ => (n : ℝ)) hnat)
        Nat.cast_ofNat
    exact Eq.trans hcast_add.symm hcast_value
  have hright :
      (20 + 60 : ℝ) * E = 80 * E :=
    congrArg (fun r : ℝ => r * E) hconst
  exact le_of_eq (Eq.trans hleft hright)

/-- Resonance-safe stationary-frequency budget for the positive long
logarithmic branch.

This is the remaining classical B-process obligation.  The proof is by the
derivative-window packet decomposition: split active derivative-frequency
packets into endpoint and stationary subfamilies, prove the endpoint packet
sum is controlled by the endpoint scale, prove the stationary packet sum is
controlled by the square-root scale, and add the two contributions.  No global
separation of shifted increments from `2πℤ` is assumed. -/
theorem Complex.logarithmicPhaseRealPhase_long_nonneg_stationary_bProcess_budget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hab_strict : a < b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  let E : ℝ :=
    (((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))
  have hsplit :
      ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
        ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b,
          Complex.realPhase_secondDerivative_vdc_packetSum
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m‖ +
        ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b,
          Complex.realPhase_secondDerivative_vdc_packetSum
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m‖ :=
    Complex.logarithmicPhaseRealPhase_block_norm_le_stationary_endpoint_packet_norms
      t a b
  have hstationary :
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
        20 * E :=
    Complex.logarithmicPhaseRealPhase_stationaryPacketContribution_le_longTarget
      t ht ht_nonneg ha hab hlong_sqrt hderiv_growth
  have hendpoint :
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
        60 * E :=
    Complex.logarithmicPhaseRealPhase_endpointPacketContribution_le_longTarget
      t ht ht_nonneg ha hab hlong_endpoint hderiv_growth
  have hpacket_budget :
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ +
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
        80 * E :=
    le_trans
      (add_le_add hstationary hendpoint)
      (Real.logarithmicPhase_twenty_sixty_targets_le_eighty E)
  exact le_trans hsplit hpacket_budget

/-- The logarithmic stationary-frequency analysis controls the positive long
branch at the canonical square-root scale.

This is the analytic content of the B-process for `φ(x) = -t log x`.  The proof
chain is:

* rewrite the derivative as `-t / x` on the positive block;
* use the reciprocal map to locate stationary frequencies and endpoint tails;
* bound endpoint tails by `(b + 1) / ‖t‖`;
* bound the stationary-frequency contribution by the square-root scale;
* sum the stationary packet estimates. -/
theorem Complex.logarithmicPhaseRealPhase_long_nonneg_stationary_bProcess_budget_target
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hab_strict : a < b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_long_nonneg_stationary_bProcess_budget
      t ht ht_nonneg ha hab hab_strict hlong_sqrt hlong_endpoint
      hderiv_growth

/-- Logarithmic B-process budget for the positive long branch.

This is the genuine logarithmic-phase sink left after the finite Weyl
differencing algebra has been separated into `SecondDerivativeVdc`.  Its proof
uses the reciprocal derivative formula for `φ(x) = -t log x`: the stationary
frequencies are controlled by the image of `x ↦ t / x`, endpoint tails account
for the scale `(b + 1) / ‖t‖`, and the remaining stationary contribution is
bounded by the square-root averaging length.  It deliberately does not assume
global separation of shifted increments from `2πℤ`, which would be false in
the resonance-safe branch. -/
theorem Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hab_strict : a < b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_long_nonneg_stationary_bProcess_budget_target
      t ht ht_nonneg ha hab hab_strict hlong_sqrt hlong_endpoint
      hderiv_growth

/-- Positive-frequency long logarithmic B-process from the derivative-growth
form of the logarithmic curvature hypothesis.

This wrapper keeps the public long-core name stable while the actual
logarithmic stationary-frequency budget is owned by
`logarithmicPhaseRealPhase_long_nonneg_bProcess_budget`. -/
theorem Complex.logarithmicPhaseRealPhase_sharp_bProcess_integer_block_bound_long_nonneg_of_growth_core
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hab_strict : a < b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget
      t ht ht_nonneg ha hab hab_strict hlong_sqrt hlong_endpoint
      hderiv_growth

/-- Positive-frequency long logarithmic B-process from the concrete curvature
growth inequality. -/
theorem Complex.logarithmicPhaseRealPhase_sharp_bProcess_integer_block_bound_long_nonneg_of_growth
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hab_strict : a < b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_sharp_bProcess_integer_block_bound_long_nonneg_of_growth_core
      t ht ht_nonneg ha hab hab_strict hlong_sqrt hlong_endpoint
      hderiv_growth

/-- Positive-frequency long logarithmic B-process from the concrete curvature
lower bound. -/
theorem Complex.logarithmicPhaseRealPhase_sharp_bProcess_integer_block_bound_long_nonneg_of_curvature
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hab_strict : a < b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hcurvature_lower :
      ∀ x : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
          ‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹ ≤
            ‖deriv
              (deriv
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
              x‖) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have hderiv_growth :
      ∀ x y : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        x ≤ y →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x) :=
    fun x y hx hy hxy =>
      Complex.logarithmicPhaseRealPhase_deriv_growth_of_nonneg_curvature_integer_block
        t ht_nonneg ha hcurvature_lower hx hy hxy
  exact
    Complex.logarithmicPhaseRealPhase_sharp_bProcess_integer_block_bound_long_nonneg_of_growth
      t ht ht_nonneg ha hab hab_strict hlong_sqrt hlong_endpoint hderiv_growth

/-- Long logarithmic B-process estimate in the branch `0 ≤ t`, where the
real-phase derivative is monotone increasing. -/
theorem Complex.logarithmicPhaseRealPhase_sharp_bProcess_integer_block_bound_long_nonneg
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hab_strict : a < b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hcurvature_lower :
      ∀ x : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
          ‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹ ≤
            ‖deriv
              (deriv
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
              x‖) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_sharp_bProcess_integer_block_bound_long_nonneg_of_curvature
      t ht ht_nonneg ha hab hab_strict hlong_sqrt hlong_endpoint
      hcurvature_lower

/-- Long logarithmic B-process estimate in the branch `t ≤ 0`, where the
real-phase derivative is monotone decreasing. -/
theorem Complex.logarithmicPhaseRealPhase_sharp_bProcess_integer_block_bound_long_nonpos
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonpos : t ≤ 0)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hab_strict : a < b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hcurvature_lower :
      ∀ x : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
          ‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹ ≤
            ‖deriv
              (deriv
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
              x‖) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have hneg_norm : ‖-t‖ = ‖t‖ :=
    norm_neg t
  have ht_neg : 1 ≤ ‖-t‖ :=
    Eq.subst
      (motive := fun r : ℝ => 1 ≤ r)
      hneg_norm.symm
      ht
  have ht_neg_nonneg : 0 ≤ -t :=
    neg_nonneg.mpr ht_nonpos
  have hlong_sqrt_neg :
      Real.sqrt (1 + ‖-t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)) :=
    Eq.subst
      (motive := fun r : ℝ =>
        Real.sqrt (1 + r) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
      hneg_norm.symm
      hlong_sqrt
  have hlong_endpoint_neg :
      (((b + 1 : ℕ) : ℝ) / ‖-t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)) :=
    Eq.subst
      (motive := fun r : ℝ =>
        (((b + 1 : ℕ) : ℝ) / r) <
          (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
      hneg_norm.symm
      hlong_endpoint
  have hneg_bound :
      ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase (-t) n : ℂ))‖ ≤
        80 * ((((b + 1 : ℕ) : ℝ) / ‖-t‖ +
          Real.sqrt (1 + ‖-t‖))) :=
    Complex.logarithmicPhaseRealPhase_sharp_bProcess_integer_block_bound_long_nonneg
      (-t) ht_neg ht_neg_nonneg ha hab hab_strict
      hlong_sqrt_neg hlong_endpoint_neg
      (Complex.logarithmicPhaseRealPhase_secondDerivative_curvature_lower
        (-t) ht_neg ha hab)
  have htarget_eq :
      80 * ((((b + 1 : ℕ) : ℝ) / ‖-t‖ + Real.sqrt (1 + ‖-t‖))) =
        80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
    exact congrArg
      (fun r : ℝ => 80 * ((((b + 1 : ℕ) : ℝ) / r + Real.sqrt (1 + r))))
      hneg_norm
  have hnorm_eq :
      ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase (-t) n : ℂ))‖ =
      ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ :=
    Complex.logarithmicPhaseRealPhase_block_norm_neg_parameter_eq t a b
  exact
    Eq.subst
      (motive := fun left : ℝ =>
        left ≤ 80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
      hnorm_eq
      (Eq.subst
        (motive := fun right : ℝ =>
          ‖∑ n ∈ Finset.Icc a b,
            Complex.exp
              (Complex.I *
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase (-t) n : ℂ))‖ ≤
            right)
        htarget_eq
        hneg_bound)

/-- Long nontrivial logarithmic-phase B-process estimate on one positive
integer block.  The singleton and short-block cases are discharged before this
theorem is used. -/
theorem Complex.logarithmicPhaseRealPhase_sharp_bProcess_integer_block_bound_long
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hab_strict : a < b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hcurvature_lower :
      ∀ x : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
          ‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹ ≤
            ‖deriv
              (deriv
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
              x‖) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  by_cases ht_nonneg : 0 ≤ t
  · exact
      Complex.logarithmicPhaseRealPhase_sharp_bProcess_integer_block_bound_long_nonneg
        t ht ht_nonneg ha hab hab_strict hlong_sqrt hlong_endpoint
        hcurvature_lower
  · have ht_nonpos : t ≤ 0 :=
      le_of_lt (lt_of_not_ge ht_nonneg)
    exact
      Complex.logarithmicPhaseRealPhase_sharp_bProcess_integer_block_bound_long_nonpos
        t ht ht_nonpos ha hab hab_strict hlong_sqrt hlong_endpoint
        hcurvature_lower

/-- Sharp logarithmic-phase B-process estimate on one positive integer block.

This is the remaining finite oscillatory summation theorem after the generic
calculus part has been separated in `SecondDerivativeVdc`: the concrete
derivative `(-t / x)` supplies the endpoint scale `B / |t|`, and the curvature
supplies the square-root transition scale. -/
theorem Complex.logarithmicPhaseRealPhase_sharp_bProcess_integer_block_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hcurvature_lower :
      ∀ x : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
          ‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹ ≤
            ‖deriv
              (deriv
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
              x‖) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  by_cases hsingleton : a = b
  · have hbase :
        ‖∑ n ∈ Finset.Icc a a,
          Complex.exp
            (Complex.I *
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
          (((a + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) :=
      Complex.realPhase_secondDerivative_vdc_singleton_integer_block_bound
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a ht
    have hwiden :
        (((a + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) ≤
          80 * ((((a + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
      Real.logarithmicPhase_target_le_eighty_mul
        (Real.logarithmicPhase_endpoint_sqrt_target_nonneg t ht a)
    exact Eq.subst
      (motive := fun right : ℕ =>
        ‖∑ n ∈ Finset.Icc a right,
          Complex.exp
            (Complex.I *
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
          80 * ((((right + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
      hsingleton.symm
      (le_trans hbase hwiden)
  · have hab_strict : a < b :=
      lt_of_le_of_ne hab hsingleton
    have hab_succ : a ≤ b + 1 :=
      le_trans hab (Nat.le_succ b)
    by_cases hshort_sqrt :
      (((b + 1 : ℕ) : ℝ) - (a : ℝ)) ≤ Real.sqrt (1 + ‖t‖)
    · have hbase :
          ‖∑ n ∈ Finset.Icc a b,
            Complex.exp
              (Complex.I *
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
            (((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) :=
        Complex.realPhase_secondDerivative_vdc_integer_block_bound_of_length_le_sqrt
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          ht hshort_sqrt hab_succ
      have hwiden :
          (((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) ≤
            80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
        Real.logarithmicPhase_target_le_eighty_mul
          (Real.logarithmicPhase_endpoint_sqrt_target_nonneg t ht b)
      exact le_trans hbase hwiden
    · by_cases hshort_endpoint :
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)) ≤ (((b + 1 : ℕ) : ℝ) / ‖t‖)
      · have hbase :
            ‖∑ n ∈ Finset.Icc a b,
              Complex.exp
                (Complex.I *
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
              (((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) :=
          Complex.realPhase_secondDerivative_vdc_integer_block_bound_of_length_le_endpoint
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            ht hshort_endpoint hab_succ
        have hwiden :
            (((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) ≤
              80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
          Real.logarithmicPhase_target_le_eighty_mul
            (Real.logarithmicPhase_endpoint_sqrt_target_nonneg t ht b)
        exact le_trans hbase hwiden
      · exact
          Complex.logarithmicPhaseRealPhase_sharp_bProcess_integer_block_bound_long
            t ht ha hab hab_strict
            (lt_of_not_ge hshort_sqrt)
            (lt_of_not_ge hshort_endpoint)
            hcurvature_lower

/-- Resonance-safe second-derivative van der Corput estimate for the real
scalar logarithmic phase, parameterized by the concrete curvature lower bound.

This is the classical analytic primitive for `φ(x) = -t log x`: it combines the
endpoint first-derivative scale with the square-root curvature scale without
any separation-from-`2πℤ` hypothesis. -/
theorem Complex.logarithmicPhaseRealPhase_secondDerivative_vdc_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hcurvature_lower :
      ∀ x : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
          ‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹ ≤
            ‖deriv
              (deriv
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
              x‖) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_sharp_bProcess_integer_block_bound
      t ht ha hab
      hcurvature_lower

/-- Resonance-safe second-derivative van der Corput block estimate for the real
scalar logarithmic phase.

This is the classical analytic primitive needed when the adjacent increments
may pass close to `2πℤ`, so the Kusmin-Landau separated-increment theorem is
not applicable.  The proof uses the nonzero curvature of `x ↦ -t log x` on the
integer block rather than a no-resonance finite-difference hypothesis. -/
theorem Complex.logarithmicPhaseRealPhase_curvature_integer_block_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_secondDerivative_vdc_bound
      t ht ha hab
      (Complex.logarithmicPhaseRealPhase_secondDerivative_curvature_lower
        t ht ha hab)

/-- Resonance-safe second-derivative van der Corput block estimate for the
concrete logarithmic phase. -/
theorem Complex.logarithmicPhase_curvature_integer_block_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    ‖∑ n ∈ Finset.Icc a b,
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have hsample :
      (∑ n ∈ Finset.Icc a b,
        ((n : ℂ) ^ (-(t : ℂ) * Complex.I))) =
        ∑ n ∈ Finset.Icc a b,
          Complex.exp
            (Complex.I *
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ)) := by
    exact Finset.sum_congr rfl
      (fun n hn_mem =>
        have hn_one : 1 ≤ n :=
          le_trans ha (Finset.mem_Icc.mp hn_mem).1
        have hn_pos : 0 < n :=
          Nat.lt_of_succ_le hn_one
        have hsample_function :
            ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) =
              Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t n :=
          (Complex.logarithmicPhase_integer_sample_eq t hn_pos).symm
        have hfunction_phase :
            Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t n =
              Complex.exp
                (Complex.I *
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ)) :=
          Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction_eq_realPhase
            t n
        Eq.trans hsample_function hfunction_phase)
  have hblock :
      ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
        80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖))) :=
    Complex.logarithmicPhaseRealPhase_curvature_integer_block_bound
      t ht ha hab
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        ‖z‖ ≤
          80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
            Real.sqrt (1 + ‖t‖))))
      hsample.symm
      hblock
end

end LFunctions
end Boundary
