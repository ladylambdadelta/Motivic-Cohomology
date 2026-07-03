import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.FirstDerivativeBlock

/-!
# Real-phase logarithmic curvature core

This file owns the small concrete real-phase facts needed by the logarithmic
curvature block estimate.
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
    Filter.mem_of_superset
      hpositive_mem_nhds
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
          (T *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) ≤
            ‖deriv
              (deriv
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
              z‖))
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
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x) := by
  let C : ℝ :=
    T *
      ((((b + 1 : ℕ) : ℝ) * ((b + 1 : ℕ) : ℝ))⁻¹)
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
      _ = conj Complex.I * (θ : ℂ) := by
        exact congrArg (fun z : ℂ => z * (θ : ℂ)) Complex.conj_I.symm
      _ = conj Complex.I * conj (θ : ℂ) := by
        exact congrArg (fun z : ℂ => conj Complex.I * z)
          (Complex.conj_ofReal θ).symm
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

end

end LFunctions
end Boundary
