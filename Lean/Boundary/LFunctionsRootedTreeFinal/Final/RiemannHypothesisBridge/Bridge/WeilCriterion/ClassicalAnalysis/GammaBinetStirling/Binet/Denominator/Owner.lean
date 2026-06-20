import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.Binet.BranchIntegral.Owner

/-!
# Binet formula: denominator analysis

This file owns nonzero properties in the right half-plane, norm inequalities,
and denominator bounds for the arctangent kernel.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- The numerator in the derivative of the Cayley transform defining the
principal arctangent. -/
theorem Complex.arctan_cayley_derivative_numerator
    (z : ℂ) :
    Complex.I * (1 - z * Complex.I) -
        (1 + z * Complex.I) * (-Complex.I) =
      (2 : ℂ) * Complex.I := by
  have hleft :
      Complex.I * (1 - z * Complex.I) = Complex.I + z := by
    calc
      Complex.I * (1 - z * Complex.I) =
          Complex.I * 1 - Complex.I * (z * Complex.I) := by
        exact mul_sub Complex.I 1 (z * Complex.I)
      _ = Complex.I - Complex.I * (z * Complex.I) := by
        exact congrArg (fun u : ℂ => u - Complex.I * (z * Complex.I))
          (mul_one Complex.I)
      _ = Complex.I - (Complex.I * z) * Complex.I := by
        exact congrArg (fun u : ℂ => Complex.I - u)
          (Eq.symm (mul_assoc Complex.I z Complex.I))
      _ = Complex.I - (z * Complex.I) * Complex.I := by
        exact congrArg (fun u : ℂ => Complex.I - u * Complex.I)
          (mul_comm Complex.I z)
      _ = Complex.I - z * (Complex.I * Complex.I) := by
        exact congrArg (fun u : ℂ => Complex.I - u)
          (mul_assoc z Complex.I Complex.I)
      _ = Complex.I - z * (-1 : ℂ) := by
        exact congrArg (fun u : ℂ => Complex.I - z * u) Complex.I_mul_I
      _ = Complex.I - -z := by
        exact congrArg (fun u : ℂ => Complex.I - u) (mul_neg_one z)
      _ = Complex.I + z := sub_neg_eq_add Complex.I z
  have hright :
      (1 + z * Complex.I) * (-Complex.I) = -Complex.I + z := by
    calc
      (1 + z * Complex.I) * (-Complex.I) =
          1 * (-Complex.I) + (z * Complex.I) * (-Complex.I) := by
        exact add_mul 1 (z * Complex.I) (-Complex.I)
      _ = -Complex.I + (z * Complex.I) * (-Complex.I) := by
        exact congrArg (fun u : ℂ => u + (z * Complex.I) * (-Complex.I))
          (one_mul (-Complex.I))
      _ = -Complex.I + z * (Complex.I * (-Complex.I)) := by
        exact congrArg (fun u : ℂ => -Complex.I + u)
          (mul_assoc z Complex.I (-Complex.I))
      _ = -Complex.I + z * (-(Complex.I * Complex.I)) := by
        exact congrArg (fun u : ℂ => -Complex.I + z * u)
          (mul_neg Complex.I Complex.I)
      _ = -Complex.I + z * (-(-1 : ℂ)) := by
        exact congrArg
          (fun u : ℂ => -Complex.I + z * (-u))
          Complex.I_mul_I
      _ = -Complex.I + z * 1 := by
        exact congrArg (fun u : ℂ => -Complex.I + z * u) (neg_neg (1 : ℂ))
      _ = -Complex.I + z := by
        exact congrArg (fun u : ℂ => -Complex.I + u) (mul_one z)
  calc
    Complex.I * (1 - z * Complex.I) -
        (1 + z * Complex.I) * (-Complex.I) =
        (Complex.I + z) - (-Complex.I + z) := by
      exact congrArg₂ HSub.hSub hleft hright
    _ = (Complex.I + z) - (z + -Complex.I) := by
      exact congrArg (fun u : ℂ => (Complex.I + z) - u)
        (add_comm (-Complex.I) z)
    _ = Complex.I + Complex.I := by
      exact Complex.add_sub_add_neg_right_eq_add Complex.I z Complex.I
    _ = (1 : ℂ) * Complex.I + (1 : ℂ) * Complex.I := by
      exact congrArg₂ HAdd.hAdd (Eq.symm (one_mul Complex.I))
        (Eq.symm (one_mul Complex.I))
    _ = ((1 : ℂ) + 1) * Complex.I := by
      exact Eq.symm (add_mul (1 : ℂ) 1 Complex.I)
    _ = (2 : ℂ) * Complex.I := by
      exact congrArg (fun u : ℂ => u * Complex.I) (one_add_one_eq_two)

/-- The real numerator cancellation in the imaginary part of the Cayley
transform. -/
theorem Real.cayley_im_div_identity
    (a b d : ℝ) :
    a * (1 + b) / d - (1 - b) * (-a) / d = 2 * a / d := by
  have hright_neg :
      -((1 - b) * (-a)) = a * (1 - b) := by
    calc
      -((1 - b) * (-a)) = -(-((1 - b) * a)) := by
        exact congrArg Neg.neg (mul_neg (1 - b) a)
      _ = (1 - b) * a := neg_neg ((1 - b) * a)
      _ = a * (1 - b) := mul_comm (1 - b) a
  have hsum :
      a * (1 + b) + a * (1 - b) = 2 * a := by
    have hinside :
        (1 + b) + (1 - b) = (2 : ℝ) := by
      calc
        (1 + b) + (1 - b) = 1 + (b + (1 - b)) := by
          exact add_assoc 1 b (1 - b)
        _ = 1 + (b + (1 + -b)) := by
          exact congrArg (fun u : ℝ => 1 + (b + u)) (sub_eq_add_neg 1 b)
        _ = 1 + ((b + 1) + -b) := by
          exact congrArg (fun u : ℝ => 1 + u) (Eq.symm (add_assoc b 1 (-b)))
        _ = 1 + ((1 + b) + -b) := by
          exact congrArg (fun u : ℝ => 1 + (u + -b)) (add_comm b 1)
        _ = 1 + (1 + (b + -b)) := by
          exact congrArg (fun u : ℝ => 1 + u) (add_assoc 1 b (-b))
        _ = 1 + (1 + 0) := by
          exact congrArg (fun u : ℝ => 1 + (1 + u)) (add_neg_cancel b)
        _ = 1 + 1 := by
          exact congrArg (fun u : ℝ => 1 + u) (add_zero 1)
        _ = 2 := one_add_one_eq_two
    calc
      a * (1 + b) + a * (1 - b) =
          a * ((1 + b) + (1 - b)) := by
        exact Eq.symm (left_distrib a (1 + b) (1 - b))
      _ = a * 2 := by
        exact congrArg (fun u : ℝ => a * u) hinside
      _ = 2 * a := mul_comm a 2
  calc
    a * (1 + b) / d - (1 - b) * (-a) / d =
        a * (1 + b) / d + -((1 - b) * (-a) / d) := by
      exact sub_eq_add_neg (a * (1 + b) / d) ((1 - b) * (-a) / d)
    _ = a * (1 + b) / d + -((1 - b) * (-a)) / d := by
      exact congrArg (fun u : ℝ => a * (1 + b) / d + u)
        (neg_div' d ((1 - b) * (-a)))
    _ = a * (1 + b) / d + (a * (1 - b)) / d := by
      exact congrArg (fun u : ℝ => a * (1 + b) / d + u / d) hright_neg
    _ = (a * (1 + b) + a * (1 - b)) / d := by
      exact Eq.symm (add_div (a * (1 + b)) (a * (1 - b)) d)
    _ = 2 * a / d := by
      exact congrArg (fun u : ℝ => u / d) hsum

/-- Positive-real Binet formula for the principal logarithm of Gamma, reduced
from the branch formula. -/
theorem Complex.Gamma_binetSecondFormula_principalLog_positiveReal_owner
    {x : ℝ}
    (hx : 0 < x)
    (hfinite :
      ∀ N : ℕ,
        Complex.binetAbelPlanaLogGammaFiniteApproximation N (x : ℂ) =
          Complex.binetAbelPlanaFiniteMainTerm N (x : ℂ) +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N (x : ℂ) +
              Complex.binetAbelPlanaFiniteContourRemainder N (x : ℂ)) :
    Complex.log (Complex.Gamma (x : ℂ)) =
      Complex.binetLogGammaMainTerm (x : ℂ) +
        Complex.binetSecondFormulaRemainder (x : ℂ) := by
  have hbranch :
      Complex.binetLogGammaBranch (x : ℂ) =
        Complex.log (Complex.Gamma (x : ℂ)) :=
    Complex.binetLogGammaBranch_eq_principalLog_Gamma_of_posReal_owner hx hfinite
  exact hbranch.symm

/-- The principal complex arctangent has derivative `1 / (1 + z^2)` at points
where its defining logarithm is differentiable.  The extra `slitPlane`
hypothesis is essential for the principal branch of `Complex.log`. -/
theorem Complex.arctan_hasDerivAt_of_log_argument_mem_slitPlane
    {z : ℂ}
    (hzI : z ≠ Complex.I)
    (hznegI : z ≠ -Complex.I)
    (hzslit :
      (1 + z * Complex.I) / (1 - z * Complex.I) ∈ Complex.slitPlane) :
    HasDerivAt
      Complex.arctan
      ((1 : ℂ) / (1 + z ^ 2)) z := by
  have hnum_ne : 1 + z * Complex.I ≠ 0 := by
    intro hzero
    have hz_eq : z = Complex.I := by
      calc
        z = z * Complex.I / Complex.I := by
          exact (mul_div_cancel_right₀ z Complex.I_ne_zero).symm
        _ = (-1 : ℂ) / Complex.I := by
          have hzI_eq : z * Complex.I = -1 := by
            have hzero_comm : z * Complex.I + 1 = 0 :=
              Eq.trans (add_comm (z * Complex.I) 1) hzero
            exact add_eq_zero_iff_eq_neg.mp hzero_comm
          exact congrArg (fun u : ℂ => u / Complex.I) hzI_eq
        _ = Complex.I := Complex.neg_one_div_I_eq_I
    exact hzI hz_eq
  have hden_ne : 1 - z * Complex.I ≠ 0 := by
    intro hzero
    have hz_eq : z = -Complex.I := by
      calc
        z = z * Complex.I / Complex.I := by
          exact (mul_div_cancel_right₀ z Complex.I_ne_zero).symm
        _ = (1 : ℂ) / Complex.I := by
          have hzI_eq : z * Complex.I = 1 := by
            exact Eq.symm (sub_eq_zero.mp hzero)
          exact congrArg (fun u : ℂ => u / Complex.I) hzI_eq
        _ = -Complex.I := Complex.one_div_I_eq_neg_I
    exact hznegI hz_eq
  let q : ℂ → ℂ :=
    fun u : ℂ => (1 + u * Complex.I) / (1 - u * Complex.I)
  have hq :
      HasDerivAt q
        ((2 : ℂ) * Complex.I / (1 - z * Complex.I) ^ 2) z := by
    have hnum :
        HasDerivAt (fun u : ℂ => 1 + u * Complex.I) Complex.I z := by
      exact
        Eq.subst
          (motive := fun d : ℂ =>
            HasDerivAt (fun u : ℂ => 1 + u * Complex.I) d z)
          (one_mul Complex.I)
          (((hasDerivAt_id' z).mul_const Complex.I).const_add 1)
    have hden :
        HasDerivAt (fun u : ℂ => 1 - u * Complex.I) (-Complex.I) z := by
      have hneg_one_mul :
          -(1 * Complex.I) = -Complex.I := by
        exact congrArg Neg.neg (one_mul Complex.I)
      exact
        Eq.subst
          (motive := fun d : ℂ =>
            HasDerivAt (fun u : ℂ => 1 - u * Complex.I) d z)
          hneg_one_mul
          (((hasDerivAt_id' z).mul_const Complex.I).const_sub 1)
    have hdiv := hnum.div hden hden_ne
    have halg :
        (Complex.I * (1 - z * Complex.I) -
            (1 + z * Complex.I) * (-Complex.I)) /
            (1 - z * Complex.I) ^ 2 =
          (2 : ℂ) * Complex.I / (1 - z * Complex.I) ^ 2 := by
      exact congrArg
        (fun u : ℂ => u / (1 - z * Complex.I) ^ 2)
        (Complex.arctan_cayley_derivative_numerator z)
    exact
      Eq.subst
        (motive := fun d : ℂ => HasDerivAt q d z)
        halg
        hdiv
  have hlog :
      HasDerivAt
        (fun u : ℂ => Complex.log (q u))
        (((2 : ℂ) * Complex.I / (1 - z * Complex.I) ^ 2) /
          ((1 + z * Complex.I) / (1 - z * Complex.I))) z :=
    hq.clog hzslit
  have hscaled :
      HasDerivAt
        (fun u : ℂ => (-Complex.I / 2) * Complex.log (q u))
        ((-Complex.I / 2) *
          (((2 : ℂ) * Complex.I / (1 - z * Complex.I) ^ 2) /
            ((1 + z * Complex.I) / (1 - z * Complex.I)))) z :=
    hlog.const_mul (-Complex.I / 2)
  have halg :
      (-Complex.I / 2) *
          (((2 : ℂ) * Complex.I / (1 - z * Complex.I) ^ 2) /
            ((1 + z * Complex.I) / (1 - z * Complex.I))) =
        (1 : ℂ) / (1 + z ^ 2) := by
    exact Complex.arctan_log_derivative_factor_algebra z hden_ne
  exact halg ▸ hscaled

/-- A point in the open right half-plane is nonzero. -/
theorem Complex.ne_zero_of_re_pos
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    w ≠ 0 := by
  intro hw
  have hre_zero : w.re = 0 := by
    exact congrArg Complex.re hw
  exact (lt_irrefl (0 : ℝ)) (hw_re_pos.trans_eq hre_zero)

/-- Adding a purely imaginary number to a point in the open right half-plane
cannot give zero. -/
theorem Complex.add_real_mul_I_ne_zero_of_re_pos
    {w : ℂ} {t : ℝ}
    (hw_re_pos : 0 < w.re) :
    w + (t : ℂ) * Complex.I ≠ 0 := by
  intro hzero
  have hre_zero : (w + (t : ℂ) * Complex.I).re = 0 := by
    exact congrArg Complex.re hzero
  have hre_eq : (w + (t : ℂ) * Complex.I).re = w.re := by
    exact Complex.add_real_mul_I_re w t
  exact (lt_irrefl (0 : ℝ)) (hw_re_pos.trans_eq (hre_eq.symm.trans hre_zero))

/-- Subtracting a purely imaginary number from a point in the open right
half-plane cannot give zero. -/
theorem Complex.sub_real_mul_I_ne_zero_of_re_pos
    {w : ℂ} {t : ℝ}
    (hw_re_pos : 0 < w.re) :
    w - (t : ℂ) * Complex.I ≠ 0 := by
  intro hzero
  have hre_zero : (w - (t : ℂ) * Complex.I).re = 0 := by
    exact congrArg Complex.re hzero
  have hre_eq : (w - (t : ℂ) * Complex.I).re = w.re := by
    exact Complex.sub_real_mul_I_re w t
  exact (lt_irrefl (0 : ℝ)) (hw_re_pos.trans_eq (hre_eq.symm.trans hre_zero))

/-- The algebraic denominator `w^2 + t^2` in the differentiated Binet kernel
does not vanish in the open right half-plane. -/
theorem Complex.binet_arctan_derivative_denominator_ne_zero
    {t : ℝ} {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    w ^ 2 + (t : ℂ) ^ 2 ≠ 0 := by
  have hplus :
      w + (t : ℂ) * Complex.I ≠ 0 :=
    Complex.add_real_mul_I_ne_zero_of_re_pos hw_re_pos
  have hminus :
      w - (t : ℂ) * Complex.I ≠ 0 :=
    Complex.sub_real_mul_I_ne_zero_of_re_pos hw_re_pos
  have hfactor :
      (w + (t : ℂ) * Complex.I) * (w - (t : ℂ) * Complex.I) =
        w ^ 2 + (t : ℂ) ^ 2 := by
    exact Complex.add_mul_sub_real_mul_I_eq_sq_add_sq w t
  intro hzero
  have hprod_zero :
      (w + (t : ℂ) * Complex.I) * (w - (t : ℂ) * Complex.I) = 0 :=
    hfactor.trans hzero
  exact
    (mul_ne_zero hplus hminus) hprod_zero

/-- A nonnegative real part gives a lower bound for the complex norm. -/
theorem Complex.re_le_norm_of_nonneg_re
    {z : ℂ}
    (hz_re_nonneg : 0 ≤ z.re) :
    z.re ≤ ‖z‖ := by
  have hre_abs_eq : |z.re| = z.re :=
    abs_of_nonneg hz_re_nonneg
  have hre_abs_le_norm : |z.re| ≤ ‖z‖ := by
    exact Complex.abs_re_le_abs z
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ ‖z‖)
      hre_abs_eq
      hre_abs_le_norm

/-- Adding a purely imaginary real multiple preserves the real-part lower
bound for the complex norm. -/
theorem Complex.re_le_norm_add_real_mul_I
    {z : ℂ}
    (hz_re_nonneg : 0 ≤ z.re)
    (t : ℝ) :
    z.re ≤ ‖z + (t : ℂ) * Complex.I‖ := by
  have hsum_re_nonneg : 0 ≤ (z + (t : ℂ) * Complex.I).re := by
    have hre : (z + (t : ℂ) * Complex.I).re = z.re := by
      exact Complex.add_real_mul_I_re z t
    exact hre ▸ hz_re_nonneg
  have hnorm :
      (z + (t : ℂ) * Complex.I).re ≤
        ‖z + (t : ℂ) * Complex.I‖ :=
    Complex.re_le_norm_of_nonneg_re hsum_re_nonneg
  have hre :
      (z + (t : ℂ) * Complex.I).re = z.re := by
    exact Complex.add_real_mul_I_re z t
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ ‖z + (t : ℂ) * Complex.I‖)
      hre
      hnorm

/-- Subtracting a purely imaginary real multiple preserves the real-part lower
bound for the complex norm. -/
theorem Complex.re_le_norm_sub_real_mul_I
    {z : ℂ}
    (hz_re_nonneg : 0 ≤ z.re)
    (t : ℝ) :
    z.re ≤ ‖z - (t : ℂ) * Complex.I‖ := by
  have hdiff_re_nonneg : 0 ≤ (z - (t : ℂ) * Complex.I).re := by
    have hre : (z - (t : ℂ) * Complex.I).re = z.re := by
      exact Complex.sub_real_mul_I_re z t
    exact hre ▸ hz_re_nonneg
  have hnorm :
      (z - (t : ℂ) * Complex.I).re ≤
        ‖z - (t : ℂ) * Complex.I‖ :=
    Complex.re_le_norm_of_nonneg_re hdiff_re_nonneg
  have hre :
      (z - (t : ℂ) * Complex.I).re = z.re := by
    exact Complex.sub_real_mul_I_re z t
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ ‖z - (t : ℂ) * Complex.I‖)
      hre
      hnorm

/-- Lower bound for the differentiated Binet denominator from a real-part
margin. -/
theorem Complex.binet_arctan_derivative_denominator_norm_lower
    {z : ℂ}
    {δ t : ℝ}
    (hδ_nonneg : 0 ≤ δ)
    (hδ_le_re : δ ≤ z.re) :
    δ ^ 2 ≤ ‖z ^ 2 + (t : ℂ) ^ 2‖ := by
  have hz_re_nonneg : 0 ≤ z.re :=
    le_trans hδ_nonneg hδ_le_re
  have hplus :
      δ ≤ ‖z + (t : ℂ) * Complex.I‖ :=
    le_trans hδ_le_re
      (Complex.re_le_norm_add_real_mul_I hz_re_nonneg t)
  have hminus :
      δ ≤ ‖z - (t : ℂ) * Complex.I‖ :=
    le_trans hδ_le_re
      (Complex.re_le_norm_sub_real_mul_I hz_re_nonneg t)
  have hmul :
      δ * δ ≤
        ‖z + (t : ℂ) * Complex.I‖ *
          ‖z - (t : ℂ) * Complex.I‖ :=
    mul_le_mul hplus hminus
      hδ_nonneg
      (norm_nonneg (z + (t : ℂ) * Complex.I))
  have hnorm_mul :
      ‖(z + (t : ℂ) * Complex.I) *
          (z - (t : ℂ) * Complex.I)‖ =
        ‖z + (t : ℂ) * Complex.I‖ *
          ‖z - (t : ℂ) * Complex.I‖ :=
    norm_mul
      (z + (t : ℂ) * Complex.I)
      (z - (t : ℂ) * Complex.I)
  have hfactor :
      (z + (t : ℂ) * Complex.I) *
          (z - (t : ℂ) * Complex.I) =
        z ^ 2 + (t : ℂ) ^ 2 :=
    Complex.add_mul_sub_real_mul_I_eq_sq_add_sq z t
  have htarget :
      δ * δ ≤ ‖z ^ 2 + (t : ℂ) ^ 2‖ :=
    Eq.subst
      (motive := fun x : ℂ => δ * δ ≤ ‖x‖)
      hfactor
      (Eq.subst
        (motive := fun x : ℝ => δ * δ ≤ x)
        hnorm_mul.symm
        hmul)
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ ‖z ^ 2 + (t : ℂ) ^ 2‖)
      (sq δ).symm
      htarget

/-- For `t > 0`, the Binet arctangent argument avoids the branch point `I`
in the open right half-plane. -/
theorem Complex.binet_arctan_argument_ne_I
    {t : ℝ} {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    (t : ℂ) / w ≠ Complex.I := by
  intro h
  have hw_ne : w ≠ 0 := Complex.ne_zero_of_re_pos hw_re_pos
  have hzero : w + (t : ℂ) * Complex.I = 0 := by
    have hmul : (t : ℂ) = Complex.I * w := by
      calc
        (t : ℂ) = ((t : ℂ) / w) * w := by
          exact (div_mul_cancel₀ (t : ℂ) hw_ne).symm
        _ = Complex.I * w := by
          exact congrArg (fun u : ℂ => u * w) h
    calc
      w + (t : ℂ) * Complex.I
          = w + (Complex.I * w) * Complex.I := by
            exact congrArg (fun u : ℂ => w + u * Complex.I) hmul
      _ = 0 := Complex.add_I_mul_mul_I_eq_zero w
  exact (Complex.add_real_mul_I_ne_zero_of_re_pos hw_re_pos) hzero

/-- For `t > 0`, the Binet arctangent argument avoids the branch point `-I`
in the open right half-plane. -/
theorem Complex.binet_arctan_argument_ne_negI
    {t : ℝ} {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    (t : ℂ) / w ≠ -Complex.I := by
  intro h
  have hw_ne : w ≠ 0 := Complex.ne_zero_of_re_pos hw_re_pos
  have hzero : w - (t : ℂ) * Complex.I = 0 := by
    have hmul : (t : ℂ) = -Complex.I * w := by
      calc
        (t : ℂ) = ((t : ℂ) / w) * w := by
          exact (div_mul_cancel₀ (t : ℂ) hw_ne).symm
        _ = -Complex.I * w := by
          exact congrArg (fun u : ℂ => u * w) h
    calc
      w - (t : ℂ) * Complex.I
          = w - (-Complex.I * w) * Complex.I := by
            exact congrArg (fun u : ℂ => w - u * Complex.I) hmul
      _ = 0 := Complex.sub_neg_I_mul_mul_I_eq_zero w
  exact (Complex.sub_real_mul_I_ne_zero_of_re_pos hw_re_pos) hzero

/-- The denominator in the Cayley transform defining `Complex.arctan` is
nonzero away from the branch point `-I`. -/
theorem Complex.one_sub_mul_I_ne_zero_of_ne_negI
    {z : ℂ}
    (hz : z ≠ -Complex.I) :
    1 - z * Complex.I ≠ 0 := by
  intro hzero
  have hmul : z * Complex.I = 1 :=
    (sub_eq_zero.mp hzero).symm
  have harg : z = -Complex.I := by
    have hnegI_mul_I : (-Complex.I) * Complex.I = 1 := by
      calc
        (-Complex.I) * Complex.I = -(Complex.I * Complex.I) := by
          exact neg_mul Complex.I Complex.I
        _ = -(-1 : ℂ) := by
          exact congrArg Neg.neg Complex.I_mul_I
        _ = 1 := neg_neg (1 : ℂ)
    have hright :
        z * Complex.I = (-Complex.I) * Complex.I :=
      hmul.trans hnegI_mul_I.symm
    exact mul_right_cancel₀ Complex.I_ne_zero hright
  exact hz harg

/-- Imaginary part of the Cayley transform used in the principal-log
definition of complex arctangent. -/
theorem Complex.arctan_cayley_im_eq
    (z : ℂ) :
    ((1 + z * Complex.I) / (1 - z * Complex.I)).im =
      2 * z.re / Complex.normSq (1 - z * Complex.I) := by
  have hnum_im : (1 + z * Complex.I).im = z.re := by
    calc
      (1 + z * Complex.I).im = (1 : ℂ).im + (z * Complex.I).im := by
        exact Complex.add_im 1 (z * Complex.I)
      _ = 0 + (z * Complex.I).im := by
        rfl
      _ = 0 + z.re := by
        exact congrArg (fun u : ℝ => 0 + u) (Complex.mul_I_im z)
      _ = z.re := zero_add z.re
  have hnum_re : (1 + z * Complex.I).re = 1 - z.im := by
    calc
      (1 + z * Complex.I).re = (1 : ℂ).re + (z * Complex.I).re := by
        exact Complex.add_re 1 (z * Complex.I)
      _ = 1 + (z * Complex.I).re := by
        rfl
      _ = 1 + -z.im := by
        exact congrArg (fun u : ℝ => 1 + u) (Complex.mul_I_re z)
      _ = 1 - z.im := by
        exact Eq.symm (sub_eq_add_neg 1 z.im)
  have hden_re : (1 - z * Complex.I).re = 1 + z.im := by
    calc
      (1 - z * Complex.I).re = (1 : ℂ).re - (z * Complex.I).re := by
        exact Complex.sub_re 1 (z * Complex.I)
      _ = 1 - (z * Complex.I).re := by
        rfl
      _ = 1 - -z.im := by
        exact congrArg (fun u : ℝ => 1 - u) (Complex.mul_I_re z)
      _ = 1 + z.im := sub_neg_eq_add 1 z.im
  have hden_im : (1 - z * Complex.I).im = -z.re := by
    calc
      (1 - z * Complex.I).im = (1 : ℂ).im - (z * Complex.I).im := by
        exact Complex.sub_im 1 (z * Complex.I)
      _ = 0 - (z * Complex.I).im := by
        rfl
      _ = 0 - z.re := by
        exact congrArg (fun u : ℝ => 0 - u) (Complex.mul_I_im z)
      _ = -z.re := zero_sub z.re
  have hdiv :
      ((1 + z * Complex.I) / (1 - z * Complex.I)).im =
        (1 + z * Complex.I).im * (1 - z * Complex.I).re /
            Complex.normSq (1 - z * Complex.I) -
          (1 + z * Complex.I).re * (1 - z * Complex.I).im /
            Complex.normSq (1 - z * Complex.I) :=
    Complex.div_im _ _
  calc
    ((1 + z * Complex.I) / (1 - z * Complex.I)).im =
        (1 + z * Complex.I).im * (1 - z * Complex.I).re /
            Complex.normSq (1 - z * Complex.I) -
          (1 + z * Complex.I).re * (1 - z * Complex.I).im /
            Complex.normSq (1 - z * Complex.I) := hdiv
    _ = z.re * (1 + z.im) / Complex.normSq (1 - z * Complex.I) -
          (1 - z.im) * (-z.re) / Complex.normSq (1 - z * Complex.I) := by
      exact congrArg₂ HSub.hSub
        (congrArg₂ HDiv.hDiv
          (congrArg₂ HMul.hMul hnum_im hden_re)
          rfl)
        (congrArg₂ HDiv.hDiv
          (congrArg₂ HMul.hMul hnum_re hden_im)
          rfl)
    _ = 2 * z.re / Complex.normSq (1 - z * Complex.I) := by
      exact Real.cayley_im_div_identity z.re z.im
        (Complex.normSq (1 - z * Complex.I))

/-- For `t > 0` and `0 < w.re`, the Cayley transform appearing in the
principal-log definition of `Complex.arctan ((t : ℂ) / w)` lies in the slit
plane, so the principal logarithm is differentiable there. -/
theorem Complex.binet_arctan_log_argument_mem_slitPlane
    {t : ℝ} {w : ℂ}
    (ht : 0 < t)
    (hw_re_pos : 0 < w.re) :
    (1 + ((t : ℂ) / w) * Complex.I) /
        (1 - ((t : ℂ) / w) * Complex.I) ∈ Complex.slitPlane := by
  let z : ℂ := (t : ℂ) / w
  have harg_ne_negI :
      z ≠ -Complex.I :=
    Complex.binet_arctan_argument_ne_negI hw_re_pos
  have hden_ne :
      1 - z * Complex.I ≠ 0 :=
    Complex.one_sub_mul_I_ne_zero_of_ne_negI harg_ne_negI
  have hw_ne : w ≠ 0 :=
    Complex.ne_zero_of_re_pos hw_re_pos
  have hw_normSq_pos : 0 < Complex.normSq w :=
    (Complex.normSq_pos).mpr hw_ne
  have hz_re_pos : 0 < z.re := by
    have hdiv_re :
        z.re =
          ((t : ℂ).re * w.re / Complex.normSq w) +
            ((t : ℂ).im * w.im / Complex.normSq w) := by
      exact Complex.div_re (t : ℂ) w
    have hreal_re : (t : ℂ).re = t := rfl
    have hreal_im : (t : ℂ).im = 0 := rfl
    have hmain_pos : 0 < t * w.re / Complex.normSq w :=
      div_pos (mul_pos ht hw_re_pos) hw_normSq_pos
    calc
      0 < t * w.re / Complex.normSq w := hmain_pos
      _ = (t * w.re / Complex.normSq w) + 0 := by
        exact Eq.symm (add_zero (t * w.re / Complex.normSq w))
      _ =
          ((t : ℂ).re * w.re / Complex.normSq w) +
            ((t : ℂ).im * w.im / Complex.normSq w) := by
        exact Eq.symm
          (congrArg₂ HAdd.hAdd
            (congrArg₂ HDiv.hDiv
              (congrArg₂ HMul.hMul hreal_re rfl)
              rfl)
            (Eq.trans
              (congrArg₂ HDiv.hDiv
                (congrArg₂ HMul.hMul hreal_im rfl)
                rfl)
              (Eq.trans
                (congrArg (fun u : ℝ => u / Complex.normSq w) (zero_mul w.im))
                (zero_div (Complex.normSq w)))))
      _ = z.re := hdiv_re.symm
  have hden_normSq_pos :
      0 < Complex.normSq (1 - z * Complex.I) :=
    (Complex.normSq_pos).mpr hden_ne
  have him_pos :
      0 <
        ((1 + z * Complex.I) / (1 - z * Complex.I)).im := by
    calc
      0 < 2 * z.re / Complex.normSq (1 - z * Complex.I) :=
        div_pos (mul_pos two_pos hz_re_pos) hden_normSq_pos
      _ = ((1 + z * Complex.I) / (1 - z * Complex.I)).im :=
        (Complex.arctan_cayley_im_eq z).symm
  exact
    Complex.mem_slitPlane_iff.mpr
      (Or.inr (ne_of_gt him_pos))

end

end LFunctions
end Boundary
