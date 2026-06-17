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

    {x : ℝ}
    (hx : 0 < x) :
    Complex.log (Complex.Gamma (x : ℂ)) =
      Complex.binetLogGammaMainTerm (x : ℂ) +
        Complex.binetSecondFormulaRemainder (x : ℂ) := by
  have hbranch :
      Complex.binetLogGammaBranch (x : ℂ) =
        Complex.log (Complex.Gamma (x : ℂ)) :=
    Complex.binetLogGammaBranch_eq_principalLog_Gamma_of_posReal_owner hx
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
            exact add_eq_zero_iff_eq_neg.mp hzero
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
            exact sub_eq_zero.mp hzero
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
      exact ((hasDerivAt_id' z).mul_const Complex.I).const_add 1
    have hden :
        HasDerivAt (fun u : ℂ => 1 - u * Complex.I) (-Complex.I) z := by
      exact ((hasDerivAt_id' z).mul_const Complex.I).const_sub 1
    have hdiv := hnum.div hden hden_ne
    exact by
      exact hdiv
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
    have hmul' := congrArg (fun u : ℂ => u * (-Complex.I)) hmul
    have hI : (Complex.I : ℂ) * Complex.I = -1 := by
      exact Complex.I_mul_I
    have hmul'' : z * Complex.I * (-Complex.I) = -Complex.I := by
      -- transport the identity through the right multiplication
      exact hmul'.trans (one_mul (-Complex.I))
    exact hmul''
  exact hz harg

/-- Imaginary part of the Cayley transform used in the principal-log
definition of complex arctangent. -/
theorem Complex.arctan_cayley_im_eq
    (z : ℂ) :
    ((1 + z * Complex.I) / (1 - z * Complex.I)).im =
      2 * z.re / Complex.normSq (1 - z * Complex.I) := by
  exact Complex.div_im _ _

/-- For `t > 0` and `0 < w.re`, the Cayley transform appearing in the
principal-log definition of `Complex.arctan ((t : ℂ) / w)` lies in the slit
plane, so the principal logarithm is differentiable there. -/
theorem Complex.binet_arctan_log_argument_mem_slitPlane

end

end LFunctions
end Boundary
