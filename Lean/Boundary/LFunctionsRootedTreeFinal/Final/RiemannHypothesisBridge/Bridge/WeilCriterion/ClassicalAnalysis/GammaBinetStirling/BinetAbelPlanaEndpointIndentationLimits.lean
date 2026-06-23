import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaResidueAccounting

/-!
# Endpoint indentation limits for finite Abel-Plana

This file owns the endpoint semicircle principal-part and remainder estimates,
and the limit identifying deleted boundary indentation contributions with
principal-value endpoint residue terms.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- The left endpoint semicircle has angular length `π`. -/
theorem Real.leftEndpointSemicircle_angleLength :
    Real.pi / 2 - (-(Real.pi / 2)) = Real.pi := by
  exact
    Eq.trans
      (sub_neg_eq_add (Real.pi / 2) (Real.pi / 2))
      (add_halves Real.pi)

/-- The right endpoint semicircle has angular length `π`. -/
theorem Real.rightEndpointSemicircle_angleLength :
    3 * Real.pi / 2 - Real.pi / 2 = Real.pi := by
  have hthree_nat :
      (3 : ℝ) = (1 : ℝ) + 1 + 1 := by
    calc
      (3 : ℝ) = (((1 + 1 + 1 : ℕ) : ℝ)) := by
        exact Eq.refl _
      _ = ((1 + 1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) := by
        exact Nat.cast_add (1 + 1) 1
      _ = (((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ)) + ((1 : ℕ) : ℝ) := by
        exact congrArg
          (fun z : ℝ => z + ((1 : ℕ) : ℝ))
          (Nat.cast_add 1 1)
      _ = (1 : ℝ) + 1 + 1 := by
        have hone : (((1 : ℕ) : ℝ) = 1) :=
          Nat.cast_one
        exact
          Eq.trans
            (congrArg
              (fun z : ℝ => (z + ((1 : ℕ) : ℝ)) + ((1 : ℕ) : ℝ))
              hone)
            (Eq.trans
              (congrArg
                (fun z : ℝ => ((1 : ℝ) + z) + ((1 : ℕ) : ℝ))
                hone)
              (congrArg
                (fun z : ℝ => ((1 : ℝ) + 1) + z)
                hone))
  have htwo_half :
      (Real.pi + Real.pi) / 2 = Real.pi := by
    exact Eq.trans (add_div Real.pi Real.pi 2) (add_halves Real.pi)
  have hthree :
      (3 : ℝ) * Real.pi / 2 =
        Real.pi + Real.pi / 2 := by
    calc
      (3 : ℝ) * Real.pi / 2 =
          (((1 : ℝ) + 1 + 1) * Real.pi) / 2 := by
        exact congrArg (fun z : ℝ => z * Real.pi / 2) hthree_nat
      _ = (((Real.pi + Real.pi) + Real.pi) / 2) := by
        have hone_mul : (1 : ℝ) * Real.pi = Real.pi :=
          one_mul Real.pi
        have hprod :
            ((1 : ℝ) + 1 + 1) * Real.pi =
              (Real.pi + Real.pi) + Real.pi := by
          exact
            Eq.trans
              (add_mul ((1 : ℝ) + 1) 1 Real.pi)
              (Eq.trans
                (congrArg
                  (fun z : ℝ => z + 1 * Real.pi)
                  (Eq.trans
                    (add_mul (1 : ℝ) 1 Real.pi)
                    (congrArg₂ HAdd.hAdd hone_mul hone_mul)))
                (congrArg
                  (fun z : ℝ => (Real.pi + Real.pi) + z)
                  hone_mul))
        exact congrArg (fun z : ℝ => z / 2) hprod
      _ = (Real.pi + Real.pi) / 2 + Real.pi / 2 := by
        exact add_div (Real.pi + Real.pi) Real.pi 2
      _ = Real.pi + Real.pi / 2 := by
        exact congrArg
          (fun z : ℝ => z + Real.pi / 2)
          htwo_half
  exact
    Eq.trans
      (congrArg
        (fun z : ℝ => z - Real.pi / 2)
        hthree)
      (add_sub_cancel_right Real.pi (Real.pi / 2))

/-- Cauchy-denominator cancellation along a complex endpoint arc. -/
theorem Complex.div_mul_I_mul_cancel
    (R D : ℂ)
    (hD : D ≠ 0) :
    (R / D) * (Complex.I * D) = Complex.I * R := by
  calc
    (R / D) * (Complex.I * D) =
        (R / D) * (D * Complex.I) := by
      exact congrArg
        (fun z : ℂ => (R / D) * z)
        (mul_comm Complex.I D)
    _ = ((R / D) * D) * Complex.I := by
      exact (mul_assoc (R / D) D Complex.I).symm
    _ = R * Complex.I := by
      exact congrArg
        (fun z : ℂ => z * Complex.I)
        (div_mul_cancel₀ R hD)
    _ = Complex.I * R := by
      exact mul_comm R Complex.I

/-- Normalizing a semicircle principal part by `2πi` gives half the residue. -/
theorem Complex.two_pi_I_normalizes_pi_I_to_half
    (R : ℂ) :
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ((Real.pi : ℂ) * (Complex.I * R)) =
      R / 2 := by
  have hπI :
      (Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
      Complex.I_ne_zero
  have hnum :
      (Real.pi : ℂ) * (Complex.I * R) =
        R * ((Real.pi : ℂ) * Complex.I) := by
    calc
      (Real.pi : ℂ) * (Complex.I * R) =
          (Real.pi : ℂ) * (R * Complex.I) := by
        exact congrArg
          (fun z : ℂ => (Real.pi : ℂ) * z)
          (mul_comm Complex.I R)
      _ = ((Real.pi : ℂ) * R) * Complex.I := by
        exact (mul_assoc (Real.pi : ℂ) R Complex.I).symm
      _ = (R * (Real.pi : ℂ)) * Complex.I := by
        exact congrArg
          (fun z : ℂ => z * Complex.I)
          (mul_comm (Real.pi : ℂ) R)
      _ = R * ((Real.pi : ℂ) * Complex.I) := by
        exact mul_assoc R (Real.pi : ℂ) Complex.I
  have hden :
      (2 : ℂ) * (Real.pi : ℂ) * Complex.I =
        (2 : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
    exact mul_assoc (2 : ℂ) (Real.pi : ℂ) Complex.I
  calc
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ((Real.pi : ℂ) * (Complex.I * R)) =
        ((Real.pi : ℂ) * (Complex.I * R)) /
          ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by
      exact inv_mul_eq_div
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)
        ((Real.pi : ℂ) * (Complex.I * R))
    _ =
        (R * ((Real.pi : ℂ) * Complex.I)) /
          ((2 : ℂ) * ((Real.pi : ℂ) * Complex.I)) := by
      exact congrArg₂ HDiv.hDiv hnum hden
    _ = R / 2 := by
      exact mul_div_mul_right R (2 : ℂ) hπI

/-- Splitting a removable endpoint numerator into residue plus defect after
arc-denominator transport. -/
theorem Complex.endpointArc_principal_remainder_split
    (R E D : ℂ)
    (hD : D ≠ 0) :
    (D⁻¹ * E) * (Complex.I * D) =
      (R / D) * (Complex.I * D) +
        ((E - R) / D) * (Complex.I * D) := by
  have hdecomp : R + (E - R) = E := by
    calc
      R + (E - R) = (E - R) + R := by
        exact add_comm R (E - R)
      _ = E := by
        exact sub_add_cancel E R
  have hleft :
      (D⁻¹ * E) * (Complex.I * D) = Complex.I * E := by
    calc
      (D⁻¹ * E) * (Complex.I * D) =
          (E / D) * (Complex.I * D) := by
        exact congrArg
          (fun z : ℂ => z * (Complex.I * D))
          (inv_mul_eq_div D E)
      _ = Complex.I * E := by
        exact Complex.div_mul_I_mul_cancel E D hD
  have hright :
      (R / D) * (Complex.I * D) +
          ((E - R) / D) * (Complex.I * D) =
        Complex.I * E := by
    calc
      (R / D) * (Complex.I * D) +
          ((E - R) / D) * (Complex.I * D) =
          Complex.I * R + Complex.I * (E - R) := by
        exact congrArg₂ HAdd.hAdd
          (Complex.div_mul_I_mul_cancel R D hD)
          (Complex.div_mul_I_mul_cancel (E - R) D hD)
      _ = Complex.I * (R + (E - R)) := by
        exact Eq.symm (mul_add Complex.I R (E - R))
      _ = Complex.I * E := by
        exact congrArg (fun z : ℂ => Complex.I * z) hdecomp
  exact hleft.trans hright.symm

/-- Endpoint arc derivative factor, written in the definition-facing
left-associated form, equals the cancellation-facing product form. -/
theorem Complex.endpointArc_derivativeFactor_assoc
    (ρ θ : ℝ) :
    Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) =
      Complex.I * ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
  exact mul_assoc Complex.I (ρ : ℂ) (Complex.exp (Complex.I * (θ : ℂ)))

/-- Rearrangement of the endpoint-remainder integral majorant product. -/
theorem Real.endpointRemainder_majorant_product_assoc
    (A C L : ℝ) :
    A * (C * L) = A * L * C := by
  calc
    A * (C * L) = A * (L * C) := by
      exact congrArg (fun z : ℝ => A * z) (mul_comm C L)
    _ = A * L * C := by
      exact Eq.symm (mul_assoc A L C)

/-- A zero norm is inside every positive ball around zero. -/
theorem Real.zero_norm_mem_ball_of_pos
    {ε x : ℝ}
    (hx : x = 0)
    (hε : 0 < ε) :
    x ∈ Metric.ball (0 : ℝ) ε := by
  have hdist : dist x 0 = 0 := by
    exact Eq.trans (congrArg (fun y : ℝ => dist y 0) hx) (dist_self 0)
  exact Metric.mem_ball.mpr (hdist.symm ▸ hε)

/-- A strict norm bound is exactly membership in the neighborhood ball around
zero. -/
theorem Real.mem_zero_ball_of_lt
    {ε x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (h : x < ε) :
    x ∈ Metric.ball (0 : ℝ) ε := by
  have hdist : dist x 0 = x :=
    calc
      dist x 0 = |x - 0| := Real.dist_eq x 0
      _ = |x| := congrArg abs (sub_zero x)
      _ = x := abs_of_nonneg hx_nonneg
  exact Metric.mem_ball.mpr (hdist.symm ▸ h)

/-- Cancelling the positive endpoint-remainder majorant scale. -/
theorem Real.endpointRemainder_scale_cancel
    {A ε : ℝ}
    (hA : A ≠ 0) :
    A * (ε / (2 * A)) = ε / 2 := by
  calc
    A * (ε / (2 * A)) = A * ε / (2 * A) := by
      exact Eq.symm (mul_div_assoc A ε (2 * A))
    _ = ε * A / (2 * A) := by
      exact congrArg
        (fun z : ℝ => z / (2 * A))
        (mul_comm A ε)
    _ = ε / 2 := by
      exact mul_div_mul_right ε (2 : ℝ) hA

/-- Distance from a nonnegative real norm to zero is the norm itself. -/
theorem Real.dist_norm_to_zero_eq_self
    {x : ℝ}
    (hx : 0 ≤ x) :
    dist x 0 = x := by
  have habs : |x| = x := abs_of_nonneg hx
  calc
    dist x 0 = |x - 0| := Real.dist_eq x 0
    _ = |x| := congrArg abs (sub_zero x)
    _ = x := habs

/-- A complex point is in a metric ball when its norm displacement is below
the radius. -/
theorem Complex.mem_ball_of_norm_sub_lt
    {z c : ℂ}
    {δ : ℝ}
    (h : ‖z - c‖ < δ) :
    z ∈ Metric.ball c δ := by
  have hdist : dist z c = ‖z - c‖ := dist_eq_norm z c
  exact Metric.mem_ball.mpr (hdist.symm ▸ h)

/-- Pointwise cancellation of the simple-pole principal part along an endpoint
arc. -/
theorem Complex.finiteAbelPlana_log_endpointSemicirclePrincipalPart_integrand_eq_const
    {w : ℂ}
    (n : ℕ)
    {ρ : ℝ}
    (hρ : ρ ≠ 0)
    (θ : ℝ) :
    ((Complex.finiteAbelPlanaLogIntegerResidue w n) /
        ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
      (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
        Complex.I * Complex.finiteAbelPlanaLogIntegerResidue w n := by
  have hρc : (ρ : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr hρ
  have hexp : Complex.exp (Complex.I * (θ : ℂ)) ≠ 0 :=
    Complex.exp_ne_zero _
  have hprod : (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) ≠ 0 :=
    mul_ne_zero hρc hexp
  exact
    Eq.trans
      (congrArg
        (fun z : ℂ =>
          (Complex.finiteAbelPlanaLogIntegerResidue w n /
            ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) * z)
        (Complex.endpointArc_derivativeFactor_assoc ρ θ))
      (Complex.div_mul_I_mul_cancel
        (Complex.finiteAbelPlanaLogIntegerResidue w n)
        ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
        hprod)

/-- The normalized principal-part integral over a positive semicircle is half
the local residue. -/
theorem Complex.finiteAbelPlana_log_endpointSemicirclePrincipalPart_integral_eq_halfResidue
    {w : ℂ}
    (n : ℕ)
    (a b : ℝ)
    (hangle : b - a = Real.pi)
    {ρ : ℝ}
    (hρ : ρ ≠ 0) :
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
      ∫ θ : ℝ in a..b,
        ((Complex.finiteAbelPlanaLogIntegerResidue w n) /
            ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
        Complex.finiteAbelPlanaLogIntegerResidue w n / 2 := by
  have hintegral :
      ∫ θ : ℝ in a..b,
        ((Complex.finiteAbelPlanaLogIntegerResidue w n) /
            ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
        (b - a : ℝ) •
          (Complex.I * Complex.finiteAbelPlanaLogIntegerResidue w n) := by
    calc
      ∫ θ : ℝ in a..b,
          ((Complex.finiteAbelPlanaLogIntegerResidue w n) /
              ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
        ∫ _θ : ℝ in a..b,
          Complex.I * Complex.finiteAbelPlanaLogIntegerResidue w n :=
        intervalIntegral.integral_congr
          (fun θ _hθ =>
            Complex.finiteAbelPlana_log_endpointSemicirclePrincipalPart_integrand_eq_const
              n hρ θ)
      _ =
        (b - a : ℝ) •
          (Complex.I * Complex.finiteAbelPlanaLogIntegerResidue w n) :=
        intervalIntegral.integral_const
          (Complex.I * Complex.finiteAbelPlanaLogIntegerResidue w n)
  calc
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
      ∫ θ : ℝ in a..b,
        ((Complex.finiteAbelPlanaLogIntegerResidue w n) /
            ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          ((b - a : ℝ) •
            (Complex.I * Complex.finiteAbelPlanaLogIntegerResidue w n)) := by
      exact congrArg
        (fun z : ℂ => ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ * z)
        hintegral
    _ =
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          ((Real.pi : ℂ) * (Complex.I * Complex.finiteAbelPlanaLogIntegerResidue w n)) := by
      have hangle_smul :
          (b - a : ℝ) •
              (Complex.I * Complex.finiteAbelPlanaLogIntegerResidue w n) =
            Real.pi •
              (Complex.I * Complex.finiteAbelPlanaLogIntegerResidue w n) :=
        congrArg
          (fun x : ℝ =>
            x • (Complex.I * Complex.finiteAbelPlanaLogIntegerResidue w n))
          hangle
      have hpi_smul :
          Real.pi •
              (Complex.I * Complex.finiteAbelPlanaLogIntegerResidue w n) =
            (Real.pi : ℂ) *
              (Complex.I * Complex.finiteAbelPlanaLogIntegerResidue w n) :=
        (Complex.real_smul :
          Real.pi •
              (Complex.I * Complex.finiteAbelPlanaLogIntegerResidue w n) =
            (Real.pi : ℂ) *
              (Complex.I * Complex.finiteAbelPlanaLogIntegerResidue w n))
      exact congrArg
        (fun z : ℂ => ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ * z)
        (hangle_smul.trans hpi_smul)
    _ = Complex.finiteAbelPlanaLogIntegerResidue w n / 2 := by
      exact Complex.two_pi_I_normalizes_pi_I_to_half
        (Complex.finiteAbelPlanaLogIntegerResidue w n)

/-- The principal part of a simple pole contributes half the normalized residue
on a positively oriented semicircle. -/
theorem Complex.finiteAbelPlana_log_endpointSemicirclePrincipalPart_tendsto_halfResidue
    {w : ℂ}
    (n : ℕ)
    (a b : ℝ)
    (hangle : b - a = Real.pi) :
    Filter.Tendsto
      (fun ρ : ℝ =>
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          ∫ θ : ℝ in a..b,
            ((Complex.finiteAbelPlanaLogIntegerResidue w n) /
                ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.finiteAbelPlanaLogIntegerResidue w n / 2)) := by
  have hevent :
      (fun ρ : ℝ =>
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          ∫ θ : ℝ in a..b,
            ((Complex.finiteAbelPlanaLogIntegerResidue w n) /
                ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun _ρ : ℝ => Complex.finiteAbelPlanaLogIntegerResidue w n / 2) := by
    exact
      Filter.mem_of_superset self_mem_nhdsWithin
        (fun ρ hρpos =>
          Complex.finiteAbelPlana_log_endpointSemicirclePrincipalPart_integral_eq_halfResidue
            n a b hangle (ne_of_gt hρpos))
  exact tendsto_const_nhds.congr' hevent.symm

/-- The endpoint-arc vector has norm exactly the radius. -/
theorem Complex.norm_endpointSemicircleArcVector
    (ρ θ : ℝ) :
    ‖(ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))‖ = |ρ| := by
  have hcomm :
      Complex.I * (θ : ℂ) = (θ : ℂ) * Complex.I := by
    exact mul_comm Complex.I (θ : ℂ)
  calc
    ‖(ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))‖ =
        ‖(ρ : ℂ)‖ * ‖Complex.exp (Complex.I * (θ : ℂ))‖ := by
      exact norm_mul (ρ : ℂ) (Complex.exp (Complex.I * (θ : ℂ)))
    _ = |ρ| * ‖Complex.exp ((θ : ℂ) * Complex.I)‖ := by
      exact congrArg₂ HMul.hMul
        (RCLike.norm_ofReal ρ)
        (congrArg (fun z : ℂ => ‖Complex.exp z‖) hcomm)
    _ = |ρ| * 1 := by
      exact congrArg
        (fun x : ℝ => |ρ| * x)
        (Complex.norm_exp_ofReal_mul_I θ)
    _ = |ρ| := by
      exact mul_one |ρ|

/-- On a nonzero endpoint arc, the Cauchy denominator cancels against `dz`. -/
theorem Complex.endpointSemicircleRemainder_integrand_eq_I_mul_defect
    {w : ℂ}
    (n : ℕ)
    {ρ : ℝ}
    (hρ : ρ ≠ 0)
    (θ : ℝ) :
    ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
          ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
        Complex.finiteAbelPlanaLogIntegerResidue w n) /
        ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
      (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
        Complex.I *
          (Complex.finiteAbelPlanaLogIntegerResidueExtension w n
            ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
          Complex.finiteAbelPlanaLogIntegerResidue w n) := by
  have hden :
      (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) ≠ 0 :=
    by
      have hρc : (ρ : ℂ) ≠ 0 := by
        exact Complex.ofReal_ne_zero.mpr hρ
      exact mul_ne_zero hρc (Complex.exp_ne_zero _)
  exact
    Eq.trans
      (congrArg
        (fun z : ℂ =>
          ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
              ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
            Complex.finiteAbelPlanaLogIntegerResidue w n) /
              ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) * z)
        (Complex.endpointArc_derivativeFactor_assoc ρ θ))
      (Complex.div_mul_I_mul_cancel
        (Complex.finiteAbelPlanaLogIntegerResidueExtension w n
          ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
          Complex.finiteAbelPlanaLogIntegerResidue w n)
        ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
        hden)

/-- The endpoint-arc remainder integrand is bounded by the removable numerator
defect after denominator cancellation. -/
theorem Complex.norm_endpointSemicircleRemainder_integrand_le
    {w : ℂ}
    (n : ℕ)
    {ρ : ℝ}
    (hρ : ρ ≠ 0)
    {C : ℝ}
    {θ : ℝ}
    (hC :
      ‖Complex.finiteAbelPlanaLogIntegerResidueExtension w n
          ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
        Complex.finiteAbelPlanaLogIntegerResidue w n‖ ≤ C) :
    ‖((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
          ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
        Complex.finiteAbelPlanaLogIntegerResidue w n) /
        ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
      (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖ ≤ C := by
  calc
    ‖((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
          ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
        Complex.finiteAbelPlanaLogIntegerResidue w n) /
        ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
      (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖ =
        ‖Complex.I *
          (Complex.finiteAbelPlanaLogIntegerResidueExtension w n
            ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
          Complex.finiteAbelPlanaLogIntegerResidue w n)‖ := by
      exact congrArg norm
        (Complex.endpointSemicircleRemainder_integrand_eq_I_mul_defect
          n hρ θ)
    _ =
        ‖Complex.finiteAbelPlanaLogIntegerResidueExtension w n
          ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
        Complex.finiteAbelPlanaLogIntegerResidue w n‖ := by
      calc
        ‖Complex.I *
          (Complex.finiteAbelPlanaLogIntegerResidueExtension w n
            ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
          Complex.finiteAbelPlanaLogIntegerResidue w n)‖ =
            ‖Complex.I‖ *
              ‖Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
              Complex.finiteAbelPlanaLogIntegerResidue w n‖ :=
          norm_mul Complex.I
            (Complex.finiteAbelPlanaLogIntegerResidueExtension w n
              ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
            Complex.finiteAbelPlanaLogIntegerResidue w n)
        _ =
            1 *
              ‖Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
              Complex.finiteAbelPlanaLogIntegerResidue w n‖ := by
          exact congrArg
            (fun x : ℝ =>
              x *
                ‖Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                  ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
                Complex.finiteAbelPlanaLogIntegerResidue w n‖)
            Complex.norm_I
        _ =
            ‖Complex.finiteAbelPlanaLogIntegerResidueExtension w n
              ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
            Complex.finiteAbelPlanaLogIntegerResidue w n‖ :=
          one_mul _
    _ ≤ C := hC

/-- The removable regular remainder contributes zero on a shrinking endpoint
semicircle. -/
theorem Complex.norm_endpointSemicircleRemainderIntegral_le
    {w : ℂ}
    (_hw : 0 < w.re)
    (n : ℕ)
    (a b ρ : ℝ)
    (hρ : 0 < ρ)
    (C : ℝ)
    (hC :
      ∀ θ ∈ Ι a b,
        ‖Complex.finiteAbelPlanaLogIntegerResidueExtension w n
            ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
          Complex.finiteAbelPlanaLogIntegerResidue w n‖ ≤ C) :
    ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ∫ θ : ℝ in a..b,
          ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
              Complex.finiteAbelPlanaLogIntegerResidue w n) /
              ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖
      ≤ ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹‖ * |b - a| * C := by
  have hρne : ρ ≠ 0 := ne_of_gt hρ
  have hintegral :
      ‖∫ θ : ℝ in a..b,
          ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
              Complex.finiteAbelPlanaLogIntegerResidue w n) /
              ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖
        ≤ C * |b - a| := by
    exact intervalIntegral.norm_integral_le_of_norm_le_const
      (fun θ hθ =>
        Complex.norm_endpointSemicircleRemainder_integrand_le
          n hρne (hC θ hθ))
  calc
    ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ∫ θ : ℝ in a..b,
          ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
              Complex.finiteAbelPlanaLogIntegerResidue w n) /
              ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖ =
        ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹‖ *
          ‖∫ θ : ℝ in a..b,
            ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                  ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
                Complex.finiteAbelPlanaLogIntegerResidue w n) /
                ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖ := by
      exact norm_mul _ _
    _ ≤ ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹‖ * (C * |b - a|) := by
      exact mul_le_mul_of_nonneg_left hintegral (norm_nonneg _)
    _ = ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹‖ * |b - a| * C := by
      exact Real.endpointRemainder_majorant_product_assoc
        ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹‖ C |b - a|

/-- Uniform smallness of the removable numerator on shrinking endpoint arcs. -/
theorem Complex.eventually_endpointSemicircleRemainder_uniform_small
    {w : ℂ}
    (hw : 0 < w.re)
    (n : ℕ)
    (a b : ℝ)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ ρ : ℝ in 𝓝[>] (0 : ℝ),
      ∀ θ ∈ Ι a b,
        ‖Complex.finiteAbelPlanaLogIntegerResidueExtension w n
            ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
          Complex.finiteAbelPlanaLogIntegerResidue w n‖ ≤ ε := by
  have hcont :
      ContinuousAt
        (fun z : ℂ =>
          Complex.finiteAbelPlanaLogIntegerResidueExtension w n z)
        (n : ℂ) :=
    Complex.continuousAt_finiteAbelPlanaLogIntegerResidueExtension_at_pole
      hw n
  have hdist :
      ∀ᶠ z : ℂ in 𝓝 (n : ℂ),
        ‖Complex.finiteAbelPlanaLogIntegerResidueExtension w n z -
          Complex.finiteAbelPlanaLogIntegerResidue w n‖ ≤ ε := by
    have htend :
        Filter.Tendsto
          (fun z : ℂ =>
            Complex.finiteAbelPlanaLogIntegerResidueExtension w n z -
              Complex.finiteAbelPlanaLogIntegerResidue w n)
          (𝓝 (n : ℂ))
          (𝓝 0) := by
      have hres :
          Complex.finiteAbelPlanaLogIntegerResidueExtension w n (n : ℂ) =
            Complex.finiteAbelPlanaLogIntegerResidue w n :=
        Complex.finiteAbelPlana_log_integerResidueExtension_at_pole w n
      have hsub :
          Filter.Tendsto
            (fun z : ℂ =>
              Complex.finiteAbelPlanaLogIntegerResidueExtension w n z -
                Complex.finiteAbelPlanaLogIntegerResidue w n)
            (𝓝 (n : ℂ))
            (𝓝
              (Complex.finiteAbelPlanaLogIntegerResidueExtension w n (n : ℂ) -
                Complex.finiteAbelPlanaLogIntegerResidue w n)) :=
        hcont.sub continuousAt_const
      have hlimit_residue_sub :
          Filter.Tendsto
            (fun z : ℂ =>
              Complex.finiteAbelPlanaLogIntegerResidueExtension w n z -
                Complex.finiteAbelPlanaLogIntegerResidue w n)
            (𝓝 (n : ℂ))
            (𝓝
              (Complex.finiteAbelPlanaLogIntegerResidue w n -
                Complex.finiteAbelPlanaLogIntegerResidue w n)) :=
        hres ▸ hsub
      exact (sub_self (Complex.finiteAbelPlanaLogIntegerResidue w n)) ▸
        hlimit_residue_sub
    have hnorm :
        Filter.Tendsto
          (fun z : ℂ =>
            ‖Complex.finiteAbelPlanaLogIntegerResidueExtension w n z -
              Complex.finiteAbelPlanaLogIntegerResidue w n‖)
          (𝓝 (n : ℂ))
          (𝓝 0) := by
      have hnorm_zero :
          ‖(0 : ℂ)‖ = (0 : ℝ) :=
        norm_zero
      exact hnorm_zero ▸ htend.norm
    have hevent_dist :
        ∀ᶠ z : ℂ in 𝓝 (n : ℂ),
          dist
          (‖Complex.finiteAbelPlanaLogIntegerResidueExtension w n z -
            Complex.finiteAbelPlanaLogIntegerResidue w n‖)
            0 < ε :=
      (Metric.tendsto_nhds.1 hnorm) ε hε
    exact
      Filter.mem_of_superset hevent_dist
        (fun z hz =>
          let q : ℝ :=
            ‖Complex.finiteAbelPlanaLogIntegerResidueExtension w n z -
              Complex.finiteAbelPlanaLogIntegerResidue w n‖
          have hq_nonneg : 0 ≤ q := norm_nonneg _
          have hdist_eq : dist q 0 = q :=
            Real.dist_norm_to_zero_eq_self hq_nonneg
          have hlt : q < ε :=
            hdist_eq ▸ hz
          le_of_lt hlt)
  exact
    Exists.elim (Metric.mem_nhds_iff.1 hdist)
      (fun δ hδdata =>
        let hδpos : 0 < δ := hδdata.1
        let hδ : Metric.ball (n : ℂ) δ ⊆
            {z : ℂ |
              ‖Complex.finiteAbelPlanaLogIntegerResidueExtension w n z -
                Complex.finiteAbelPlanaLogIntegerResidue w n‖ ≤ ε} :=
          hδdata.2
        Filter.mem_of_superset
          (Ioo_mem_nhdsWithin_Ioi ⟨le_rfl, hδpos⟩)
          (fun ρ hρδ θ _hθ =>
            have hnorm_arc :
                ‖(ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))‖ = ρ := by
              calc
                ‖(ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))‖ = |ρ| :=
                  Complex.norm_endpointSemicircleArcVector ρ θ
                _ = ρ := abs_of_pos hρδ.1
            have hball :
                (n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) ∈
                  Metric.ball (n : ℂ) δ :=
              Complex.mem_ball_of_norm_sub_lt
                (calc
                  ‖(n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) -
                      (n : ℂ)‖ =
                      ‖(ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))‖ := by
                    exact congrArg norm
                      (add_sub_cancel_left (n : ℂ)
                        ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
                  _ = ρ := hnorm_arc
                  _ < δ := hρδ.2)
            hδ hball))

theorem Complex.finiteAbelPlana_log_endpointSemicircleRemainder_tendsto_zero
    {w : ℂ}
    (hw : 0 < w.re)
    (n : ℕ)
    (a b : ℝ) :
    Filter.Tendsto
      (fun ρ : ℝ =>
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          ∫ θ : ℝ in a..b,
            ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                  ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
                Complex.finiteAbelPlanaLogIntegerResidue w n) /
                ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (0 : ℂ)) := by
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (Metric.tendsto_nhds.2
      (fun ε hε =>
      let A : ℝ := ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹‖ * |b - a|
      have hAnonneg : 0 ≤ A := by
        exact mul_nonneg (norm_nonneg _) (abs_nonneg _)
      match lt_or_eq_of_le hAnonneg with
      | Or.inr hAzero_zero_left => by
        let hAzero : A = 0 := hAzero_zero_left.symm
        have hsmall :
            ∀ᶠ ρ : ℝ in 𝓝[>] (0 : ℝ),
              ∀ θ ∈ Ι a b,
                ‖Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                    ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
                  Complex.finiteAbelPlanaLogIntegerResidue w n‖ ≤ 1 :=
          Complex.eventually_endpointSemicircleRemainder_uniform_small
            hw n a b zero_lt_one
        exact
          Filter.mem_of_superset
            (Filter.inter_mem self_mem_nhdsWithin hsmall)
            (fun ρ hρdata =>
              have hρpos : 0 < ρ := hρdata.1
              have hbound :
                  ∀ θ ∈ Ι a b,
                    ‖Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                        ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
                      Complex.finiteAbelPlanaLogIntegerResidue w n‖ ≤ 1 := hρdata.2
              have hle :
                  ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                      ∫ θ : ℝ in a..b,
                        ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                              ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
                            Complex.finiteAbelPlanaLogIntegerResidue w n) /
                            ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
                          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖
                    ≤ A * 1 :=
                Complex.norm_endpointSemicircleRemainderIntegral_le
                  hw n a b ρ hρpos 1 hbound
              have hzero_le :
                  ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                      ∫ θ : ℝ in a..b,
                        ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                              ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
                            Complex.finiteAbelPlanaLogIntegerResidue w n) /
                            ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
                          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖
                    = 0 := by
                have hA_one_zero : A * 1 = 0 := by
                  exact Eq.trans
                    (congrArg (fun x : ℝ => x * 1) hAzero)
                    (zero_mul (1 : ℝ))
                have hle_zero :
                    ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                        ∫ θ : ℝ in a..b,
                          ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                                ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
                              Complex.finiteAbelPlanaLogIntegerResidue w n) /
                              ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
                            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖
                      ≤ 0 :=
                  hA_one_zero ▸ hle
                exact le_antisymm hle_zero (norm_nonneg _)
              Real.zero_norm_mem_ball_of_pos hzero_le hε)
      | Or.inl hApos => by
        have hsmall :
            ∀ᶠ ρ : ℝ in 𝓝[>] (0 : ℝ),
              ∀ θ ∈ Ι a b,
                ‖Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                    ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
                  Complex.finiteAbelPlanaLogIntegerResidue w n‖ ≤ ε / (2 * A) :=
          Complex.eventually_endpointSemicircleRemainder_uniform_small
            hw n a b (div_pos hε (mul_pos two_pos hApos))
        exact
          Filter.mem_of_superset
            (Filter.inter_mem self_mem_nhdsWithin hsmall)
            (fun ρ hρdata =>
              have hρpos : 0 < ρ := hρdata.1
              have hbound :
                  ∀ θ ∈ Ι a b,
                    ‖Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                        ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
                      Complex.finiteAbelPlanaLogIntegerResidue w n‖ ≤ ε / (2 * A) :=
                hρdata.2
              have hle :
                  ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                      ∫ θ : ℝ in a..b,
                        ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                              ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
                            Complex.finiteAbelPlanaLogIntegerResidue w n) /
                          ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
                          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖
                    ≤ A * (ε / (2 * A)) :=
                Complex.norm_endpointSemicircleRemainderIntegral_le
                  hw n a b ρ hρpos (ε / (2 * A)) hbound
              have hA_cancel : A * (ε / (2 * A)) = ε / 2 := by
                exact Real.endpointRemainder_scale_cancel (ne_of_gt hApos)
              have hhalf_lt : ε / 2 < ε := by
                exact half_lt_self hε
              have hlt :
                  ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                      ∫ θ : ℝ in a..b,
                        ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                              ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
                            Complex.finiteAbelPlanaLogIntegerResidue w n) /
                            ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
                          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖
                    < ε := by
                exact lt_of_le_of_lt (hA_cancel ▸ hle) hhalf_lt
              Real.mem_zero_ball_of_lt (norm_nonneg _) hlt)))
/-- Endpoint arc decomposition into the principal simple-pole part plus the
removable regular remainder. -/
theorem Complex.finiteAbelPlana_log_endpointSemicircle_integrand_eq_principal_add_remainder
    (w : ℂ)
    (n : ℕ)
    (ρ : ℝ)
    (hρ : ρ ≠ 0)
    (θ : ℝ) :
    Complex.finiteAbelPlanaLogRectangleIntegrand w
          ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
        (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
      ((Complex.finiteAbelPlanaLogIntegerResidue w n) /
          ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
        (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) +
      ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
            ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
          Complex.finiteAbelPlanaLogIntegerResidue w n) /
          ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
        (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
  have hρc : (ρ : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr hρ
  have hexp : Complex.exp (Complex.I * (θ : ℂ)) ≠ 0 :=
    Complex.exp_ne_zero _
  have hden :
      (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) ≠ 0 :=
    mul_ne_zero hρc hexp
  have hpoint_ne :
      (n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) ≠ (n : ℂ) := by
    exact fun h =>
      have hzero :
          (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) = 0 :=
        add_left_cancel
          (Eq.trans h (Eq.symm (add_zero (n : ℂ))))
      hden hzero
  have hrewrite :
      Complex.finiteAbelPlanaLogRectangleIntegrand w
          ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
        (((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))⁻¹ *
          Complex.finiteAbelPlanaLogIntegerResidueExtension w n
            ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) := by
    have hoff :
        Complex.finiteAbelPlanaLogIntegerResidueExtension w n
            ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
          (((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - (n : ℂ)) *
            Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) :=
      Complex.finiteAbelPlana_log_integerResidueExtension_eq_centered_off_pole
        w n hpoint_ne
    calc
      Complex.finiteAbelPlanaLogRectangleIntegrand w
          ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
        1 * Complex.finiteAbelPlanaLogRectangleIntegrand w
          ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
        exact (one_mul _).symm
      _ =
        (((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))⁻¹ *
            ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
          Complex.finiteAbelPlanaLogRectangleIntegrand w
            ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
        exact congrArg
          (fun u : ℂ =>
            u * Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
          (inv_mul_cancel₀ hden).symm
      _ =
        (((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))⁻¹ *
          (((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - (n : ℂ))) *
          Complex.finiteAbelPlanaLogRectangleIntegrand w
            ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
        exact congrArg
          (fun z : ℂ =>
            (((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))⁻¹ * z) *
              Complex.finiteAbelPlanaLogRectangleIntegrand w
                ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
          (Eq.symm
            (add_sub_cancel_left (n : ℂ)
              ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))))
      _ =
        ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))⁻¹ *
          ((((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - (n : ℂ)) *
            Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) := by
        exact mul_assoc _ _ _
      _ =
        ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))⁻¹ *
          Complex.finiteAbelPlanaLogIntegerResidueExtension w n
            ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
        exact congrArg
          (fun u : ℂ => ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))⁻¹ * u)
          hoff.symm
  calc
    Complex.finiteAbelPlanaLogRectangleIntegrand w
          ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
        (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
      (((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))⁻¹ *
          Complex.finiteAbelPlanaLogIntegerResidueExtension w n
            ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
        (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
      exact congrArg
        (fun z : ℂ => z * (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        hrewrite
    _ =
      ((Complex.finiteAbelPlanaLogIntegerResidue w n) /
          ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
        (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) +
      ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
            ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
          Complex.finiteAbelPlanaLogIntegerResidue w n) /
          ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
        (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
      have hsplit :=
        Complex.endpointArc_principal_remainder_split
          (Complex.finiteAbelPlanaLogIntegerResidue w n)
          (Complex.finiteAbelPlanaLogIntegerResidueExtension w n
            ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
          ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
          hden
      exact
        Eq.trans
          (congrArg
            (fun z : ℂ =>
              (((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))⁻¹ *
                  Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                    ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) * z)
            (Complex.endpointArc_derivativeFactor_assoc ρ θ))
          (Eq.trans hsplit
            (congrArg₂ HAdd.hAdd
              (congrArg
                (fun z : ℂ =>
                  (Complex.finiteAbelPlanaLogIntegerResidue w n /
                    ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) * z)
                (Complex.endpointArc_derivativeFactor_assoc ρ θ).symm)
              (congrArg
                (fun z : ℂ =>
                  ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                      ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
                    Complex.finiteAbelPlanaLogIntegerResidue w n) /
                      ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) * z)
                (Complex.endpointArc_derivativeFactor_assoc ρ θ).symm)))

/-- Full endpoint semicircle integrand before Laurent decomposition. -/
abbrev Complex.endpointSemicircleFullIntegrand
    (w : ℂ)
    (n : ℕ)
    (ρ : ℝ) :
    ℝ → ℂ :=
  fun θ : ℝ =>
    Complex.finiteAbelPlanaLogRectangleIntegrand w
        ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
      (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- Endpoint semicircle principal-part integrand. -/
abbrev Complex.endpointSemicirclePrincipalIntegrand
    (w : ℂ)
    (n : ℕ)
    (ρ : ℝ) :
    ℝ → ℂ :=
  fun θ : ℝ =>
    ((Complex.finiteAbelPlanaLogIntegerResidue w n) /
        ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
      (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- Endpoint semicircle removable-remainder integrand. -/
abbrev Complex.endpointSemicircleRemainderIntegrand
    (w : ℂ)
    (n : ℕ)
    (ρ : ℝ) :
    ℝ → ℂ :=
  fun θ : ℝ =>
    ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
          ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
        Complex.finiteAbelPlanaLogIntegerResidue w n) /
        ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
      (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- Normalized endpoint semicircle integral of an angle integrand. -/
abbrev Complex.endpointSemicircleNormalizedIntegral
    (a b : ℝ)
    (F : ℝ → ℂ) :
    ℂ :=
  ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
    ∫ θ : ℝ in a..b, F θ

/-- Normalized endpoint full arc integral. -/
abbrev Complex.endpointSemicircleFullIntegral
    (w : ℂ)
    (n : ℕ)
    (a b ρ : ℝ) :
    ℂ :=
  Complex.endpointSemicircleNormalizedIntegral a b
    (Complex.endpointSemicircleFullIntegrand w n ρ)

/-- Normalized endpoint principal-part integral. -/
abbrev Complex.endpointSemicirclePrincipalIntegral
    (w : ℂ)
    (n : ℕ)
    (a b ρ : ℝ) :
    ℂ :=
  Complex.endpointSemicircleNormalizedIntegral a b
    (Complex.endpointSemicirclePrincipalIntegrand w n ρ)

/-- Normalized endpoint removable-remainder integral. -/
abbrev Complex.endpointSemicircleRemainderIntegral
    (w : ℂ)
    (n : ℕ)
    (a b ρ : ℝ) :
    ℂ :=
  Complex.endpointSemicircleNormalizedIntegral a b
    (Complex.endpointSemicircleRemainderIntegrand w n ρ)

/-- Endpoint arc decomposition into the principal simple-pole part plus the
removable regular remainder after integrating over the arc. -/
theorem Complex.finiteAbelPlana_log_endpointSemicircleIntegral_linearized
    (w : ℂ)
    (n : ℕ)
    (a b ρ : ℝ)
    (hρ : ρ ≠ 0)
    (hprincipal :
      IntervalIntegrable
        (Complex.endpointSemicirclePrincipalIntegrand w n ρ)
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) a b)
    (hremainder :
      IntervalIntegrable
        (Complex.endpointSemicircleRemainderIntegrand w n ρ)
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) a b) :
    Complex.endpointSemicircleFullIntegral w n a b ρ =
      HAdd.hAdd
        (Complex.endpointSemicirclePrincipalIntegral w n a b ρ)
        (Complex.endpointSemicircleRemainderIntegral w n a b ρ) := by
  have hintegral_eq :
      ∫ θ : ℝ in a..b, Complex.endpointSemicircleFullIntegrand w n ρ θ =
        ∫ θ : ℝ in a..b,
          Complex.endpointSemicirclePrincipalIntegrand w n ρ θ +
            Complex.endpointSemicircleRemainderIntegrand w n ρ θ :=
    intervalIntegral.integral_congr
      (fun θ _hθ =>
        Complex.finiteAbelPlana_log_endpointSemicircle_integrand_eq_principal_add_remainder
          w n ρ hρ θ)
  have hintegral_add :
      ∫ θ : ℝ in a..b,
          Complex.endpointSemicirclePrincipalIntegrand w n ρ θ +
            Complex.endpointSemicircleRemainderIntegrand w n ρ θ =
        (∫ θ : ℝ in a..b,
          Complex.endpointSemicirclePrincipalIntegrand w n ρ θ) +
        (∫ θ : ℝ in a..b,
          Complex.endpointSemicircleRemainderIntegrand w n ρ θ) :=
    intervalIntegral.integral_add
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      hprincipal hremainder
  have hnormalize :
      Complex.endpointSemicircleNormalizedIntegral a b
          (Complex.endpointSemicircleFullIntegrand w n ρ) =
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          ((∫ θ : ℝ in a..b,
            Complex.endpointSemicirclePrincipalIntegrand w n ρ θ) +
          (∫ θ : ℝ in a..b,
            Complex.endpointSemicircleRemainderIntegrand w n ρ θ)) :=
    Eq.trans
      (congrArg
        (fun z : ℂ => ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ * z)
        hintegral_eq)
      (congrArg
        (fun z : ℂ => ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ * z)
        hintegral_add)
  have hsplit :
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          ((∫ θ : ℝ in a..b,
            Complex.endpointSemicirclePrincipalIntegrand w n ρ θ) +
          (∫ θ : ℝ in a..b,
            Complex.endpointSemicircleRemainderIntegrand w n ρ θ)) =
        HAdd.hAdd
          (Complex.endpointSemicirclePrincipalIntegral w n a b ρ)
          (Complex.endpointSemicircleRemainderIntegral w n a b ρ) :=
    mul_add
      (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹)
      (∫ θ : ℝ in a..b,
        Complex.endpointSemicirclePrincipalIntegrand w n ρ θ)
      (∫ θ : ℝ in a..b,
        Complex.endpointSemicircleRemainderIntegrand w n ρ θ)
  exact Eq.trans hnormalize hsplit

/-- Endpoint arc decomposition into the principal simple-pole part plus the
removable regular remainder after integrating over the arc. -/
theorem Complex.intervalIntegrable_endpointSemicirclePrincipalPart
    (w : ℂ)
    (n : ℕ)
    (a b ρ : ℝ)
    (hρ : ρ ≠ 0) :
    IntervalIntegrable
      (fun θ : ℝ =>
          ((Complex.finiteAbelPlanaLogIntegerResidue w n) /
              ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) a b := by
  exact
    intervalIntegrable_const.congr
      (Filter.Eventually.of_forall
        (fun θ =>
          (Complex.finiteAbelPlana_log_endpointSemicirclePrincipalPart_integrand_eq_const
            (w := w) n hρ θ).symm))

/-- The removable endpoint-arc remainder integrand is interval-integrable for
each nonzero radius. -/
theorem Complex.continuous_endpointSemicircleArc
    (n : ℕ)
    (ρ : ℝ) :
    Continuous
      (fun θ : ℝ =>
        (n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
  exact
    continuous_const.add
      (continuous_const.mul
        (Complex.continuous_exp.comp
          (continuous_const.mul Complex.continuous_ofReal)))

/-- The nonzero-radius endpoint arc vector never vanishes. -/
theorem Complex.endpointSemicircleArcVector_ne_zero
    {ρ : ℝ}
    (hρ : ρ ≠ 0)
    (θ : ℝ) :
    (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) ≠ 0 := by
  have hρc : (ρ : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr hρ
  exact mul_ne_zero hρc (Complex.exp_ne_zero _)

/-- A sufficiently small positive endpoint arc stays inside the residue
isolation ball around its center. -/
theorem Complex.endpointSemicircleArc_mem_integerResidueIsolationBall
    {w : ℂ}
    (n : ℕ)
    {ρ : ℝ}
    (hρpos : 0 < ρ)
    (hρR : ρ <
      Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (θ : ℝ) :
    (n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) ∈
      Metric.ball (n : ℂ)
        (Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n) := by
  have hdist :
      dist ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) (n : ℂ) =
        ρ := by
    calc
      dist ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) (n : ℂ) =
          ‖((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - (n : ℂ)‖ := by
        exact dist_eq_norm _ _
      _ = ‖(ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))‖ := by
        exact congrArg norm
          (add_sub_cancel_left (n : ℂ)
            ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
      _ = |ρ| := Complex.norm_endpointSemicircleArcVector ρ θ
      _ = ρ := abs_of_pos hρpos
  exact Metric.mem_ball.mpr (hdist.symm ▸ hρR)

/-- The removable numerator extension is continuous along a nonzero endpoint
arc. -/
theorem Complex.continuousOn_endpointSemicircleResidueExtension_comp_arc
    {w : ℂ}
    (hw : 0 < w.re)
    (n : ℕ)
    [∀ z : ℂ, Decidable (z = (n : ℂ))]
    (a b ρ : ℝ)
    (hρpos : 0 < ρ)
    (hρR : ρ <
      Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n) :
    ContinuousOn
      (fun θ : ℝ =>
        Complex.finiteAbelPlanaLogIntegerResidueExtension w n
          ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
      (Set.uIcc a b) := by
  let arc : ℝ → ℂ :=
    fun θ : ℝ =>
      (n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
  have harc_continuous : Continuous arc :=
    Complex.continuous_endpointSemicircleArc n ρ
  have hresidue_continuous :
      ContinuousOn
        (fun z : ℂ =>
          Complex.finiteAbelPlanaLogIntegerResidueExtension w n z)
        (Metric.ball (n : ℂ)
          (Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)) :=
    (Complex.differentiableOn_finiteAbelPlanaLogIntegerResidueExtension_isolationBall
      hw n).continuousOn
  have harc_maps :
      ∀ θ ∈ Set.uIcc a b,
        arc θ ∈ Metric.ball (n : ℂ)
          (Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n) := by
    exact fun θ _hθ =>
      Complex.endpointSemicircleArc_mem_integerResidueIsolationBall
        n hρpos hρR θ
  exact hresidue_continuous.comp harc_continuous.continuousOn harc_maps

/-- The removable endpoint-arc remainder integrand is continuous on the angle
interval. -/
theorem Complex.continuousOn_endpointSemicircleRemainderIntegrand
    {w : ℂ}
    (hw : 0 < w.re)
    (n : ℕ)
    [∀ z : ℂ, Decidable (z = (n : ℂ))]
    (a b ρ : ℝ)
    (hρpos : 0 < ρ)
    (hρR : ρ <
      Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n) :
    ContinuousOn
      (fun θ : ℝ =>
        ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
              ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
            Complex.finiteAbelPlanaLogIntegerResidue w n) /
            ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
      (Set.uIcc a b) := by
  have hnum :
      ContinuousOn
        (fun θ : ℝ =>
          Complex.finiteAbelPlanaLogIntegerResidueExtension w n
            ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
          Complex.finiteAbelPlanaLogIntegerResidue w n)
        (Set.uIcc a b) :=
    (Complex.continuousOn_endpointSemicircleResidueExtension_comp_arc
      hw n a b ρ hρpos hρR).sub continuousOn_const
  have hden :
      ContinuousOn
        (fun θ : ℝ =>
          (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
        (Set.uIcc a b) := by
    exact
      (continuous_const.mul
        (Complex.continuous_exp.comp
          (continuous_const.mul Complex.continuous_ofReal))).continuousOn
  have hquot :
      ContinuousOn
        (fun θ : ℝ =>
          (Complex.finiteAbelPlanaLogIntegerResidueExtension w n
              ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
            Complex.finiteAbelPlanaLogIntegerResidue w n) /
            ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        (Set.uIcc a b) :=
    have hρne : ρ ≠ 0 := ne_of_gt hρpos
    hnum.div hden (fun θ _hθ =>
      Complex.endpointSemicircleArcVector_ne_zero hρne θ)
  have hdz :
      ContinuousOn
        (fun θ : ℝ =>
          Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
        (Set.uIcc a b) := by
    exact
      ((continuous_const.mul continuous_const).mul
        (Complex.continuous_exp.comp
          (continuous_const.mul Complex.continuous_ofReal))).continuousOn
  exact hquot.mul hdz

/-- The removable endpoint-arc remainder integrand is interval-integrable for
each nonzero radius. -/
theorem Complex.intervalIntegrable_endpointSemicircleRemainder
    {w : ℂ}
    (hw : 0 < w.re)
    (n : ℕ)
    [∀ z : ℂ, Decidable (z = (n : ℂ))]
    (a b ρ : ℝ)
    (hρpos : 0 < ρ)
    (hρR : ρ <
      Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n) :
    IntervalIntegrable
      (fun θ : ℝ =>
        ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
              ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
            Complex.finiteAbelPlanaLogIntegerResidue w n) /
          ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
        (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) a b := by
  exact
    (Complex.continuousOn_endpointSemicircleRemainderIntegrand
      hw n a b ρ hρpos hρR).intervalIntegrable

/-- Endpoint arc decomposition into the principal simple-pole part plus the
removable regular remainder after integrating over the arc. -/
theorem Complex.finiteAbelPlana_log_endpointSemicircleIntegral_eq_principal_add_remainder
    {w : ℂ}
    (hw : 0 < w.re)
    (n : ℕ)
    (a b ρ : ℝ)
    (hρpos : 0 < ρ)
    (hρR : ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n) :
    Complex.endpointSemicircleFullIntegral w n a b ρ =
      HAdd.hAdd
        (Complex.endpointSemicirclePrincipalIntegral w n a b ρ)
        (Complex.endpointSemicircleRemainderIntegral w n a b ρ) := by
  -- Pointwise Laurent decomposition, followed by linearity of the interval
  -- integral and multiplication by the normalization constant.
  exact
    Complex.finiteAbelPlana_log_endpointSemicircleIntegral_linearized
      w n a b ρ (ne_of_gt hρpos)
      (Complex.intervalIntegrable_endpointSemicirclePrincipalPart
        w n a b ρ (ne_of_gt hρpos))
      (Complex.intervalIntegrable_endpointSemicircleRemainder
        hw n a b ρ hρpos hρR)

/-- The named normalized endpoint principal-part integral tends to the half
residue. -/
theorem Complex.endpointSemicirclePrincipalIntegral_tendsto_halfResidue
    {w : ℂ}
    (n : ℕ)
    (a b : ℝ)
    (hangle : b - a = Real.pi) :
    Filter.Tendsto
      (fun ρ : ℝ =>
        Complex.endpointSemicirclePrincipalIntegral w n a b ρ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.finiteAbelPlanaLogIntegerResidue w n / 2)) :=
  Complex.finiteAbelPlana_log_endpointSemicirclePrincipalPart_tendsto_halfResidue
    n a b hangle

/-- The named normalized endpoint remainder integral tends to zero. -/
theorem Complex.endpointSemicircleRemainderIntegral_tendsto_zero
    {w : ℂ}
    (hw : 0 < w.re)
    (n : ℕ)
    (a b : ℝ) :
    Filter.Tendsto
      (fun ρ : ℝ =>
        Complex.endpointSemicircleRemainderIntegral w n a b ρ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (0 : ℂ)) :=
  Complex.finiteAbelPlana_log_endpointSemicircleRemainder_tendsto_zero
    hw n a b

/-- Local half-arc residue theorem for an integer cotangent pole.

The removable numerator is already owned by
`finiteAbelPlanaLogIntegerResidueExtension`; this theorem is the endpoint
version of the existing full-circle residue theorem.  The interval endpoints
are required to differ by `π`, so the principal part contributes exactly half
of the normalized residue. -/
theorem Complex.finiteAbelPlana_log_endpointSemicircleIndentation_tendsto_halfResidue
    {w : ℂ}
    (hw : 0 < w.re)
    (n : ℕ)
    (a b : ℝ)
    (hangle : b - a = Real.pi) :
    Filter.Tendsto
      (fun ρ : ℝ =>
        Complex.endpointSemicircleFullIntegral w n a b ρ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.finiteAbelPlanaLogIntegerResidue w n / 2)) := by
  have hprincipal :
      Filter.Tendsto
        (fun ρ : ℝ =>
          Complex.endpointSemicirclePrincipalIntegral w n a b ρ)
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.finiteAbelPlanaLogIntegerResidue w n / 2)) :=
    Complex.endpointSemicirclePrincipalIntegral_tendsto_halfResidue
      n a b hangle
  have hremainder :
      Filter.Tendsto
        (fun ρ : ℝ =>
          Complex.endpointSemicircleRemainderIntegral w n a b ρ)
        (𝓝[>] (0 : ℝ))
        (𝓝 (0 : ℂ)) :=
    Complex.endpointSemicircleRemainderIntegral_tendsto_zero
      hw n a b
  have hsum := hprincipal.add hremainder
  have hpoint :
      (fun ρ : ℝ =>
        Complex.endpointSemicircleFullIntegral w n a b ρ) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ρ : ℝ =>
        HAdd.hAdd
          (Complex.endpointSemicirclePrincipalIntegral w n a b ρ)
          (Complex.endpointSemicircleRemainderIntegral w n a b ρ)) := by
    exact
      Filter.mem_of_superset
        (Complex.eventually_pos_lt_finiteAbelPlanaLogIntegerResidueIsolationRadius
          hw n)
        (fun ρ hρ =>
          Complex.finiteAbelPlana_log_endpointSemicircleIntegral_eq_principal_add_remainder
            hw n a b ρ hρ.1 hρ.2)
  have htarget :
      Complex.finiteAbelPlanaLogIntegerResidue w n / 2 + 0 =
        Complex.finiteAbelPlanaLogIntegerResidue w n / 2 := by
    exact add_zero _
  exact (htarget ▸ hsum).congr' hpoint.symm

/-- The left endpoint indentation is the named endpoint full integral centered
at `0`. -/
theorem Complex.finiteAbelPlanaLogLeftEndpointIndentationIntegral_eq_endpointFullIntegral
    (w : ℂ)
    (ρ : ℝ) :
    Complex.finiteAbelPlanaLogLeftEndpointIndentationIntegral w ρ =
      Complex.endpointSemicircleFullIntegral
        w 0 (-(Real.pi / 2)) (Real.pi / 2) ρ := by
  exact
    congrArg
      (fun z : ℂ => ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ * z)
      (intervalIntegral.integral_congr
        (fun θ _hθ =>
          congrArg
            (fun z : ℂ =>
              Complex.finiteAbelPlanaLogRectangleIntegrand w z *
                (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
            (show
              (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) =
                ((0 : ℕ) : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) from
              Eq.trans
                (zero_add ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))).symm
                (congrArg
                  (fun z : ℂ =>
                    z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
                  (Nat.cast_zero (R := ℂ)).symm))))

/-- The right endpoint indentation is the named endpoint full integral centered
at `N + 1`. -/
theorem Complex.finiteAbelPlanaLogRightEndpointIndentationIntegral_eq_endpointFullIntegral
    (N : ℕ)
    (w : ℂ)
    (ρ : ℝ) :
    Complex.finiteAbelPlanaLogRightEndpointIndentationIntegral N w ρ =
      Complex.endpointSemicircleFullIntegral
        w (N + 1) (Real.pi / 2) (3 * Real.pi / 2) ρ :=
  rfl

/-- The left endpoint indentation tends to half the local residue at `0`. -/
theorem Complex.finiteAbelPlana_log_leftEndpointIndentationIntegral_tendsto_halfResidue
    {w : ℂ}
    (hw : 0 < w.re) :
    Filter.Tendsto
      (fun ρ : ℝ =>
        Complex.finiteAbelPlanaLogLeftEndpointIndentationIntegral w ρ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.finiteAbelPlanaLogIntegerResidue w 0 / 2)) := by
  have hsemicircle :
      Filter.Tendsto
        (fun ρ : ℝ =>
          Complex.endpointSemicircleFullIntegral
            w 0 (-(Real.pi / 2)) (Real.pi / 2) ρ)
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.finiteAbelPlanaLogIntegerResidue w 0 / 2)) :=
    Complex.finiteAbelPlana_log_endpointSemicircleIndentation_tendsto_halfResidue
      hw 0 (-(Real.pi / 2)) (Real.pi / 2)
      Real.leftEndpointSemicircle_angleLength
  have hevent :
      (fun ρ : ℝ =>
        Complex.endpointSemicircleFullIntegral
          w 0 (-(Real.pi / 2)) (Real.pi / 2) ρ) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ρ : ℝ =>
        Complex.finiteAbelPlanaLogLeftEndpointIndentationIntegral w ρ) :=
    Filter.Eventually.of_forall
      (fun ρ =>
        (Complex.finiteAbelPlanaLogLeftEndpointIndentationIntegral_eq_endpointFullIntegral
          w ρ).symm)
  exact hsemicircle.congr' hevent

/-- The right endpoint indentation tends to half the local residue at `N + 1`. -/
theorem Complex.finiteAbelPlana_log_rightEndpointIndentationIntegral_tendsto_halfResidue
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    Filter.Tendsto
      (fun ρ : ℝ =>
        Complex.finiteAbelPlanaLogRightEndpointIndentationIntegral N w ρ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.finiteAbelPlanaLogIntegerResidue w (N + 1) / 2)) := by
  have hsemicircle :
      Filter.Tendsto
        (fun ρ : ℝ =>
          Complex.endpointSemicircleFullIntegral
            w (N + 1) (Real.pi / 2) (3 * Real.pi / 2) ρ)
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.finiteAbelPlanaLogIntegerResidue w (N + 1) / 2)) :=
    Complex.finiteAbelPlana_log_endpointSemicircleIndentation_tendsto_halfResidue
      hw (N + 1) (Real.pi / 2) (3 * Real.pi / 2)
      Real.rightEndpointSemicircle_angleLength
  have hevent :
      (fun ρ : ℝ =>
        Complex.endpointSemicircleFullIntegral
          w (N + 1) (Real.pi / 2) (3 * Real.pi / 2) ρ) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ρ : ℝ =>
        Complex.finiteAbelPlanaLogRightEndpointIndentationIntegral N w ρ) :=
    Filter.Eventually.of_forall
      (fun ρ =>
        (Complex.finiteAbelPlanaLogRightEndpointIndentationIntegral_eq_endpointFullIntegral
          N w ρ).symm)
  exact hsemicircle.congr' hevent

/-- Unfolding of the finite-radius deleted-boundary contribution. -/
theorem Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution_unfold
    (N : ℕ)
    (w : ℂ)
    (ρ : ℝ) :
    Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ =
      Complex.finiteAbelPlanaLogLeftEndpointIndentationIntegral w ρ +
        Complex.finiteAbelPlanaLogRightEndpointIndentationIntegral N w ρ +
          ∑ n in Finset.range N,
            Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral
              w ((n + 1 : ℕ) : ℂ) ρ :=
  rfl

/-- The two endpoint indentations converge to the half-weighted endpoint
residue contribution. -/
theorem Complex.finiteAbelPlana_log_endpointIndentationIntegral_tendsto_endpointResidues
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    Filter.Tendsto
      (fun ρ : ℝ =>
        Complex.finiteAbelPlanaLogLeftEndpointIndentationIntegral w ρ +
          Complex.finiteAbelPlanaLogRightEndpointIndentationIntegral N w ρ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w)) := by
  have hleft :
      Filter.Tendsto
        (fun ρ : ℝ =>
          Complex.finiteAbelPlanaLogLeftEndpointIndentationIntegral w ρ)
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.finiteAbelPlanaLogIntegerResidue w 0 / 2)) :=
    Complex.finiteAbelPlana_log_leftEndpointIndentationIntegral_tendsto_halfResidue
      hw
  have hright :
      Filter.Tendsto
        (fun ρ : ℝ =>
          Complex.finiteAbelPlanaLogRightEndpointIndentationIntegral N w ρ)
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.finiteAbelPlanaLogIntegerResidue w (N + 1) / 2)) :=
    Complex.finiteAbelPlana_log_rightEndpointIndentationIntegral_tendsto_halfResidue
      hw N
  have hsum :
      Filter.Tendsto
        (fun ρ : ℝ =>
          Complex.finiteAbelPlanaLogLeftEndpointIndentationIntegral w ρ +
            Complex.finiteAbelPlanaLogRightEndpointIndentationIntegral N w ρ)
        (𝓝[>] (0 : ℝ))
        (𝓝
          (Complex.finiteAbelPlanaLogIntegerResidue w 0 / 2 +
            Complex.finiteAbelPlanaLogIntegerResidue w (N + 1) / 2)) :=
    hleft.add hright
  have htarget :
      Complex.finiteAbelPlanaLogIntegerResidue w 0 / 2 +
          Complex.finiteAbelPlanaLogIntegerResidue w (N + 1) / 2 =
        Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w := by
    calc
      Complex.finiteAbelPlanaLogIntegerResidue w 0 / 2 +
          Complex.finiteAbelPlanaLogIntegerResidue w (N + 1) / 2 =
        (Complex.finiteAbelPlanaLogIntegerResidue w 0 +
          Complex.finiteAbelPlanaLogIntegerResidue w (N + 1)) / 2 :=
        (add_div
          (Complex.finiteAbelPlanaLogIntegerResidue w 0)
          (Complex.finiteAbelPlanaLogIntegerResidue w (N + 1))
          (2 : ℂ)).symm
      _ = Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w :=
        (Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution_unfold N w).symm
  exact htarget ▸ hsum

/-- The finite-radius deleted-boundary contribution converges to the
principal-value residue contribution. -/
theorem Complex.finiteAbelPlana_log_pvDeletedBoundaryIntegralContribution_tendsto_pvResidues
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (hdecInteriorPole : ∀ n : ℕ, n ∈ Finset.range N →
      ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ))) :
    Filter.Tendsto
      (fun ρ : ℝ =>
        Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w)) := by
  have hendpoints :
      Filter.Tendsto
        (fun ρ : ℝ =>
          Complex.finiteAbelPlanaLogLeftEndpointIndentationIntegral w ρ +
            Complex.finiteAbelPlanaLogRightEndpointIndentationIntegral N w ρ)
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w)) :=
    Complex.finiteAbelPlana_log_endpointIndentationIntegral_tendsto_endpointResidues
      hw N
  have hinterior :
      Filter.Tendsto
        (fun ρ : ℝ =>
          ∑ n in Finset.range N,
            Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral
              w ((n + 1 : ℕ) : ℂ) ρ)
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.finiteAbelPlanaLogInteriorIntegerResidueContribution N w)) :=
    Complex.finiteAbelPlana_log_pvInteriorSmallCircleIntegral_tendsto_residues
      hw N hdecInteriorPole
  have htotal :
      Filter.Tendsto
        (fun ρ : ℝ =>
          (Complex.finiteAbelPlanaLogLeftEndpointIndentationIntegral w ρ +
            Complex.finiteAbelPlanaLogRightEndpointIndentationIntegral N w ρ) +
            ∑ n in Finset.range N,
              Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral
                w ((n + 1 : ℕ) : ℂ) ρ)
        (𝓝[>] (0 : ℝ))
        (𝓝
          (Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w +
            Complex.finiteAbelPlanaLogInteriorIntegerResidueContribution N w)) :=
    hendpoints.add hinterior
  have htarget :
      Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w =
        Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w +
          Complex.finiteAbelPlanaLogInteriorIntegerResidueContribution N w :=
    Complex.finiteAbelPlana_log_pvIntegerResidueContribution_unfold N w
  have htotal_target :
      Filter.Tendsto
        (fun ρ : ℝ =>
          Complex.finiteAbelPlanaLogLeftEndpointIndentationIntegral w ρ +
            Complex.finiteAbelPlanaLogRightEndpointIndentationIntegral N w ρ +
              ∑ n in Finset.range N,
                Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral
                  w ((n + 1 : ℕ) : ℂ) ρ)
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w)) :=
    htarget.symm ▸ htotal
  have hsource_event :
      (fun ρ : ℝ =>
        Complex.finiteAbelPlanaLogLeftEndpointIndentationIntegral w ρ +
          Complex.finiteAbelPlanaLogRightEndpointIndentationIntegral N w ρ +
            ∑ n in Finset.range N,
              Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral
                w ((n + 1 : ℕ) : ℂ) ρ) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ρ : ℝ =>
        Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ) :=
    Filter.Eventually.of_forall
      (fun ρ =>
        (Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution_unfold
          N w ρ).symm)
  exact
    htotal_target.congr' hsource_event

end

end LFunctions
end Boundary
