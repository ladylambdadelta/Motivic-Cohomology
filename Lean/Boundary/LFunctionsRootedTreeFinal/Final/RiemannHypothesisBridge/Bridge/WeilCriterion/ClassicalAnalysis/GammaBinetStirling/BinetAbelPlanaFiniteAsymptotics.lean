import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaFiniteFormula
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaUpperResidual
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Finite asymptotic owners for the Abel-Plana proof of Binet's formula

This file owns the two standard analytic estimates behind the finite
Abel-Plana limit passage:

* the endpoint logarithmic Stirling remainder tends to zero;
* the finite Abel-Plana contour remainder has norm tending to zero.

The downstream classical-input file should only assemble these estimates with
the concrete finite terms from `BinetAbelPlanaCore`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Algebraic normalization of the real factorial endpoint error. -/
theorem Real.factorialStirlingEndpoint_algebra_normalization
    (A M L L₂ Lπ : ℝ) :
    A - (((M + (1 / 2 : ℝ)) * L - M + (L₂ + Lπ) / 2)) =
      (A - (1 / 2 : ℝ) * (L₂ + L) - M * (L - 1)) - Lπ / 2 := by
  calc
    A - (((M + (1 / 2 : ℝ)) * L - M + (L₂ + Lπ) / 2)) =
        A - ((M * L + (1 / 2 : ℝ) * L - M) +
          (L₂ / 2 + Lπ / 2)) := by
      exact congrArg (fun x : ℝ => A - x) <| by
        calc
          (M + (1 / 2 : ℝ)) * L - M + (L₂ + Lπ) / 2 =
              (M * L + (1 / 2 : ℝ) * L) - M + (L₂ + Lπ) / 2 := by
            exact congrArg (fun x : ℝ => x - M + (L₂ + Lπ) / 2)
              (add_mul M (1 / 2 : ℝ) L)
          _ = (M * L + (1 / 2 : ℝ) * L - M) + (L₂ + Lπ) / 2 := rfl
          _ = (M * L + (1 / 2 : ℝ) * L - M) + (L₂ / 2 + Lπ / 2) := by
            exact congrArg (fun x : ℝ => (M * L + (1 / 2 : ℝ) * L - M) + x)
              (add_div L₂ Lπ 2)
    _ = A + -((M * L + (1 / 2 : ℝ) * L - M) +
          (L₂ / 2 + Lπ / 2)) := sub_eq_add_neg A _
    _ = A + (-(M * L + (1 / 2 : ℝ) * L - M) +
          -(L₂ / 2 + Lπ / 2)) := by
      exact congrArg (fun x : ℝ => A + x)
        (neg_add (M * L + (1 / 2 : ℝ) * L - M) (L₂ / 2 + Lπ / 2))
    _ = A + (-(M * L + (1 / 2 : ℝ) * L - M) +
          (-(L₂ / 2) + -(Lπ / 2))) := by
      exact congrArg
        (fun x : ℝ => A + (-(M * L + (1 / 2 : ℝ) * L - M) + x))
        (neg_add (L₂ / 2) (Lπ / 2))
    _ = (A - (1 / 2 : ℝ) * (L₂ + L) - M * (L - 1)) - Lπ / 2 := by
      have hhalf :
          (1 / 2 : ℝ) * (L₂ + L) =
            L₂ / 2 + (1 / 2 : ℝ) * L := by
        calc
          (1 / 2 : ℝ) * (L₂ + L) =
              (1 / 2 : ℝ) * L₂ + (1 / 2 : ℝ) * L :=
            mul_add (1 / 2 : ℝ) L₂ L
          _ = L₂ / 2 + (1 / 2 : ℝ) * L := by
            exact congrArg (fun x : ℝ => x + (1 / 2 : ℝ) * L)
              (div_eq_mul_inv L₂ 2).symm
      have hM :
          M * (L - 1) = M * L - M := by
        calc
          M * (L - 1) = M * L - M * 1 := mul_sub M L 1
          _ = M * L - M := by
            exact congrArg (fun x : ℝ => M * L - x) (mul_one M)
      calc
        A + (-(M * L + (1 / 2 : ℝ) * L - M) +
            (-(L₂ / 2) + -(Lπ / 2))) =
            (A - (L₂ / 2 + (1 / 2 : ℝ) * L) - (M * L - M)) -
              Lπ / 2 := by
          ac_rfl
        _ = (A - (1 / 2 : ℝ) * (L₂ + L) - (M * L - M)) -
              Lπ / 2 := by
          exact congrArg
            (fun x : ℝ => (A - x - (M * L - M)) - Lπ / 2)
            hhalf.symm
        _ = (A - (1 / 2 : ℝ) * (L₂ + L) - M * (L - 1)) -
              Lπ / 2 := by
          exact congrArg
            (fun x : ℝ => (A - (1 / 2 : ℝ) * (L₂ + L) - x) - Lπ / 2)
            hM.symm

/-- Coercion of the logarithm of a nonnegative real into the principal complex
logarithm. -/
theorem Complex.ofReal_log_nonneg_eq_complex_log
    {x : ℝ}
    (hx : 0 ≤ x) :
    ((Real.log x : ℝ) : ℂ) = Complex.log (x : ℂ) := by
  exact (Complex.ofReal_log hx).symm

/-- Coercion preserves the algebraic shape of the factorial Stirling endpoint
error. -/
theorem Complex.ofReal_factorialStirlingEndpoint_algebra
    (A M L L₂π : ℝ) :
    ((A - (((M + (1 / 2 : ℝ)) * L - M + L₂π / 2)) : ℝ) : ℂ) =
      (A : ℂ) -
        (((M : ℂ) + (1 / 2 : ℂ)) * (L : ℂ) -
          (M : ℂ) + (L₂π : ℂ) / 2) := by
  exact
    map_sub (Complex.ofRealRingHom)
      A
      (((M + (1 / 2 : ℝ)) * L - M + L₂π / 2))

/-- Subtracting an appended term from the original term gives the negative
appended term. -/
theorem Complex.sub_add_cancel_to_neg
    (a b : ℂ) :
    a - (a + b) = -b := by
  calc
    a - (a + b) = a + -(a + b) := sub_eq_add_neg a (a + b)
    _ = a + (-a + -b) := by
      exact congrArg (fun x : ℂ => a + x) (neg_add a b)
    _ = (a + -a) + -b := (add_assoc a (-a) (-b)).symm
    _ = 0 + -b := by
      exact congrArg (fun x : ℂ => x + -b) (add_neg_cancel a)
    _ = -b := zero_add (-b)

/-- Multiplying the endpoint affine factor by the endpoint scale leaves the
linear term after the quadratic part is removed. -/
theorem Complex.binetEndpoint_affine_mul_small_sub_quadratic_div
    {w : ℂ}
    {M : ℕ}
    (hM : M ≠ 0) :
    ((w + (M : ℂ) + (1 / 2 : ℂ)) * (w / (M : ℂ))) -
        ((w * (w + (1 / 2 : ℂ))) / (M : ℂ)) =
      w := by
  have hM_ne : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM
  have hquad :
      (w + (1 / 2 : ℂ)) * (w / (M : ℂ)) =
        (w * (w + (1 / 2 : ℂ))) / (M : ℂ) := by
    calc
      (w + (1 / 2 : ℂ)) * (w / (M : ℂ)) =
          (w + (1 / 2 : ℂ)) * (w * (M : ℂ)⁻¹) :=
        congrArg (fun x : ℂ => (w + (1 / 2 : ℂ)) * x)
          (div_eq_mul_inv w (M : ℂ))
      _ = ((w + (1 / 2 : ℂ)) * w) * (M : ℂ)⁻¹ :=
        mul_assoc (w + (1 / 2 : ℂ)) w (M : ℂ)⁻¹
      _ = (w * (w + (1 / 2 : ℂ))) * (M : ℂ)⁻¹ := by
        exact congrArg (fun x : ℂ => x * (M : ℂ)⁻¹)
          (mul_comm (w + (1 / 2 : ℂ)) w)
      _ = (w * (w + (1 / 2 : ℂ))) / (M : ℂ) :=
        (div_eq_mul_inv (w * (w + (1 / 2 : ℂ))) (M : ℂ)).symm
  have hlin :
      (M : ℂ) * (w / (M : ℂ)) = w := by
    calc
      (M : ℂ) * (w / (M : ℂ)) =
          (M : ℂ) * (w * (M : ℂ)⁻¹) :=
        congrArg (fun x : ℂ => (M : ℂ) * x)
          (div_eq_mul_inv w (M : ℂ))
      _ = (M : ℂ) * ((M : ℂ)⁻¹ * w) := by
        exact congrArg (fun x : ℂ => (M : ℂ) * x)
          (mul_comm w (M : ℂ)⁻¹)
      _ = ((M : ℂ) * (M : ℂ)⁻¹) * w :=
        (mul_assoc (M : ℂ) (M : ℂ)⁻¹ w).symm
      _ = 1 * w := by
        exact congrArg (fun x : ℂ => x * w) (mul_inv_cancel₀ hM_ne)
      _ = w := one_mul w
  have haff :
      w + (M : ℂ) + (1 / 2 : ℂ) = (w + (1 / 2 : ℂ)) + (M : ℂ) := by
    calc
      w + (M : ℂ) + (1 / 2 : ℂ) =
          (w + (M : ℂ)) + (1 / 2 : ℂ) := rfl
      _ = w + ((M : ℂ) + (1 / 2 : ℂ)) :=
        add_assoc w (M : ℂ) (1 / 2 : ℂ)
      _ = w + ((1 / 2 : ℂ) + (M : ℂ)) := by
        exact congrArg (fun x : ℂ => w + x)
          (add_comm (M : ℂ) (1 / 2 : ℂ))
      _ = (w + (1 / 2 : ℂ)) + (M : ℂ) :=
        (add_assoc w (1 / 2 : ℂ) (M : ℂ)).symm
  calc
    ((w + (M : ℂ) + (1 / 2 : ℂ)) * (w / (M : ℂ))) -
        ((w * (w + (1 / 2 : ℂ))) / (M : ℂ)) =
      (((w + (1 / 2 : ℂ)) + (M : ℂ)) * (w / (M : ℂ))) -
        ((w * (w + (1 / 2 : ℂ))) / (M : ℂ)) := by
        exact congrArg
          (fun x : ℂ =>
            x * (w / (M : ℂ)) -
              ((w * (w + (1 / 2 : ℂ))) / (M : ℂ)))
          haff
    _ =
      (((w + (1 / 2 : ℂ)) * (w / (M : ℂ))) +
          ((M : ℂ) * (w / (M : ℂ)))) -
        ((w * (w + (1 / 2 : ℂ))) / (M : ℂ)) := by
        exact congrArg
          (fun x : ℂ =>
            x - ((w * (w + (1 / 2 : ℂ))) / (M : ℂ)))
          (add_mul (w + (1 / 2 : ℂ)) (M : ℂ) (w / (M : ℂ)))
    _ =
      (((w * (w + (1 / 2 : ℂ))) / (M : ℂ)) + w) -
        ((w * (w + (1 / 2 : ℂ))) / (M : ℂ)) := by
        exact congrArg₂ HSub.hSub (congrArg₂ HAdd.hAdd hquad hlin) rfl
    _ = w := add_sub_cancel_left w ((w * (w + (1 / 2 : ℂ))) / (M : ℂ))

/-- Endpoint Taylor algebra once the branch logarithm has been separated. -/
theorem Complex.binetEndpointLogShiftError_taylor_algebra
    {w L : ℂ}
    {M : ℕ}
    (hM : M ≠ 0) :
    ((w + (M : ℂ) + (1 / 2 : ℂ)) *
        (Complex.log (M : ℂ) - (Complex.log (M : ℂ) + L))) + w =
      -((w * (w + (1 / 2 : ℂ))) / (M : ℂ)) -
        (w + (M : ℂ) + (1 / 2 : ℂ)) * (L - w / (M : ℂ)) := by
  let A : ℂ := w + (M : ℂ) + (1 / 2 : ℂ)
  let Q : ℂ := (w * (w + (1 / 2 : ℂ))) / (M : ℂ)
  have hlogdiff :
      Complex.log (M : ℂ) - (Complex.log (M : ℂ) + L) = -L :=
    Complex.sub_add_cancel_to_neg (Complex.log (M : ℂ)) L
  have hendpoint : A * (w / (M : ℂ)) - Q = w := by
    exact Complex.binetEndpoint_affine_mul_small_sub_quadratic_div hM
  have hregroup :
      -(A * L) + (A * (w / (M : ℂ)) - Q) =
        -Q - A * (L - w / (M : ℂ)) := by
    calc
      -(A * L) + (A * (w / (M : ℂ)) - Q) =
          -(A * L) + (A * (w / (M : ℂ)) + -Q) := by
        exact congrArg (fun x : ℂ => -(A * L) + x)
          (sub_eq_add_neg (A * (w / (M : ℂ))) Q)
      _ = (-(A * L) + A * (w / (M : ℂ))) + -Q :=
        (add_assoc (-(A * L)) (A * (w / (M : ℂ))) (-Q)).symm
      _ = -Q + (-(A * L) + A * (w / (M : ℂ))) := by
        exact add_comm (-(A * L) + A * (w / (M : ℂ))) (-Q)
      _ = -Q + (-(A * L) + A * (w / (M : ℂ))) := rfl
      _ = -Q + -(A * (L - w / (M : ℂ))) := by
        exact congrArg (fun x : ℂ => -Q + x) <| by
          calc
            -(A * L) + A * (w / (M : ℂ)) =
                A * (w / (M : ℂ)) + -(A * L) :=
              add_comm (-(A * L)) (A * (w / (M : ℂ)))
            _ = A * (w / (M : ℂ)) - A * L :=
              (sub_eq_add_neg (A * (w / (M : ℂ))) (A * L)).symm
            _ = -(A * L - A * (w / (M : ℂ))) :=
              (neg_sub (A * L) (A * (w / (M : ℂ)))).symm
            _ = -(A * (L - w / (M : ℂ))) :=
              (congrArg Neg.neg
                (mul_sub A L (w / (M : ℂ)))).symm
      _ = -Q - A * (L - w / (M : ℂ)) :=
        (sub_eq_add_neg (-Q) (A * (L - w / (M : ℂ)))).symm
  calc
    A * (Complex.log (M : ℂ) - (Complex.log (M : ℂ) + L)) + w =
        A * (-L) + w := by
      exact congrArg (fun x : ℂ => A * x + w) hlogdiff
    _ = -(A * L) + w := by
      exact congrArg (fun x : ℂ => x + w) (mul_neg A L)
    _ = -(A * L) + (A * (w / (M : ℂ)) - Q) := by
      exact congrArg (fun x : ℂ => -(A * L) + x) hendpoint.symm
    _ = -Q - A * (L - w / (M : ℂ)) := hregroup

/-- The factorial part of the logarithmic Stirling endpoint error. -/
noncomputable def Complex.binetAbelPlanaFactorialStirlingError
    (M : ℕ) : ℂ :=
  Complex.log ((Nat.factorial M : ℕ) : ℂ) -
    (((M : ℂ) + (1 / 2 : ℂ)) * Complex.log (M : ℂ) -
      (M : ℂ) +
        (((Real.log (2 * Real.pi)) : ℝ) : ℂ) / 2)

/-- Real-valued factorial Stirling endpoint error before coercion to `ℂ`. -/
noncomputable def Real.binetAbelPlanaFactorialStirlingError
    (M : ℕ) : ℝ :=
  Real.log ((Nat.factorial M : ℕ) : ℝ) -
    (((M : ℝ) + (1 / 2 : ℝ)) * Real.log (M : ℝ) -
      (M : ℝ) +
        Real.log (2 * Real.pi) / 2)

/-- The real factorial Stirling endpoint error is the logarithm of mathlib's
Stirling sequence, normalized by its limiting value `√π`. -/
theorem Real.binetAbelPlanaFactorialStirlingError_eq_log_stirlingSeq_sub_log_sqrt_pi
    (M : ℕ)
    (hM : M ≠ 0) :
    Real.binetAbelPlanaFactorialStirlingError M =
      Real.log (Stirling.stirlingSeq M) - Real.log (Real.sqrt Real.pi) := by
  have hMpos_nat : 0 < M := Nat.pos_of_ne_zero hM
  have hMpos_real : 0 < (M : ℝ) := Nat.cast_pos.mpr hMpos_nat
  have htwoMpos : 0 < (2 : ℝ) * M := mul_pos two_pos hMpos_real
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hsqrt_pi_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hpi_pos
  have hlog_sqrt_pi :
      Real.log (Real.sqrt Real.pi) = Real.log Real.pi / 2 := by
    exact Real.log_sqrt hpi_pos.le
  have hlog_two_mul_M :
      Real.log ((2 : ℝ) * M) = Real.log (2 : ℝ) + Real.log (M : ℝ) := by
    exact Real.log_mul two_ne_zero hMpos_real.ne'
  have hlog_M_div_exp :
      Real.log ((M : ℝ) / Real.exp 1) = Real.log (M : ℝ) - 1 := by
    have hdiv : Real.log ((M : ℝ) / Real.exp 1) =
        Real.log (M : ℝ) - Real.log (Real.exp 1) :=
      Real.log_div hMpos_real.ne' (Real.exp_pos 1).ne'
    have hlog_exp : Real.log (Real.exp 1) = 1 := Real.log_exp 1
    calc
      Real.log ((M : ℝ) / Real.exp 1) =
          Real.log (M : ℝ) - Real.log (Real.exp 1) :=
        hdiv
      _ = Real.log (M : ℝ) - 1 := by
        exact congrArg (fun x : ℝ => Real.log (M : ℝ) - x) hlog_exp
  have hlog_two_pi :
      Real.log (2 * Real.pi) = Real.log (2 : ℝ) + Real.log Real.pi := by
    exact Real.log_mul two_ne_zero hpi_pos.ne'
  calc
    Real.binetAbelPlanaFactorialStirlingError M
        =
        Real.log ((Nat.factorial M : ℕ) : ℝ) -
          (((M : ℝ) + (1 / 2 : ℝ)) * Real.log (M : ℝ) -
            (M : ℝ) +
              Real.log (2 * Real.pi) / 2) := by
          rfl
    _ =
        (Real.log ((Nat.factorial M : ℕ) : ℝ) -
            (1 / 2 : ℝ) * Real.log ((2 : ℝ) * M) -
              (M : ℝ) * Real.log ((M : ℝ) / Real.exp 1)) -
          Real.log (Real.sqrt Real.pi) := by
          have h1 := hlog_sqrt_pi
          have h2 := hlog_two_mul_M
          have h3 := hlog_M_div_exp
          have h4 := hlog_two_pi
          have hlog_two_from_two_pi :
              Real.log (2 * Real.pi) - Real.log Real.pi =
                Real.log (2 : ℝ) := by
            calc
              Real.log (2 * Real.pi) - Real.log Real.pi =
                  (Real.log (2 : ℝ) + Real.log Real.pi) -
                    Real.log Real.pi := by
                exact congrArg (fun x : ℝ => x - Real.log Real.pi) h4
              _ = Real.log (2 : ℝ) := by
                ac_rfl
          calc
            Real.log ((Nat.factorial M : ℕ) : ℝ) -
                (((M : ℝ) + (1 / 2 : ℝ)) * Real.log (M : ℝ) -
                  (M : ℝ) +
                    Real.log (2 * Real.pi) / 2) =
                (Real.log ((Nat.factorial M : ℕ) : ℝ) -
                    (1 / 2 : ℝ) *
                      (Real.log (2 * Real.pi) - Real.log Real.pi +
                        Real.log (M : ℝ)) -
                      (M : ℝ) *
                        (Real.log (M : ℝ) - 1)) -
                  Real.log Real.pi / 2 := by
                exact
                  Real.factorialStirlingEndpoint_algebra_normalization
                    (Real.log ((Nat.factorial M : ℕ) : ℝ))
                    (M : ℝ)
                    (Real.log (M : ℝ))
                    (Real.log (2 * Real.pi) - Real.log Real.pi)
                    (Real.log Real.pi)
            _ =
                (Real.log ((Nat.factorial M : ℕ) : ℝ) -
                    (1 / 2 : ℝ) * Real.log ((2 : ℝ) * M) -
                      (M : ℝ) * Real.log ((M : ℝ) / Real.exp 1)) -
                  Real.log (Real.sqrt Real.pi) := by
                calc
                  (Real.log ((Nat.factorial M : ℕ) : ℝ) -
                      (1 / 2 : ℝ) *
                        (Real.log (2 * Real.pi) - Real.log Real.pi +
                          Real.log (M : ℝ)) -
                        (M : ℝ) *
                          (Real.log (M : ℝ) - 1)) -
                    Real.log Real.pi / 2 =
                      (Real.log ((Nat.factorial M : ℕ) : ℝ) -
                        (1 / 2 : ℝ) *
                          (Real.log (2 : ℝ) + Real.log (M : ℝ)) -
                          (M : ℝ) *
                            (Real.log (M : ℝ) - 1)) -
                      Real.log Real.pi / 2 := by
                    exact congrArg
                      (fun x : ℝ =>
                        (Real.log ((Nat.factorial M : ℕ) : ℝ) -
                          (1 / 2 : ℝ) * (x + Real.log (M : ℝ)) -
                            (M : ℝ) * (Real.log (M : ℝ) - 1)) -
                          Real.log Real.pi / 2)
                      hlog_two_from_two_pi
                  _ =
                      (Real.log ((Nat.factorial M : ℕ) : ℝ) -
                        (1 / 2 : ℝ) * Real.log ((2 : ℝ) * M) -
                          (M : ℝ) *
                            (Real.log (M : ℝ) - 1)) -
                      Real.log Real.pi / 2 := by
                    exact congrArg
                      (fun x : ℝ =>
                        (Real.log ((Nat.factorial M : ℕ) : ℝ) -
                          (1 / 2 : ℝ) * x -
                            (M : ℝ) * (Real.log (M : ℝ) - 1)) -
                          Real.log Real.pi / 2)
                      h2.symm
                  _ =
                      (Real.log ((Nat.factorial M : ℕ) : ℝ) -
                        (1 / 2 : ℝ) * Real.log ((2 : ℝ) * M) -
                          (M : ℝ) *
                            Real.log ((M : ℝ) / Real.exp 1)) -
                      Real.log Real.pi / 2 := by
                    exact congrArg
                      (fun x : ℝ =>
                        (Real.log ((Nat.factorial M : ℕ) : ℝ) -
                          (1 / 2 : ℝ) * Real.log ((2 : ℝ) * M) -
                            (M : ℝ) * x) -
                          Real.log Real.pi / 2)
                      h3.symm
                  _ =
                      (Real.log ((Nat.factorial M : ℕ) : ℝ) -
                        (1 / 2 : ℝ) * Real.log ((2 : ℝ) * M) -
                          (M : ℝ) *
                            Real.log ((M : ℝ) / Real.exp 1)) -
                      Real.log (Real.sqrt Real.pi) := by
                    exact congrArg
                      (fun x : ℝ =>
                        (Real.log ((Nat.factorial M : ℕ) : ℝ) -
                          (1 / 2 : ℝ) * Real.log ((2 : ℝ) * M) -
                            (M : ℝ) *
                              Real.log ((M : ℝ) / Real.exp 1)) -
                          x)
                      h1.symm
    _ =
        Real.log (Stirling.stirlingSeq M) -
          Real.log (Real.sqrt Real.pi) := by
          exact Stirling.log_stirlingSeq_formula M

/-- The complex factorial Stirling endpoint error is the coercion of its real
normal form. -/
theorem Complex.binetAbelPlanaFactorialStirlingError_eq_ofReal
    (M : ℕ)
    (hM : M ≠ 0) :
    Complex.binetAbelPlanaFactorialStirlingError M =
      (Real.binetAbelPlanaFactorialStirlingError M : ℂ) := by
  have hMpos_nat : 0 < M := Nat.pos_of_ne_zero hM
  have hMpos_real : 0 < (M : ℝ) := Nat.cast_pos.mpr hMpos_nat
  have hfact_nonneg :
      0 ≤ ((Nat.factorial M : ℕ) : ℝ) :=
    Nat.cast_nonneg (Nat.factorial M)
  have hM_nonneg : 0 ≤ (M : ℝ) := hMpos_real.le
  have htwo_pi_nonneg : 0 ≤ (2 : ℝ) * Real.pi :=
    (mul_pos two_pos Real.pi_pos).le
  dsimp [Complex.binetAbelPlanaFactorialStirlingError,
    Real.binetAbelPlanaFactorialStirlingError]
  calc
    Complex.log (((Nat.factorial M : ℕ) : ℂ)) -
        (((M : ℂ) + (1 / 2 : ℂ)) * Complex.log (M : ℂ) -
          (M : ℂ) + (((Real.log (2 * Real.pi) : ℝ) : ℂ) / 2)) =
        ((Real.log ((Nat.factorial M : ℕ) : ℝ) : ℝ) : ℂ) -
          (((M : ℂ) + (1 / 2 : ℂ)) *
            ((Real.log (M : ℝ) : ℝ) : ℂ) -
            (M : ℂ) + (((Real.log (2 * Real.pi) : ℝ) : ℂ) / 2)) := by
        exact
          congrArg
            (fun z : ℂ =>
              z -
                (((M : ℂ) + (1 / 2 : ℂ)) * Complex.log (M : ℂ) -
                  (M : ℂ) +
                    (((Real.log (2 * Real.pi) : ℝ) : ℂ) / 2)))
            (Complex.ofReal_log_nonneg_eq_complex_log hfact_nonneg).symm
    _ =
        ((Real.log ((Nat.factorial M : ℕ) : ℝ) : ℝ) : ℂ) -
          (((M : ℂ) + (1 / 2 : ℂ)) *
            ((Real.log (M : ℝ) : ℝ) : ℂ) -
            (M : ℂ) +
              (((Real.log (2 * Real.pi) : ℝ) : ℂ) / 2)) := by
        exact rfl
    _ =
        (Real.log ((Nat.factorial M : ℕ) : ℝ) -
          (((M : ℝ) + (1 / 2 : ℝ)) * Real.log (M : ℝ) -
            (M : ℝ) + Real.log (2 * Real.pi) / 2) : ℝ) := by
        exact
          (Complex.ofReal_factorialStirlingEndpoint_algebra
            (Real.log ((Nat.factorial M : ℕ) : ℝ))
            (M : ℝ)
            (Real.log (M : ℝ))
            (Real.log (2 * Real.pi))).symm

/-- The real factorial Stirling endpoint error tends to zero. -/
theorem Real.binetAbelPlanaFactorialStirlingError_tendsto_zero_owner :
    Tendsto
      (fun N : ℕ =>
        Real.binetAbelPlanaFactorialStirlingError (N + 1))
      atTop
      (𝓝 (0 : ℝ)) := by
  have hstirling :
      Tendsto
        (fun N : ℕ => Stirling.stirlingSeq (N + 1))
        atTop
        (𝓝 (Real.sqrt Real.pi)) :=
    Stirling.tendsto_stirlingSeq_sqrt_pi.comp
      (tendsto_add_atTop_nat 1)
  have hsqrt_ne : Real.sqrt Real.pi ≠ 0 :=
    (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hlog :
      Tendsto
        (fun N : ℕ => Real.log (Stirling.stirlingSeq (N + 1)))
        atTop
        (𝓝 (Real.log (Real.sqrt Real.pi))) :=
    (Real.continuousAt_log hsqrt_ne).tendsto.comp hstirling
  have hsub :
      Tendsto
        (fun N : ℕ =>
          Real.log (Stirling.stirlingSeq (N + 1)) -
            Real.log (Real.sqrt Real.pi))
        atTop
        (𝓝 (Real.log (Real.sqrt Real.pi) -
          Real.log (Real.sqrt Real.pi))) :=
    hlog.sub tendsto_const_nhds
  have heq :
      (fun N : ℕ =>
        Real.binetAbelPlanaFactorialStirlingError (N + 1)) =
      (fun N : ℕ =>
        Real.log (Stirling.stirlingSeq (N + 1)) -
          Real.log (Real.sqrt Real.pi)) := by
    funext N
    exact
      Real.binetAbelPlanaFactorialStirlingError_eq_log_stirlingSeq_sub_log_sqrt_pi
        (N + 1)
        (Nat.succ_ne_zero N)
  exact sub_self (Real.log (Real.sqrt Real.pi)) ▸ (heq ▸ hsub)

/-- The endpoint shift error measuring
`(M + w + 1/2) log (1 + w/M) - w`, in branch-safe difference form. -/
noncomputable def Complex.binetAbelPlanaEndpointLogShiftError
    (w : ℂ)
    (M : ℕ) : ℂ :=
  ((w + (M : ℂ) + (1 / 2 : ℂ)) *
      (Complex.log (M : ℂ) - Complex.log (w + (M : ℂ)))) +
    w

/-- The positive-real scaling factor in the endpoint logarithm. -/
noncomputable def Complex.binetEndpointScale
    (M : ℕ) : ℂ :=
  (M : ℂ)

/-- The small logarithmic endpoint variable `w / M`. -/
noncomputable def Complex.binetEndpointSmallVariable
    (w : ℂ)
    (M : ℕ) : ℂ :=
  w / Complex.binetEndpointScale M

/-- Norm of division by the positive natural endpoint scale. -/
theorem Complex.norm_div_natCast
    (z : ℂ)
    (M : ℕ) :
    ‖z / (M : ℂ)‖ = ‖z‖ / (M : ℝ) := by
  calc
    ‖z / (M : ℂ)‖ = ‖z‖ / ‖(M : ℂ)‖ := norm_div z (M : ℂ)
    _ = ‖z‖ / (M : ℝ) := by
      exact congrArg (fun x : ℝ => ‖z‖ / x)
        (Complex.norm_natCast M)

/-- Norm of the endpoint small variable after unfolding the endpoint scale. -/
theorem Complex.norm_binetEndpointSmallVariable_eq
    (w : ℂ)
    (M : ℕ) :
    ‖Complex.binetEndpointSmallVariable w M‖ = ‖w‖ / (M : ℝ) := by
  dsimp [Complex.binetEndpointSmallVariable, Complex.binetEndpointScale]
  exact Complex.norm_div_natCast w M

/-- The endpoint logarithmic Taylor error `log (1 + z) - z`. -/
noncomputable def Complex.binetEndpointLogTaylorError
    (w : ℂ)
    (M : ℕ) : ℂ :=
  Complex.log (1 + Complex.binetEndpointSmallVariable w M) -
    Complex.binetEndpointSmallVariable w M

/-- The endpoint logarithmic branch identity in the open right half-plane. -/
theorem Complex.binetEndpoint_log_nat_add_eq_log_nat_add_log_one_add
    {w : ℂ}
    {M : ℕ}
    (hM : M ≠ 0)
    (hw : 0 < w.re) :
    Complex.log (w + (M : ℂ)) =
      Complex.log (M : ℂ) +
        Complex.log (1 + Complex.binetEndpointSmallVariable w M) := by
  have hMpos_nat : 0 < M := Nat.pos_of_ne_zero hM
  have hMpos_real : 0 < (M : ℝ) := Nat.cast_pos.mpr hMpos_nat
  have hprod :
      ((M : ℂ) *
          (1 + Complex.binetEndpointSmallVariable w M)) =
        w + (M : ℂ) := by
    have hM_ne : (M : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr hM
    have hcancel : (M : ℂ) * (M : ℂ)⁻¹ = 1 :=
      mul_inv_cancel₀ hM_ne
    dsimp [Complex.binetEndpointSmallVariable, Complex.binetEndpointScale]
    calc
      (M : ℂ) * (1 + w / (M : ℂ)) =
          (M : ℂ) * 1 + (M : ℂ) * (w / (M : ℂ)) := by
        exact mul_add (M : ℂ) 1 (w / (M : ℂ))
      _ = (M : ℂ) + (M : ℂ) * (w / (M : ℂ)) := by
        exact congrArg
          (fun x : ℂ => x + (M : ℂ) * (w / (M : ℂ)))
          (mul_one (M : ℂ))
      _ = (M : ℂ) + (M : ℂ) * (w * (M : ℂ)⁻¹) := by
        exact congrArg
          (fun x : ℂ => (M : ℂ) + (M : ℂ) * x)
          (div_eq_mul_inv w (M : ℂ))
      _ = (M : ℂ) + (M : ℂ) * ((M : ℂ)⁻¹ * w) := by
        exact congrArg
          (fun x : ℂ => (M : ℂ) + (M : ℂ) * x)
          (mul_comm w (M : ℂ)⁻¹)
      _ = (M : ℂ) + ((M : ℂ) * (M : ℂ)⁻¹) * w := by
        exact congrArg
          (fun x : ℂ => (M : ℂ) + x)
          ((mul_assoc (M : ℂ) (M : ℂ)⁻¹ w).symm)
      _ = (M : ℂ) + 1 * w := by
        exact congrArg
          (fun x : ℂ => (M : ℂ) + x * w)
          hcancel
      _ = (M : ℂ) + w := by
        exact congrArg (fun x : ℂ => (M : ℂ) + x) (one_mul w)
      _ = w + (M : ℂ) := by
        exact add_comm (M : ℂ) w
  have hsmall_ne :
      (1 + Complex.binetEndpointSmallVariable w M) ≠ 0 := by
    intro hzero
    have hmul_zero :
        (M : ℂ) * (1 + Complex.binetEndpointSmallVariable w M) = 0 := by
      exact congrArg (fun z : ℂ => (M : ℂ) * z) hzero
    have hsum_zero : w + (M : ℂ) = 0 := by
      exact hprod.symm ▸ hmul_zero
    have hre_zero : (w + (M : ℂ)).re = 0 := by
      exact congrArg Complex.re hsum_zero
    have hre_eq : (w + (M : ℂ)).re = w.re + (M : ℝ) := by
      calc
        (w + (M : ℂ)).re = w.re + (M : ℂ).re :=
          Complex.add_re w (M : ℂ)
        _ = w.re + (M : ℝ) := by
          exact congrArg (fun r : ℝ => w.re + r)
            (Complex.ofReal_re (M : ℝ))
    have hre_pos : 0 < (w + (M : ℂ)).re := by
      exact hre_eq.symm ▸ add_pos hw hMpos_real
    exact (ne_of_gt hre_pos) hre_zero
  calc
    Complex.log (w + (M : ℂ))
        = Complex.log ((M : ℂ) *
            (1 + Complex.binetEndpointSmallVariable w M)) := by
          exact congrArg Complex.log hprod
    _ = Real.log (M : ℝ) +
          Complex.log (1 + Complex.binetEndpointSmallVariable w M) := by
          exact
            Complex.log_ofReal_mul hMpos_real hsmall_ne
    _ = Complex.log (M : ℂ) +
          Complex.log (1 + Complex.binetEndpointSmallVariable w M) := by
          exact (Complex.ofReal_log hMpos_real.le).symm

/-- Branch-safe endpoint log-shift error in Taylor-remainder normal form. -/
theorem Complex.binetAbelPlanaEndpointLogShiftError_eq_taylor_normal_form
    {w : ℂ}
    {M : ℕ}
    (hM : M ≠ 0)
    (hw : 0 < w.re) :
    Complex.binetAbelPlanaEndpointLogShiftError w M =
      -((w * (w + (1 / 2 : ℂ))) / (M : ℂ)) -
        (w + (M : ℂ) + (1 / 2 : ℂ)) *
          Complex.binetEndpointLogTaylorError w M := by
  have hlog :
      Complex.log (w + (M : ℂ)) =
        Complex.log (M : ℂ) +
          Complex.log (1 + Complex.binetEndpointSmallVariable w M) :=
    Complex.binetEndpoint_log_nat_add_eq_log_nat_add_log_one_add hM hw
  dsimp [Complex.binetAbelPlanaEndpointLogShiftError,
    Complex.binetEndpointLogTaylorError,
    Complex.binetEndpointSmallVariable,
    Complex.binetEndpointScale]
  exact
    Eq.trans
      (congrArg
        (fun z : ℂ =>
          ((w + (M : ℂ) + (1 / 2 : ℂ)) *
            (Complex.log (M : ℂ) - z)) + w)
        hlog)
      (Complex.binetEndpointLogShiftError_taylor_algebra
        (w := w)
        (L := Complex.log (1 + w / (M : ℂ)))
        hM)

/-- Eventually the endpoint small variable lies in the Taylor disk
`‖z‖ ≤ 1 / 2`. -/
theorem Complex.eventually_norm_binetEndpointSmallVariable_le_half
    (w : ℂ) :
    ∀ᶠ M : ℕ in atTop,
      ‖Complex.binetEndpointSmallVariable w M‖ ≤ (1 / 2 : ℝ) := by
  have hbound :
      ∀ᶠ M : ℕ in atTop, 2 * ‖w‖ ≤ (M : ℝ) := by
    exact eventually_ge_atTop (Nat.ceil (2 * ‖w‖))
  filter_upwards [hbound] with M hM
  by_cases hMzero : M = 0
  · subst M
    dsimp [Complex.binetEndpointSmallVariable, Complex.binetEndpointScale]
    calc
      ‖w / (0 : ℂ)‖ = 0 := by
        exact congrArg norm (div_zero w)
      _ ≤ (1 / 2 : ℝ) :=
        div_nonneg zero_le_one zero_le_two
  · have hMpos_nat : 0 < M := Nat.pos_of_ne_zero hMzero
    have hMpos_real : 0 < (M : ℝ) := Nat.cast_pos.mpr hMpos_nat
    dsimp [Complex.binetEndpointSmallVariable, Complex.binetEndpointScale]
    have htwo_ne : (2 : ℝ) ≠ 0 :=
      two_ne_zero
    have hdiv_bound :
        (2 * ‖w‖) / (2 : ℝ) ≤ (M : ℝ) / (2 : ℝ) :=
      div_le_div_of_nonneg_right hM zero_le_two
    have hleft :
        (2 * ‖w‖) / (2 : ℝ) = ‖w‖ := by
      calc
        (2 * ‖w‖) / (2 : ℝ) = (‖w‖ * 2) / (2 : ℝ) := by
          exact congrArg (fun x : ℝ => x / (2 : ℝ))
            (mul_comm (2 : ℝ) ‖w‖)
        _ = ‖w‖ :=
          mul_div_cancel_right₀ ‖w‖ htwo_ne
    have hright :
        (M : ℝ) / (2 : ℝ) = (1 / 2 : ℝ) * (M : ℝ) := by
      calc
        (M : ℝ) / (2 : ℝ) = (M : ℝ) * (2 : ℝ)⁻¹ := by
          exact div_eq_mul_inv (M : ℝ) (2 : ℝ)
        _ = (2 : ℝ)⁻¹ * (M : ℝ) := by
          exact mul_comm (M : ℝ) (2 : ℝ)⁻¹
        _ = (1 / 2 : ℝ) * (M : ℝ) := by
          exact congrArg (fun x : ℝ => x * (M : ℝ))
            (inv_eq_one_div (2 : ℝ))
    have hhalf :
        ‖w‖ ≤ (1 / 2 : ℝ) * (M : ℝ) := by
      calc
        ‖w‖ = (2 * ‖w‖) / (2 : ℝ) := hleft.symm
        _ ≤ (M : ℝ) / (2 : ℝ) := hdiv_bound
        _ = (1 / 2 : ℝ) * (M : ℝ) := hright
    have hnorm_div :
        ‖w / (M : ℂ)‖ = ‖w‖ / (M : ℝ) := by
      calc
        ‖w / (M : ℂ)‖ = ‖w‖ / ‖(M : ℂ)‖ :=
          norm_div w (M : ℂ)
        _ = ‖w‖ / (M : ℝ) := by
          exact congrArg (fun x : ℝ => ‖w‖ / x)
            (Complex.norm_natCast M)
    calc
      ‖w / (M : ℂ)‖ = ‖w‖ / (M : ℝ) := hnorm_div
      _ ≤ (1 / 2 : ℝ) :=
        (div_le_iff₀ hMpos_real).mpr hhalf

/-- A number bounded by `1 / 2` leaves a positive distance from `1`. -/
theorem Real.one_sub_pos_of_le_half
    {x : ℝ}
    (hx : x ≤ (1 / 2 : ℝ)) :
    0 < 1 - x := by
  have hhalf_lt_one : (1 / 2 : ℝ) < 1 :=
    one_half_lt_one
  have hx_lt_one : x < 1 :=
    lt_of_le_of_lt hx hhalf_lt_one
  exact sub_pos.mpr hx_lt_one

/-- A number bounded by `1 / 2` leaves at least `1 / 2` distance from `1`. -/
theorem Real.half_le_one_sub_of_le_half
    {x : ℝ}
    (hx : x ≤ (1 / 2 : ℝ)) :
    (1 / 2 : ℝ) ≤ 1 - x := by
  have hsum : (1 / 2 : ℝ) + x ≤ (1 / 2 : ℝ) + (1 / 2 : ℝ) :=
    add_le_add_left hx (1 / 2 : ℝ)
  have hsum_eq_one : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 :=
    add_halves 1
  have hsum_le_one : (1 / 2 : ℝ) + x ≤ 1 :=
    hsum_eq_one ▸ hsum
  exact le_sub_iff_add_le.mpr hsum_le_one

/-- Inverse form of the endpoint Taylor denominator bound. -/
theorem Real.inv_one_sub_le_two_of_le_half
    {x : ℝ}
    (hx : x ≤ (1 / 2 : ℝ)) :
    (1 - x)⁻¹ ≤ (2 : ℝ) := by
  have hhalf : (1 / 2 : ℝ) ≤ 1 - x :=
    Real.half_le_one_sub_of_le_half hx
  have hinv : (1 - x)⁻¹ ≤ ((1 / 2 : ℝ))⁻¹ :=
    inv_anti₀ one_half_pos hhalf
  have hhalf_inv : ((1 / 2 : ℝ))⁻¹ = (2 : ℝ) :=
    inv_one_div 2
  exact hhalf_inv ▸ hinv

/-- Cancelling the harmless factor `2 / 2` in the Taylor majorant. -/
theorem Real.mul_two_div_two
    (x : ℝ) :
    x * (2 : ℝ) / (2 : ℝ) = x := by
  exact mul_div_cancel_right₀ x two_ne_zero

/-- Cancelling `(1 / 2) * (2 * x)`. -/
theorem Real.half_mul_two_mul
    (x : ℝ) :
    (1 / 2 : ℝ) * (2 * x) = x := by
  calc
    (1 / 2 : ℝ) * (2 * x) = ((1 / 2 : ℝ) * 2) * x := by
      exact (mul_assoc (1 / 2 : ℝ) 2 x).symm
    _ = 1 * x := by
      exact congrArg (fun y : ℝ => y * x)
        (div_mul_cancel₀ (1 : ℝ) two_ne_zero)
    _ = x :=
      one_mul x

/-- The zero limit scalar expression used in squeeze arguments. -/
theorem Real.mul_zero_add_zero
    (C : ℝ) :
    C * 0 + 0 = 0 := by
  calc
    C * 0 + 0 = 0 + 0 := by
      exact congrArg (fun y : ℝ => y + 0) (mul_zero C)
    _ = 0 :=
      zero_add 0

/-- The complex norm of the real scalar `1 / 2`. -/
theorem Complex.norm_one_div_two :
    ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by
  have hnonneg : 0 ≤ (1 / 2 : ℝ) :=
    div_nonneg zero_le_one zero_le_two
  calc
    ‖(1 / 2 : ℂ)‖ = Complex.abs ((1 / 2 : ℝ) : ℂ) := by
      exact Complex.norm_eq_abs ((1 / 2 : ℂ))
    _ = |(1 / 2 : ℝ)| := Complex.abs_ofReal (1 / 2 : ℝ)
    _ = (1 / 2 : ℝ) := abs_of_nonneg hnonneg

/-- Quadratic envelope for the endpoint product numerator. -/
theorem Real.mul_add_half_le_one_add_sq
    {x : ℝ}
    (hx : 0 ≤ x) :
    x * (x + (1 / 2 : ℝ)) ≤ (1 + x) ^ 2 := by
  have hhalf_le_one : (1 / 2 : ℝ) ≤ 1 :=
    one_half_le_one
  have hadd : x + (1 / 2 : ℝ) ≤ x + 1 :=
    add_le_add_left hhalf_le_one x
  have hleft : x * (x + (1 / 2 : ℝ)) ≤ x * (x + 1) :=
    mul_le_mul_of_nonneg_left hadd hx
  have hx_le_one_add : x ≤ 1 + x :=
    le_add_of_nonneg_left zero_le_one
  have hx_add_one_nonneg : 0 ≤ x + 1 :=
    add_nonneg hx zero_le_one
  have hmiddle : x * (x + 1) ≤ (1 + x) * (x + 1) :=
    mul_le_mul_of_nonneg_right hx_le_one_add hx_add_one_nonneg
  have hright : (1 + x) * (x + 1) = (1 + x) ^ 2 := by
    exact congrArg (fun y : ℝ => (1 + x) * y) (add_comm x 1)
  calc
    x * (x + (1 / 2 : ℝ)) ≤ x * (x + 1) := hleft
    _ ≤ (1 + x) * (x + 1) := hmiddle
    _ = (1 + x) ^ 2 := hright

/-- Large endpoint control implies the small-variable half-disk condition. -/
theorem Real.le_half_mul_of_two_mul_one_add_le
    {x M : ℝ}
    (hx : 0 ≤ x)
    (hlarge : 2 * (1 + x) ≤ M) :
    x ≤ (1 / 2 : ℝ) * M := by
  have htwo_nonneg : (0 : ℝ) ≤ 2 :=
    zero_le_two
  have hdiv :
      (2 * (1 + x)) / (2 : ℝ) ≤ M / (2 : ℝ) :=
    div_le_div_of_nonneg_right hlarge htwo_nonneg
  have hleft :
      (2 * (1 + x)) / (2 : ℝ) = 1 + x := by
    calc
      (2 * (1 + x)) / (2 : ℝ) = ((1 + x) * 2) / (2 : ℝ) := by
        exact congrArg (fun y : ℝ => y / (2 : ℝ))
          (mul_comm (2 : ℝ) (1 + x))
      _ = 1 + x :=
        mul_div_cancel_right₀ (1 + x) two_ne_zero
  have hright :
      M / (2 : ℝ) = (1 / 2 : ℝ) * M := by
    calc
      M / (2 : ℝ) = M * (2 : ℝ)⁻¹ := div_eq_mul_inv M (2 : ℝ)
      _ = (2 : ℝ)⁻¹ * M := mul_comm M (2 : ℝ)⁻¹
      _ = (1 / 2 : ℝ) * M := by
        exact congrArg (fun y : ℝ => y * M) (inv_eq_one_div (2 : ℝ))
  have hone_add_le : 1 + x ≤ (1 / 2 : ℝ) * M := by
    calc
      1 + x = (2 * (1 + x)) / (2 : ℝ) := hleft.symm
      _ ≤ M / (2 : ℝ) := hdiv
      _ = (1 / 2 : ℝ) * M := hright
  have hx_le_one_add : x ≤ 1 + x :=
    le_add_of_nonneg_left zero_le_one
  exact le_trans hx_le_one_add hone_add_le

/-- The scalar identity `2 + 1 = 3` over the reals, without arithmetic automation. -/
theorem Real.two_add_one_eq_three :
    (2 : ℝ) + 1 = 3 := by
  have htwo : ((2 : ℕ) : ℝ) = 2 :=
    Nat.cast_ofNat
  have hone : ((1 : ℕ) : ℝ) = 1 :=
    Nat.cast_one
  calc
    (2 : ℝ) + 1 = ((2 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) := by
      exact (congrArg₂ HAdd.hAdd htwo hone).symm
    _ = ((2 + 1 : ℕ) : ℝ) :=
      (Nat.cast_add 2 1).symm
    _ = (3 : ℝ) :=
      Nat.cast_ofNat

/-- The scalar inequality `2 ≤ 4` over the reals. -/
theorem Real.two_le_four :
    (2 : ℝ) ≤ 4 := by
  have htwo_nonneg : (0 : ℝ) ≤ 2 :=
    zero_le_two
  have hfour_eq : (2 : ℝ) + 2 = 4 := by
    have htwo : ((2 : ℕ) : ℝ) = 2 :=
      Nat.cast_ofNat
    have hfour : ((4 : ℕ) : ℝ) = 4 :=
      Nat.cast_ofNat
    calc
      (2 : ℝ) + 2 = ((2 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) := by
        exact (congrArg₂ HAdd.hAdd htwo htwo).symm
      _ = ((2 + 2 : ℕ) : ℝ) :=
        (Nat.cast_add 2 2).symm
      _ = (4 : ℝ) :=
        hfour
  calc
    (2 : ℝ) ≤ 2 + 2 :=
      le_add_of_nonneg_right htwo_nonneg
    _ = 4 :=
      hfour_eq

/-- The scalar inequality `4 ≤ 8` over the reals. -/
theorem Real.four_le_eight :
    (4 : ℝ) ≤ 8 := by
  have hfour_nonneg : (0 : ℝ) ≤ 4 :=
    le_trans zero_le_two Real.two_le_four
  have height_eq : (4 : ℝ) + 4 = 8 := by
    have hfour : ((4 : ℕ) : ℝ) = 4 :=
      Nat.cast_ofNat
    have height : ((8 : ℕ) : ℝ) = 8 :=
      Nat.cast_ofNat
    calc
      (4 : ℝ) + 4 = ((4 : ℕ) : ℝ) + ((4 : ℕ) : ℝ) := by
        exact (congrArg₂ HAdd.hAdd hfour hfour).symm
      _ = ((4 + 4 : ℕ) : ℝ) :=
        (Nat.cast_add 4 4).symm
      _ = (8 : ℝ) :=
        height
  calc
    (4 : ℝ) ≤ 4 + 4 :=
      le_add_of_nonneg_right hfour_nonneg
    _ = 8 :=
      height_eq

/-- If `1 ≤ a`, then `2 ≤ 4 * a`. -/
theorem Real.two_le_four_mul_of_one_le
    {a : ℝ}
    (ha : 1 ≤ a) :
    (2 : ℝ) ≤ 4 * a := by
  have hfour_nonneg : (0 : ℝ) ≤ 4 :=
    le_trans zero_le_two Real.two_le_four
  have hfour_le_four_mul : (4 : ℝ) ≤ 4 * a := by
    calc
      (4 : ℝ) = 4 * 1 := (mul_one 4).symm
      _ ≤ 4 * a :=
        mul_le_mul_of_nonneg_left ha hfour_nonneg
  exact le_trans Real.two_le_four hfour_le_four_mul

/-- If `1 ≤ a`, then `4a ≤ 8a²`. -/
theorem Real.four_mul_le_eight_mul_sq_of_one_le
    {a : ℝ}
    (ha : 1 ≤ a) :
    4 * a ≤ 8 * a ^ 2 := by
  have ha_nonneg : 0 ≤ a :=
    le_trans zero_le_one ha
  have hfour_nonneg : (0 : ℝ) ≤ 4 :=
    le_trans zero_le_two Real.two_le_four
  have hfirst : 4 * a ≤ 4 * a ^ 2 := by
    have ha_le_sq : a ≤ a ^ 2 := by
      calc
        a = a * 1 := (mul_one a).symm
        _ ≤ a * a :=
          mul_le_mul_of_nonneg_left ha ha_nonneg
        _ = a ^ 2 := by
          exact (pow_two a).symm
    exact mul_le_mul_of_nonneg_left ha_le_sq hfour_nonneg
  have hsecond : 4 * a ^ 2 ≤ 8 * a ^ 2 :=
    mul_le_mul_of_nonneg_right Real.four_le_eight (sq_nonneg a)
  exact le_trans hfirst hsecond

/-- A number at least one has square bounded by cube. -/
theorem Real.square_le_cube_of_one_le
    {a : ℝ}
    (ha : 1 ≤ a) :
    a ^ 2 ≤ a ^ 3 := by
  have ha_nonneg : 0 ≤ a :=
    le_trans zero_le_one ha
  calc
    a ^ 2 = a ^ 2 * 1 := (mul_one (a ^ 2)).symm
    _ ≤ a ^ 2 * a :=
      mul_le_mul_of_nonneg_left ha (sq_nonneg a)
    _ = a ^ 3 := by
      exact (pow_succ a 2).symm

/-- The scalar identity `1 + 3 = 4` over the reals. -/
theorem Real.one_add_three_eq_four :
    (1 : ℝ) + 3 = 4 := by
  have hone : ((1 : ℕ) : ℝ) = 1 :=
    Nat.cast_one
  have hthree : ((3 : ℕ) : ℝ) = 3 :=
    Nat.cast_ofNat
  have hfour : ((4 : ℕ) : ℝ) = 4 :=
    Nat.cast_ofNat
  calc
    (1 : ℝ) + 3 = ((1 : ℕ) : ℝ) + ((3 : ℕ) : ℝ) := by
      exact (congrArg₂ HAdd.hAdd hone hthree).symm
    _ = ((1 + 3 : ℕ) : ℝ) :=
      (Nat.cast_add 1 3).symm
    _ = (4 : ℝ) :=
      hfour

/-- Collect `x + 3x` as `4x`. -/
theorem Real.add_three_mul_eq_four_mul
    (x : ℝ) :
    x + 3 * x = 4 * x := by
  calc
    x + 3 * x = 1 * x + 3 * x := by
      exact congrArg (fun y : ℝ => y + 3 * x) (one_mul x).symm
    _ = ((1 : ℝ) + 3) * x :=
      (add_mul 1 3 x).symm
    _ = 4 * x := by
      exact congrArg (fun y : ℝ => y * x) Real.one_add_three_eq_four

/-- Summing endpoint majorant pieces after the square-cube comparison. -/
theorem Real.endpoint_square_cube_sum_le_four_cube
    {a M : ℝ}
    (hM_nonneg : 0 ≤ M)
    (ha : 1 ≤ a) :
    a ^ 2 / M + 3 * a ^ 3 / M ≤ 4 * a ^ 3 / M := by
  have hsquare_le_cube : a ^ 2 ≤ a ^ 3 :=
    Real.square_le_cube_of_one_le ha
  have hdiv : a ^ 2 / M ≤ a ^ 3 / M :=
    div_le_div_of_nonneg_right hsquare_le_cube hM_nonneg
  calc
    a ^ 2 / M + 3 * a ^ 3 / M ≤
        a ^ 3 / M + 3 * a ^ 3 / M := by
      exact add_le_add_right hdiv (3 * a ^ 3 / M)
    _ = 4 * (a ^ 3 / M) :=
      Real.add_three_mul_eq_four_mul (a ^ 3 / M)
    _ = 4 * a ^ 3 / M := by
      exact (mul_div_assoc 4 (a ^ 3) M).symm

/-- The scalar identity `(1 + 1 / 2) * 2 = 3` over the reals. -/
theorem Real.one_add_half_mul_two_eq_three :
    (1 + (1 / 2 : ℝ)) * 2 = 3 := by
  calc
    (1 + (1 / 2 : ℝ)) * 2 =
        1 * 2 + (1 / 2 : ℝ) * 2 := by
      exact add_mul 1 (1 / 2 : ℝ) 2
    _ = 2 + (1 / 2 : ℝ) * 2 := by
      exact congrArg
        (fun y : ℝ => y + (1 / 2 : ℝ) * 2)
        (one_mul 2)
    _ = 2 + 1 := by
      exact congrArg
        (fun y : ℝ => 2 + y)
        (div_mul_cancel₀ (1 : ℝ) two_ne_zero)
    _ = 3 :=
      Real.two_add_one_eq_three

/-- The real identity `3 / 2 = 1 + 1 / 2`. -/
theorem Real.three_div_two_eq_one_add_half :
    ((3 : ℝ) / 2) = 1 + (1 / 2 : ℝ) := by
  apply (div_eq_iff two_ne_zero).mpr
  exact Real.one_add_half_mul_two_eq_three.symm

/-- Rewriting `(3 / 2) * M` as `M + (1 / 2) * M`. -/
theorem Real.three_div_two_mul
    (M : ℝ) :
    ((3 : ℝ) / 2) * M = M + (1 / 2 : ℝ) * M := by
  calc
    ((3 : ℝ) / 2) * M = (1 + (1 / 2 : ℝ)) * M := by
      exact congrArg (fun y : ℝ => y * M)
        Real.three_div_two_eq_one_add_half
    _ = 1 * M + (1 / 2 : ℝ) * M := by
      exact add_mul 1 (1 / 2 : ℝ) M
    _ = M + (1 / 2 : ℝ) * M := by
      exact congrArg
        (fun y : ℝ => y + (1 / 2 : ℝ) * M)
        (one_mul M)

/-- Endpoint norm scalar bound used in the large endpoint estimate. -/
theorem Real.endpoint_add_half_le_three_halves
    {x M : ℝ}
    (hx : 0 ≤ x)
    (hlarge : 2 * (1 + x) ≤ M) :
    x + M + (1 / 2 : ℝ) ≤ (3 / 2 : ℝ) * M := by
  have hone_add_le_halfM : 1 + x ≤ (1 / 2 : ℝ) * M := by
    have htwo_nonneg : (0 : ℝ) ≤ 2 :=
      zero_le_two
    have hdiv :
        (2 * (1 + x)) / (2 : ℝ) ≤ M / (2 : ℝ) :=
      div_le_div_of_nonneg_right hlarge htwo_nonneg
    have hleft :
        (2 * (1 + x)) / (2 : ℝ) = 1 + x := by
      calc
        (2 * (1 + x)) / (2 : ℝ) = ((1 + x) * 2) / (2 : ℝ) := by
          exact congrArg (fun y : ℝ => y / (2 : ℝ))
            (mul_comm (2 : ℝ) (1 + x))
        _ = 1 + x :=
          mul_div_cancel_right₀ (1 + x) two_ne_zero
    have hright :
        M / (2 : ℝ) = (1 / 2 : ℝ) * M := by
      calc
        M / (2 : ℝ) = M * (2 : ℝ)⁻¹ := div_eq_mul_inv M (2 : ℝ)
        _ = (2 : ℝ)⁻¹ * M := mul_comm M (2 : ℝ)⁻¹
        _ = (1 / 2 : ℝ) * M := by
          exact congrArg (fun y : ℝ => y * M) (inv_eq_one_div (2 : ℝ))
    calc
      1 + x = (2 * (1 + x)) / (2 : ℝ) := hleft.symm
      _ ≤ M / (2 : ℝ) := hdiv
      _ = (1 / 2 : ℝ) * M := hright
  have hx_half_le : x + (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) * M := by
    have hhalf_le_one : (1 / 2 : ℝ) ≤ 1 :=
      one_half_le_one
    have hadd : x + (1 / 2 : ℝ) ≤ x + 1 :=
      add_le_add_left hhalf_le_one x
    have hcomm : x + 1 = 1 + x :=
      add_comm x 1
    exact le_trans hadd (hcomm ▸ hone_add_le_halfM)
  calc
    x + M + (1 / 2 : ℝ) = M + (x + (1 / 2 : ℝ)) := by
      calc
        x + M + (1 / 2 : ℝ) = (x + M) + (1 / 2 : ℝ) := rfl
        _ = (M + x) + (1 / 2 : ℝ) := by
          exact congrArg (fun y : ℝ => y + (1 / 2 : ℝ))
            (add_comm x M)
        _ = M + (x + (1 / 2 : ℝ)) := add_assoc M x (1 / 2 : ℝ)
    _ ≤ M + (1 / 2 : ℝ) * M :=
      add_le_add_left hx_half_le M
    _ = (3 / 2 : ℝ) * M :=
      (Real.three_div_two_mul M).symm

/-- Scalar denominator normalization for the endpoint Taylor second term. -/
theorem Real.endpoint_second_term_le_cubic_over_endpoint
    {r M : ℝ}
    (hMpos : 0 < M)
    (hr_nonneg : 0 ≤ r) :
    ((3 / 2 : ℝ) * M) * ((r / M) ^ 2) ≤
      3 * (1 + r) ^ 3 / M := by
  have hM_nonneg : 0 ≤ M := hMpos.le
  have hleft_eq :
      ((3 / 2 : ℝ) * M) * ((r / M) ^ 2) =
        ((3 / 2 : ℝ) * r ^ 2) / M := by
    have hM_ne : M ≠ 0 := hMpos.ne'
    calc
      ((3 / 2 : ℝ) * M) * ((r / M) ^ 2) =
          ((3 / 2 : ℝ) * M) * ((r / M) * (r / M)) := by
        exact congrArg (fun x : ℝ => ((3 / 2 : ℝ) * M) * x)
          (pow_two (r / M))
      _ = ((3 / 2 : ℝ) * M) * ((r * M⁻¹) * (r * M⁻¹)) := by
        exact congrArg
          (fun x : ℝ => ((3 / 2 : ℝ) * M) * (x * x))
          (div_eq_mul_inv r M)
      _ = (3 / 2 : ℝ) * ((M * M⁻¹) * (r * (r * M⁻¹))) := by
        ac_rfl
      _ = (3 / 2 : ℝ) * (1 * (r * (r * M⁻¹))) := by
        exact congrArg
          (fun x : ℝ => (3 / 2 : ℝ) * (x * (r * (r * M⁻¹))))
          (mul_inv_cancel₀ hM_ne)
      _ = (3 / 2 : ℝ) * (r * (r * M⁻¹)) := by
        exact congrArg (fun x : ℝ => (3 / 2 : ℝ) * x)
          (one_mul (r * (r * M⁻¹)))
      _ = (3 / 2 : ℝ) * ((r * r) * M⁻¹) := by
        exact congrArg (fun x : ℝ => (3 / 2 : ℝ) * x)
          (mul_assoc r r M⁻¹).symm
      _ = (3 / 2 : ℝ) * (r ^ 2 * M⁻¹) := by
        exact congrArg (fun x : ℝ => (3 / 2 : ℝ) * (x * M⁻¹))
          (pow_two r).symm
      _ = ((3 / 2 : ℝ) * r ^ 2) * M⁻¹ :=
        mul_assoc (3 / 2 : ℝ) (r ^ 2) M⁻¹
      _ = ((3 / 2 : ℝ) * r ^ 2) / M :=
        (div_eq_mul_inv ((3 / 2 : ℝ) * r ^ 2) M).symm
  have hcoef_le : (3 / 2 : ℝ) ≤ 3 := by
    calc
      (3 / 2 : ℝ) = 1 + (1 / 2 : ℝ) :=
        Real.three_div_two_eq_one_add_half
      _ ≤ 1 + 1 :=
        add_le_add_left one_half_le_one 1
      _ = (2 : ℝ) := by
        exact one_add_one_eq_two
      _ ≤ 3 := by
        exact two_le_three
  have hcoef :
      (3 / 2 : ℝ) * r ^ 2 ≤ 3 * r ^ 2 := by
    exact mul_le_mul_of_nonneg_right hcoef_le (sq_nonneg r)
  have hone_add_nonneg : 0 ≤ 1 + r :=
    add_nonneg zero_le_one hr_nonneg
  have habs_bound : |r| ≤ 1 + r := by
    exact abs_le.mpr
      ⟨le_trans (neg_nonpos.mpr hone_add_nonneg) hr_nonneg,
        le_add_of_nonneg_left zero_le_one⟩
  have hsquare_le_one_add_square :
      r ^ 2 ≤ (1 + r) ^ 2 := by
    exact sq_le_sq.mpr habs_bound
  have hone_le : 1 ≤ 1 + r :=
    le_add_of_nonneg_right hr_nonneg
  have hsquare_le_cube :
      r ^ 2 ≤ (1 + r) ^ 3 :=
    le_trans hsquare_le_one_add_square
      (Real.square_le_cube_of_one_le hone_le)
  have hthree_nonneg : (0 : ℝ) ≤ 3 :=
    le_trans zero_le_two two_le_three
  calc
    ((3 / 2 : ℝ) * M) * ((r / M) ^ 2) =
        ((3 / 2 : ℝ) * r ^ 2) / M := hleft_eq
    _ ≤ (3 * r ^ 2) / M :=
      div_le_div_of_nonneg_right hcoef hM_nonneg
    _ ≤ (3 * (1 + r) ^ 3) / M := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsquare_le_cube hthree_nonneg)
        hM_nonneg
    _ = 3 * (1 + r) ^ 3 / M :=
      (mul_div_assoc 3 ((1 + r) ^ 3) M).symm

/-- Subtracting the shared first two summands leaves the third summand. -/
theorem Complex.add_add_sub_add_eq_right
    (a b c : ℂ) :
    (a + b + c) - (a + b) = c := by
  calc
    (a + b + c) - (a + b) = ((a + b) + c) - (a + b) := rfl
    _ = c :=
      add_sub_cancel_left c (a + b)

/-- Triangle estimate for a difference of two negated complex terms. -/
theorem Complex.norm_neg_sub_le_add_norm
    (a b : ℂ) :
    ‖-a - b‖ ≤ ‖a‖ + ‖b‖ := by
  calc
    ‖-a - b‖ = ‖(-a) + (-b)‖ := by
      exact congrArg norm (sub_eq_add_neg (-a) b)
    _ ≤ ‖-a‖ + ‖-b‖ :=
      norm_add_le (-a) (-b)
    _ = ‖a‖ + ‖-b‖ := by
      exact congrArg (fun r : ℝ => r + ‖-b‖) (norm_neg a)
    _ = ‖a‖ + ‖b‖ := by
      exact congrArg (fun r : ℝ => ‖a‖ + r) (norm_neg b)

/-- The real part of a real multiple of `I` is zero. -/
theorem Complex.real_cast_mul_I_re
    (s : ℝ) :
    ((s : ℂ) * Complex.I).re = 0 := by
  calc
    ((s : ℂ) * Complex.I).re =
        (s : ℂ).re * Complex.I.re - (s : ℂ).im * Complex.I.im := by
      exact Complex.mul_re (s : ℂ) Complex.I
    _ = s * Complex.I.re - (s : ℂ).im * Complex.I.im := by
      exact congrArg
        (fun r : ℝ => r * Complex.I.re - (s : ℂ).im * Complex.I.im)
        (Complex.ofReal_re s)
    _ = s * 0 - (s : ℂ).im * Complex.I.im := by
      exact congrArg
        (fun r : ℝ => s * r - (s : ℂ).im * Complex.I.im)
        Complex.I_re
    _ = s * 0 - 0 * Complex.I.im := by
      exact congrArg
        (fun r : ℝ => s * 0 - r * Complex.I.im)
        (Complex.ofReal_im s)
    _ = s * 0 - 0 * 1 := by
      exact congrArg
        (fun r : ℝ => s * 0 - 0 * r)
        Complex.I_im
    _ = 0 - 0 * 1 := by
      exact congrArg (fun r : ℝ => r - 0 * 1) (mul_zero s)
    _ = 0 - 0 := by
      exact congrArg (fun r : ℝ => 0 - r) (zero_mul (1 : ℝ))
    _ = 0 :=
      sub_self 0

/-- Replace a final zero summand after proving it is zero. -/
theorem Real.add_right_zero_after_eq_zero
    (a b c : ℝ)
    (h : c = 0) :
    a + b + c = a + b := by
  calc
    a + b + c = a + b + 0 := by
      exact congrArg (fun r : ℝ => a + b + r) h
    _ = a + b :=
      add_zero (a + b)

/-- Norm of `I / z` expressed as the inverse norm of `z`. -/
theorem Complex.norm_I_div_eq_inv_norm
    (z : ℂ) :
    ‖Complex.I‖ / ‖z‖ = ‖z‖⁻¹ := by
  calc
    ‖Complex.I‖ / ‖z‖ = (1 : ℝ) / ‖z‖ := by
      exact congrArg (fun r : ℝ => r / ‖z‖) Complex.norm_I
    _ = ‖z‖⁻¹ :=
      (inv_eq_one_div ‖z‖).symm

/-- Coercing a real negative before multiplying by `I`. -/
theorem Complex.ofReal_neg_mul_I
    (t : ℝ) :
    ((-t : ℝ) : ℂ) * Complex.I = -((t : ℂ) * Complex.I) := by
  calc
    ((-t : ℝ) : ℂ) * Complex.I = (-(t : ℂ)) * Complex.I := by
      exact congrArg (fun z : ℂ => z * Complex.I) (Complex.ofReal_neg t)
    _ = -((t : ℂ) * Complex.I) :=
      neg_mul (t : ℂ) Complex.I

/-- Normalize `t - (-t)` to `2 * t`. -/
theorem Real.sub_neg_eq_two_mul
    (t : ℝ) :
    t - (-t) = 2 * t := by
  calc
    t - (-t) = t + t :=
      sub_neg_eq_add t t
    _ = (1 : ℝ) * t + 1 * t := by
      exact congrArg₂ HAdd.hAdd (one_mul t).symm (one_mul t).symm
    _ = ((1 : ℝ) + 1) * t :=
      (add_mul 1 1 t).symm
    _ = 2 * t := by
      exact congrArg (fun r : ℝ => r * t) one_add_one_eq_two

/-- Move the denominator of `(2 * t) / d` into the coefficient of `t`. -/
theorem Real.two_mul_div_eq_div_mul
    (t d : ℝ) :
    (2 * t) / d = ((2 : ℝ) / d) * t := by
  calc
    (2 * t) / d = (2 * t) * d⁻¹ := div_eq_mul_inv (2 * t) d
    _ = 2 * (t * d⁻¹) := mul_assoc 2 t d⁻¹
    _ = 2 * (d⁻¹ * t) := by
      exact congrArg (fun y : ℝ => 2 * y) (mul_comm t d⁻¹)
    _ = (2 * d⁻¹) * t := (mul_assoc 2 d⁻¹ t).symm
    _ = ((2 : ℝ) / d) * t := by
      exact congrArg (fun y : ℝ => y * t) (div_eq_mul_inv 2 d).symm

/-- Move a denominator inside the second factor. -/
theorem Real.mul_mul_div_eq_mul_div
    (A t d : ℝ) :
    (A * t) / d = A * (t / d) :=
  mul_div_assoc A t d

/-- Reassociate `2 * (C * K)` as `(2 * C) * K`. -/
theorem Real.two_mul_assoc
    (C K : ℝ) :
    2 * (C * K) = (2 * C) * K :=
  (mul_assoc 2 C K).symm

/-- The norm of the complex natural `2`, in nat-cast normal form. -/
theorem Complex.norm_two_natCast :
    ‖(2 : ℂ)‖ = (2 : ℝ) :=
  Complex.norm_natCast 2

/-- Taylor bound for the endpoint logarithmic error in the eventual small
variable range. -/
theorem Complex.norm_binetEndpointLogTaylorError_le_square
    {w : ℂ}
    {M : ℕ}
    (hsmall :
      ‖Complex.binetEndpointSmallVariable w M‖ ≤ (1 / 2 : ℝ)) :
    ‖Complex.binetEndpointLogTaylorError w M‖ ≤
      ‖Complex.binetEndpointSmallVariable w M‖ ^ 2 := by
  have hlt :
      ‖Complex.binetEndpointSmallVariable w M‖ < 1 :=
    lt_of_le_of_lt hsmall one_half_lt_one
  have hraw :
      ‖Complex.log (1 + Complex.binetEndpointSmallVariable w M) -
          Complex.binetEndpointSmallVariable w M‖ ≤
        ‖Complex.binetEndpointSmallVariable w M‖ ^ 2 *
          (1 - ‖Complex.binetEndpointSmallVariable w M‖)⁻¹ / 2 :=
    Complex.norm_log_one_add_sub_self_le hlt
  have hden :
      (1 - ‖Complex.binetEndpointSmallVariable w M‖)⁻¹ ≤ (2 : ℝ) := by
    exact Real.inv_one_sub_le_two_of_le_half hsmall
  dsimp [Complex.binetEndpointLogTaylorError]
  calc
    ‖Complex.log (1 + Complex.binetEndpointSmallVariable w M) -
        Complex.binetEndpointSmallVariable w M‖
        ≤
        ‖Complex.binetEndpointSmallVariable w M‖ ^ 2 *
          (1 - ‖Complex.binetEndpointSmallVariable w M‖)⁻¹ / 2 := hraw
    _ ≤ ‖Complex.binetEndpointSmallVariable w M‖ ^ 2 * 2 / 2 := by
      exact
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hden
            (sq_nonneg ‖Complex.binetEndpointSmallVariable w M‖))
          zero_le_two
    _ = ‖Complex.binetEndpointSmallVariable w M‖ ^ 2 := by
      exact Real.mul_two_div_two
        (‖Complex.binetEndpointSmallVariable w M‖ ^ 2)

/-- Large-endpoint bound for the branch-safe logarithmic shift error. -/
theorem Complex.norm_binetAbelPlanaEndpointLogShiftError_le_large_endpoint_majorant
    {w : ℂ}
    {M : ℕ}
    (hM : M ≠ 0)
    (hw : 0 < w.re)
    (hlarge : 2 * (1 + ‖w‖) ≤ (M : ℝ)) :
    ‖Complex.binetAbelPlanaEndpointLogShiftError w M‖ ≤
      4 * (1 + ‖w‖) ^ 3 / (M : ℝ) := by
  have hMpos_nat : 0 < M := Nat.pos_of_ne_zero hM
  have hMpos_real : 0 < (M : ℝ) := Nat.cast_pos.mpr hMpos_nat
  have hM_complex_ne : (M : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr hM
  have hsmall :
      ‖Complex.binetEndpointSmallVariable w M‖ ≤ (1 / 2 : ℝ) := by
    have hhalf : ‖w‖ ≤ (1 / 2 : ℝ) * (M : ℝ) := by
      exact Real.le_half_mul_of_two_mul_one_add_le
        (norm_nonneg w)
        hlarge
    calc
      ‖Complex.binetEndpointSmallVariable w M‖ = ‖w‖ / (M : ℝ) :=
        Complex.norm_binetEndpointSmallVariable_eq w M
      _ ≤ (1 / 2 : ℝ) :=
        (div_le_iff₀ hMpos_real).mpr hhalf
  have htaylor :
      ‖Complex.binetEndpointLogTaylorError w M‖ ≤
        ‖Complex.binetEndpointSmallVariable w M‖ ^ 2 :=
    Complex.norm_binetEndpointLogTaylorError_le_square hsmall
  have hsmall_norm :
      ‖Complex.binetEndpointSmallVariable w M‖ =
        ‖w‖ / (M : ℝ) := by
    exact Complex.norm_binetEndpointSmallVariable_eq w M
  have hnormal :
      Complex.binetAbelPlanaEndpointLogShiftError w M =
        -((w * (w + (1 / 2 : ℂ))) / (M : ℂ)) -
          (w + (M : ℂ) + (1 / 2 : ℂ)) *
            Complex.binetEndpointLogTaylorError w M :=
    Complex.binetAbelPlanaEndpointLogShiftError_eq_taylor_normal_form hM hw
  have hfirst :
      ‖(w * (w + (1 / 2 : ℂ))) / (M : ℂ)‖ ≤
        (1 + ‖w‖) ^ 2 / (M : ℝ) := by
    have hdiv_norm :
        ‖(w * (w + (1 / 2 : ℂ))) / (M : ℂ)‖ =
          ‖w * (w + (1 / 2 : ℂ))‖ / (M : ℝ) :=
      Complex.norm_div_natCast (w * (w + (1 / 2 : ℂ))) M
    have hnum :
        ‖w * (w + (1 / 2 : ℂ))‖ ≤ (1 + ‖w‖) ^ 2 := by
      calc
        ‖w * (w + (1 / 2 : ℂ))‖
            = ‖w‖ * ‖w + (1 / 2 : ℂ)‖ := norm_mul _ _
        _ ≤ ‖w‖ * (‖w‖ + ‖(1 / 2 : ℂ)‖) := by
          exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg w)
        _ ≤ (1 + ‖w‖) ^ 2 := by
          have hhalf_norm : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) :=
            Complex.norm_one_div_two
          have htransport :
              ‖w‖ * (‖w‖ + ‖(1 / 2 : ℂ)‖) =
                ‖w‖ * (‖w‖ + (1 / 2 : ℝ)) := by
            exact congrArg
              (fun y : ℝ => ‖w‖ * (‖w‖ + y))
              hhalf_norm
          calc
            ‖w‖ * (‖w‖ + ‖(1 / 2 : ℂ)‖) =
                ‖w‖ * (‖w‖ + (1 / 2 : ℝ)) := htransport
            _ ≤ (1 + ‖w‖) ^ 2 :=
              Real.mul_add_half_le_one_add_sq (norm_nonneg w)
    calc
      ‖(w * (w + (1 / 2 : ℂ))) / (M : ℂ)‖ =
          ‖w * (w + (1 / 2 : ℂ))‖ / (M : ℝ) := hdiv_norm
      _ ≤ (1 + ‖w‖) ^ 2 / (M : ℝ) :=
        div_le_div_of_nonneg_right hnum hMpos_real.le
  have hsecond :
      ‖(w + (M : ℂ) + (1 / 2 : ℂ)) *
          Complex.binetEndpointLogTaylorError w M‖ ≤
        3 * (1 + ‖w‖) ^ 3 / (M : ℝ) := by
    have hendpoint :
        ‖w + (M : ℂ) + (1 / 2 : ℂ)‖ ≤
          (3 / 2 : ℝ) * (M : ℝ) := by
      calc
        ‖w + (M : ℂ) + (1 / 2 : ℂ)‖
            ≤ ‖w‖ + ‖(M : ℂ)‖ + ‖(1 / 2 : ℂ)‖ := by
              exact (norm_add_le (w + (M : ℂ)) (1 / 2 : ℂ)).trans
                (add_le_add_right (norm_add_le w (M : ℂ)) ‖(1 / 2 : ℂ)‖)
        _ = ‖w‖ + (M : ℝ) + (1 / 2 : ℝ) := by
              have hM_norm : ‖(M : ℂ)‖ = (M : ℝ) :=
                Complex.norm_natCast M
              have hhalf_norm : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) :=
                Complex.norm_one_div_two
              exact congrArg₂ HAdd.hAdd
                (congrArg₂ HAdd.hAdd rfl hM_norm)
                hhalf_norm
        _ ≤ (3 / 2 : ℝ) * (M : ℝ) := by
              exact Real.endpoint_add_half_le_three_halves
                (norm_nonneg w)
                hlarge
    have htailor_bound :
        ‖Complex.binetEndpointLogTaylorError w M‖ ≤
          (‖w‖ / (M : ℝ)) ^ 2 := by
      exact hsmall_norm.symm ▸ htaylor
    calc
      ‖(w + (M : ℂ) + (1 / 2 : ℂ)) *
          Complex.binetEndpointLogTaylorError w M‖ =
        ‖w + (M : ℂ) + (1 / 2 : ℂ)‖ *
          ‖Complex.binetEndpointLogTaylorError w M‖ := norm_mul _ _
      _ 
          ≤
          ((3 / 2 : ℝ) * (M : ℝ)) *
            ((‖w‖ / (M : ℝ)) ^ 2) := by
            exact mul_le_mul hendpoint htailor_bound
              (norm_nonneg _) (norm_nonneg _)
      _ ≤ 3 * (1 + ‖w‖) ^ 3 / (M : ℝ) := by
            have hMpos : 0 < (M : ℝ) := hMpos_real
            have hr_nonneg : 0 ≤ ‖w‖ := norm_nonneg w
            exact
              Real.endpoint_second_term_le_cubic_over_endpoint
                hMpos
                hr_nonneg
  exact hnormal ▸ by
  calc
    ‖-((w * (w + (1 / 2 : ℂ))) / (M : ℂ)) -
        (w + (M : ℂ) + (1 / 2 : ℂ)) *
          Complex.binetEndpointLogTaylorError w M‖
        ≤
      ‖((w * (w + (1 / 2 : ℂ))) / (M : ℂ))‖ +
          ‖(w + (M : ℂ) + (1 / 2 : ℂ)) *
            Complex.binetEndpointLogTaylorError w M‖ := by
          exact Complex.norm_neg_sub_le_add_norm
            ((w * (w + (1 / 2 : ℂ))) / (M : ℂ))
            ((w + (M : ℂ) + (1 / 2 : ℂ)) *
              Complex.binetEndpointLogTaylorError w M)
    _ ≤
        (1 + ‖w‖) ^ 2 / (M : ℝ) +
          3 * (1 + ‖w‖) ^ 3 / (M : ℝ) := by
          exact add_le_add hfirst hsecond
    _ ≤ 4 * (1 + ‖w‖) ^ 3 / (M : ℝ) := by
          have hMpos : 0 < (M : ℝ) := hMpos_real
          have hone : 1 ≤ 1 + ‖w‖ := by
            exact le_add_of_nonneg_right (norm_nonneg w)
          have hsquare_le_cube :
              (1 + ‖w‖) ^ 2 ≤ (1 + ‖w‖) ^ 3 := by
            exact Real.square_le_cube_of_one_le hone
          exact
            (add_le_add_right
              (div_le_div_of_nonneg_right hsquare_le_cube hMpos.le)
              (3 * (1 + ‖w‖) ^ 3 / (M : ℝ))).trans
              (Real.endpoint_square_cube_sum_le_four_cube hMpos.le hone)

/-- Exact algebraic endpoint decomposition: the finite endpoint remainder is
the sum of the factorial Stirling error and the branch-safe endpoint shift
error. -/
theorem Complex.binetAbelPlanaFiniteEndpointStirlingRemainder_eq_factorial_add_shift
    (w : ℂ)
    (N : ℕ) :
    Complex.binetAbelPlanaFiniteEndpointStirlingRemainder N w =
      Complex.binetAbelPlanaFactorialStirlingError (N + 1) +
        Complex.binetAbelPlanaEndpointLogShiftError w (N + 1) := by
  dsimp [Complex.binetAbelPlanaFiniteEndpointStirlingRemainder,
    Complex.binetAbelPlanaFiniteMainTerm,
    Complex.binetLogGammaMainTerm,
    Complex.binetAbelPlanaFactorialStirlingError,
    Complex.binetAbelPlanaEndpointLogShiftError]
  ac_rfl

/-- Factorial Stirling error majorant for the endpoint decomposition. -/
noncomputable def Complex.binetAbelPlanaFactorialStirlingMajorant
    (N : ℕ) : ℝ :=
  (1 : ℝ) / (N + 1 : ℝ)

/-- Endpoint logarithmic-shift majorant for the endpoint decomposition. -/
noncomputable def Complex.binetAbelPlanaEndpointLogShiftMajorant
    (w : ℂ)
    (N : ℕ) : ℝ :=
  4 * (1 + ‖w‖) ^ 3 / (N + 1 : ℝ)

/-- Explicit endpoint-Stirling majorant for the finite Abel-Plana endpoint
remainder.

The intended classical proof gives a branch-coherent logarithmic Stirling
expansion with an `O(1 / N)` endpoint error after replacing
`log (N + 1 + w)` by `log (N + 1) + log (1 + w / (N + 1))`. -/
noncomputable def Complex.binetAbelPlanaEndpointStirlingMajorant
    (w : ℂ)
    (N : ℕ) : ℝ :=
  Complex.binetAbelPlanaFactorialStirlingMajorant N +
    Complex.binetAbelPlanaEndpointLogShiftMajorant w N

/-- The factorial Stirling majorant tends to zero. -/
theorem Complex.binetAbelPlanaFactorialStirlingMajorant_tendsto_zero :
    Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFactorialStirlingMajorant N)
      atTop
      (𝓝 (0 : ℝ)) := by
  have hinv :
      Tendsto
        (fun N : ℕ => ((N + 1 : ℝ))⁻¹)
        atTop
        (𝓝 (0 : ℝ)) := by
    have hshift :
        Tendsto
          (fun N : ℕ => (N + 1 : ℝ))
          atTop
          atTop := by
      exact
        tendsto_atTop_add_const_right atTop (1 : ℝ)
          tendsto_natCast_atTop_atTop
    exact tendsto_inv_atTop_zero.comp hshift
  have heq :
      (fun N : ℕ =>
        Complex.binetAbelPlanaFactorialStirlingMajorant N) =
      (fun N : ℕ => ((N + 1 : ℝ))⁻¹) := by
    funext N
    dsimp [Complex.binetAbelPlanaFactorialStirlingMajorant]
    exact one_div (N + 1 : ℝ)
  exact heq ▸ hinv

/-- The endpoint logarithmic-shift majorant tends to zero. -/
theorem Complex.binetAbelPlanaEndpointLogShiftMajorant_tendsto_zero
    (w : ℂ) :
    Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaEndpointLogShiftMajorant w N)
      atTop
      (𝓝 (0 : ℝ)) := by
  have hconst :
      Tendsto
        (fun _N : ℕ => 4 * (1 + ‖w‖) ^ 3)
        atTop
        (𝓝 (4 * (1 + ‖w‖) ^ 3)) :=
    tendsto_const_nhds
  have hinv :
      Tendsto
        (fun N : ℕ => ((N + 1 : ℝ))⁻¹)
        atTop
        (𝓝 (0 : ℝ)) := by
    have hshift :
        Tendsto
          (fun N : ℕ => (N + 1 : ℝ))
          atTop
          atTop := by
      exact
        tendsto_atTop_add_const_right atTop (1 : ℝ)
          tendsto_natCast_atTop_atTop
    exact tendsto_inv_atTop_zero.comp hshift
  have hmul :
      Tendsto
        (fun N : ℕ => 4 * (1 + ‖w‖) ^ 3 * ((N + 1 : ℝ))⁻¹)
        atTop
        (𝓝 (4 * (1 + ‖w‖) ^ 3 * 0)) :=
    hconst.mul hinv
  have heq :
      (fun N : ℕ =>
        Complex.binetAbelPlanaEndpointLogShiftMajorant w N) =
      (fun N : ℕ => 4 * (1 + ‖w‖) ^ 3 * ((N + 1 : ℝ))⁻¹) := by
    funext N
    dsimp [Complex.binetAbelPlanaEndpointLogShiftMajorant]
    exact div_eq_mul_inv
      (4 * (1 + ‖w‖) ^ 3)
      (N + 1 : ℝ)
  exact (mul_zero (4 * (1 + ‖w‖) ^ 3)).symm ▸ (heq ▸ hmul)

/-- The endpoint-Stirling majorant tends to zero. -/
theorem Complex.binetAbelPlanaEndpointStirlingMajorant_tendsto_zero
    (w : ℂ) :
    Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaEndpointStirlingMajorant w N)
      atTop
      (𝓝 (0 : ℝ)) := by
  have hfactorial :
      Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaFactorialStirlingMajorant N)
        atTop
        (𝓝 (0 : ℝ)) :=
    Complex.binetAbelPlanaFactorialStirlingMajorant_tendsto_zero
  have hshift :
      Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaEndpointLogShiftMajorant w N)
        atTop
        (𝓝 (0 : ℝ)) :=
    Complex.binetAbelPlanaEndpointLogShiftMajorant_tendsto_zero w
  have hsum :
      Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaFactorialStirlingMajorant N +
            Complex.binetAbelPlanaEndpointLogShiftMajorant w N)
        atTop
        (𝓝 ((0 : ℝ) + 0)) :=
    hfactorial.add hshift
  have heq :
      (fun N : ℕ =>
        Complex.binetAbelPlanaEndpointStirlingMajorant w N) =
      (fun N : ℕ =>
        Complex.binetAbelPlanaFactorialStirlingMajorant N +
          Complex.binetAbelPlanaEndpointLogShiftMajorant w N) := by
    funext N
    rfl
  exact (zero_add (0 : ℝ)).symm ▸ (heq ▸ hsum)

/-- The factorial Stirling component tends to zero by mathlib's Stirling
formula. -/
theorem Complex.binetAbelPlanaFactorialStirlingError_tendsto_zero_owner :
    Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFactorialStirlingError (N + 1))
      atTop
      (𝓝 (0 : ℂ)) := by
  have hreal :
      Tendsto
        (fun N : ℕ =>
          Real.binetAbelPlanaFactorialStirlingError (N + 1))
        atTop
        (𝓝 (0 : ℝ)) :=
    Real.binetAbelPlanaFactorialStirlingError_tendsto_zero_owner
  have hcomplex :
      Tendsto
        (fun N : ℕ =>
          (Real.binetAbelPlanaFactorialStirlingError (N + 1) : ℂ))
        atTop
        (𝓝 ((0 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.tendsto 0 |>.comp hreal
  have heq :
      (fun N : ℕ =>
        Complex.binetAbelPlanaFactorialStirlingError (N + 1)) =
      (fun N : ℕ =>
        (Real.binetAbelPlanaFactorialStirlingError (N + 1) : ℂ)) := by
    funext N
    exact
      Complex.binetAbelPlanaFactorialStirlingError_eq_ofReal
        (N + 1)
        (Nat.succ_ne_zero N)
  exact heq ▸ hcomplex

/-- Owner logarithmic-shift estimate in majorant form. -/
theorem Complex.norm_binetAbelPlanaEndpointLogShiftError_le_majorant_owner
    {w : ℂ}
    (hw : 0 < w.re) :
    ∀ᶠ N : ℕ in atTop,
      ‖Complex.binetAbelPlanaEndpointLogShiftError w (N + 1)‖ ≤
        Complex.binetAbelPlanaEndpointLogShiftMajorant w N := by
  have hlarge :
      ∀ᶠ N : ℕ in atTop,
        2 * (1 + ‖w‖) ≤ ((N + 1 : ℕ) : ℝ) := by
    refine eventually_atTop.mpr ?_
    refine ⟨Nat.ceil (2 * (1 + ‖w‖)), ?_⟩
    intro N hN
    have hceil :
        2 * (1 + ‖w‖) ≤ ((Nat.ceil (2 * (1 + ‖w‖))) : ℝ) :=
      Nat.le_ceil (2 * (1 + ‖w‖))
    have hNreal :
        ((Nat.ceil (2 * (1 + ‖w‖))) : ℝ) ≤ (N : ℝ) :=
      Nat.cast_le.mpr hN
    have hN_le_succ : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
      exact Nat.cast_le.mpr (Nat.le_succ N)
    exact hceil.trans (hNreal.trans hN_le_succ)
  filter_upwards [hlarge] with N hNlarge
  have hM_ne : N + 1 ≠ 0 := Nat.succ_ne_zero N
  have hlarge_M :
      2 * (1 + ‖w‖) ≤ ((N + 1 : ℕ) : ℝ) :=
    hNlarge
  have hraw :
      ‖Complex.binetAbelPlanaEndpointLogShiftError w (N + 1)‖ ≤
        4 * (1 + ‖w‖) ^ 3 / ((N + 1 : ℕ) : ℝ) :=
    Complex.norm_binetAbelPlanaEndpointLogShiftError_le_large_endpoint_majorant
      hM_ne hw hlarge_M
  dsimp [Complex.binetAbelPlanaEndpointLogShiftMajorant]
  exact hraw

/-- The endpoint logarithmic-shift component tends to zero from its explicit
majorant. -/
theorem Complex.binetAbelPlanaEndpointLogShiftError_tendsto_zero_owner
    {w : ℂ}
    (hw : 0 < w.re) :
    Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaEndpointLogShiftError w (N + 1))
      atTop
      (𝓝 (0 : ℂ)) := by
  have hbound :
      ∀ᶠ N : ℕ in atTop,
        ‖Complex.binetAbelPlanaEndpointLogShiftError w (N + 1)‖ ≤
          Complex.binetAbelPlanaEndpointLogShiftMajorant w N :=
    Complex.norm_binetAbelPlanaEndpointLogShiftError_le_majorant_owner hw
  have hmajorant :
      Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaEndpointLogShiftMajorant w N)
        atTop
        (𝓝 (0 : ℝ)) :=
    Complex.binetAbelPlanaEndpointLogShiftMajorant_tendsto_zero w
  have hnorm :
      Tendsto
        (fun N : ℕ =>
          ‖Complex.binetAbelPlanaEndpointLogShiftError w (N + 1)‖)
        atTop
        (𝓝 (0 : ℝ)) :=
    squeeze_zero'
      (Eventually.of_forall
        (fun N : ℕ =>
          norm_nonneg
            (Complex.binetAbelPlanaEndpointLogShiftError w (N + 1))))
      hbound
      hmajorant
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

/-- Endpoint-Stirling remainder convergence assembled from the factorial
Stirling convergence and the endpoint logarithmic-shift convergence. -/
theorem Complex.binetAbelPlanaFiniteEndpointStirlingRemainder_tendsto_zero_from_components
    {w : ℂ}
    (hfactorial :
      Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaFactorialStirlingError (N + 1))
        atTop
        (𝓝 (0 : ℂ)))
    (hshift :
      Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaEndpointLogShiftError w (N + 1))
        atTop
        (𝓝 (0 : ℂ))) :
    Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteEndpointStirlingRemainder N w)
      atTop
      (𝓝 (0 : ℂ)) := by
  have hsum :
      Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaFactorialStirlingError (N + 1) +
            Complex.binetAbelPlanaEndpointLogShiftError w (N + 1))
        atTop
        (𝓝 ((0 : ℂ) + 0)) :=
    hfactorial.add hshift
  have heq :
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteEndpointStirlingRemainder N w) =
      (fun N : ℕ =>
        Complex.binetAbelPlanaFactorialStirlingError (N + 1) +
          Complex.binetAbelPlanaEndpointLogShiftError w (N + 1)) := by
    funext N
    exact
      Complex.binetAbelPlanaFiniteEndpointStirlingRemainder_eq_factorial_add_shift
        w N
  exact (zero_add (0 : ℂ)).symm ▸ (heq ▸ hsum)

/-- Endpoint logarithmic Stirling remainder for the finite Abel-Plana main
term.

This is the classical branch-compatible finite endpoint estimate: after the
Euler-product endpoint terms are put in the principal-log normalization used
by `binetLogGammaMainTerm`, their difference from the limiting Binet main term
vanishes.  See the standard Binet derivation in Whittaker-Watson, Ch. XII, or
DLMF §5.11.3. -/
theorem Complex.binetAbelPlanaFiniteEndpointStirlingRemainder_tendsto_zero_owner
    {w : ℂ}
    (hw : 0 < w.re) :
    Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteEndpointStirlingRemainder N w)
      atTop
      (𝓝 (0 : ℂ)) := by
  have hfactorial :
      Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaFactorialStirlingError (N + 1))
        atTop
        (𝓝 (0 : ℂ)) :=
    Complex.binetAbelPlanaFactorialStirlingError_tendsto_zero_owner
  have hshift :
      Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaEndpointLogShiftError w (N + 1))
        atTop
        (𝓝 (0 : ℂ)) :=
    Complex.binetAbelPlanaEndpointLogShiftError_tendsto_zero_owner hw
  exact
    Complex.binetAbelPlanaFiniteEndpointStirlingRemainder_tendsto_zero_from_components
      hfactorial hshift

/-- Algebraic assembly of finite-main-term convergence from the endpoint
Stirling remainder estimate. -/
theorem Complex.binetAbelPlanaFiniteMainTerm_tendsto_binetMainTerm_of_endpointStirlingRemainder
    {w : ℂ}
    (hendpoint :
      Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaFiniteEndpointStirlingRemainder N w)
        atTop
        (𝓝 (0 : ℂ))) :
    Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteMainTerm N w)
      atTop
      (𝓝 (Complex.binetLogGammaMainTerm w)) := by
  have hsum :
      Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaFiniteEndpointStirlingRemainder N w +
            Complex.binetLogGammaMainTerm w)
        atTop
        (𝓝 (0 + Complex.binetLogGammaMainTerm w)) :=
    hendpoint.add tendsto_const_nhds
  have hfinite_eq :
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteEndpointStirlingRemainder N w +
          Complex.binetLogGammaMainTerm w) =
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteMainTerm N w) := by
    funext N
    calc
      Complex.binetAbelPlanaFiniteEndpointStirlingRemainder N w +
          Complex.binetLogGammaMainTerm w
          =
          (Complex.binetAbelPlanaFiniteMainTerm N w -
              Complex.binetLogGammaMainTerm w) +
            Complex.binetLogGammaMainTerm w := by
        rfl
      _ = Complex.binetAbelPlanaFiniteMainTerm N w := by
        exact sub_add_cancel
          (Complex.binetAbelPlanaFiniteMainTerm N w)
          (Complex.binetLogGammaMainTerm w)
  have htarget :
      (0 : ℂ) + Complex.binetLogGammaMainTerm w =
        Complex.binetLogGammaMainTerm w :=
    zero_add (Complex.binetLogGammaMainTerm w)
  exact htarget ▸ (hfinite_eq ▸ hsum)

/-- Finite endpoint/Stirling asymptotic in the concrete finite-main-term
form. -/
theorem Complex.binetAbelPlanaFiniteMainTerm_tendsto_binetMainTerm_from_endpointStirling_owner
    {w : ℂ}
    (hw : 0 < w.re) :
    Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteMainTerm N w)
      atTop
      (𝓝 (Complex.binetLogGammaMainTerm w)) := by
  exact
    Complex.binetAbelPlanaFiniteMainTerm_tendsto_binetMainTerm_of_endpointStirlingRemainder
      (Complex.binetAbelPlanaFiniteEndpointStirlingRemainder_tendsto_zero_owner
        hw)

/-- Explicit finite-contour majorant for the upper Abel-Plana endpoint
residual.

The standard finite-contour proof bounds the upper vertical residual by the
endpoint scale `O(1 / N)`.  The exponential factor belongs to the integration
kernel in the vertical variable, not to the endpoint parameter `N` itself. -/
noncomputable def Complex.binetAbelPlanaFiniteUpperContourResidualMajorant
    (w : ℂ)
    (N : ℕ) : ℝ :=
  8 * (1 + ‖w‖) ^ 2 *
    (1 + |Complex.binetAbelPlanaVerticalKernelMass|) / (N + 1 : ℝ)

/-- Explicit majorant for the lower Abel-Plana tail omitted by truncating the
lower boundary at height `N`.

This is intentionally a tail integral of the already-owned Binet vertical
kernel majorant.  The lower contour tail has exponential decay, but the
owner-level API available here proves decay through integrability of the
kernel, not through the upper-endpoint `O(1 / (N + 1))` scale used for the
finite upper residual. -/
noncomputable def Complex.binetAbelPlanaFiniteLowerContourTailMajorant
    (w : ℂ)
    (N : ℕ) : ℝ :=
  2 * ∫ t : ℝ in Set.Ioi (N : ℝ),
    Complex.binetAbelPlanaVerticalKernelMajorant t

/-- Explicit finite-contour majorant for the honest total Abel-Plana
remainder. -/
noncomputable def Complex.binetAbelPlanaFiniteContourRemainderMajorant
    (w : ℂ)
    (N : ℕ) : ℝ :=
  Complex.binetAbelPlanaFiniteLowerContourTailMajorant w N +
    Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N

/-- The upper endpoint-residual majorant tends to zero. -/
theorem Complex.binetAbelPlanaFiniteUpperContourResidualMajorant_tendsto_zero
    (w : ℂ) :
    Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N)
      atTop
      (𝓝 (0 : ℝ)) := by
  have hconst :
      Tendsto
        (fun _N : ℕ =>
          8 * (1 + ‖w‖) ^ 2 *
            (1 + |Complex.binetAbelPlanaVerticalKernelMass|))
        atTop
        (𝓝 (8 * (1 + ‖w‖) ^ 2 *
          (1 + |Complex.binetAbelPlanaVerticalKernelMass|))) :=
    tendsto_const_nhds
  have hinv :
      Tendsto
        (fun N : ℕ => ((N + 1 : ℝ))⁻¹)
        atTop
        (𝓝 (0 : ℝ)) := by
    have hshift :
        Tendsto
          (fun N : ℕ => (N + 1 : ℝ))
          atTop
          atTop := by
      exact
        tendsto_atTop_add_const_right atTop (1 : ℝ)
          tendsto_natCast_atTop_atTop
    exact tendsto_inv_atTop_zero.comp hshift
  have hmul :
      Tendsto
        (fun N : ℕ =>
          8 * (1 + ‖w‖) ^ 2 *
            (1 + |Complex.binetAbelPlanaVerticalKernelMass|) *
              ((N + 1 : ℝ))⁻¹)
        atTop
        (𝓝 (8 * (1 + ‖w‖) ^ 2 *
          (1 + |Complex.binetAbelPlanaVerticalKernelMass|) * 0)) :=
    hconst.mul hinv
  have heq :
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N) =
      (fun N : ℕ =>
        8 * (1 + ‖w‖) ^ 2 *
          (1 + |Complex.binetAbelPlanaVerticalKernelMass|) *
            ((N + 1 : ℝ))⁻¹) := by
    funext N
    dsimp [Complex.binetAbelPlanaFiniteUpperContourResidualMajorant]
    exact div_eq_mul_inv
      (8 * (1 + ‖w‖) ^ 2 *
        (1 + |Complex.binetAbelPlanaVerticalKernelMass|))
      (N + 1 : ℝ)
  exact
    (mul_zero (8 * (1 + ‖w‖) ^ 2 *
      (1 + |Complex.binetAbelPlanaVerticalKernelMass|))).symm ▸
      (heq ▸ hmul)

/-- The lower-tail majorant tends to zero. -/
theorem Complex.binetAbelPlanaFiniteLowerContourTailMajorant_tendsto_zero
    (w : ℂ) :
    Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteLowerContourTailMajorant w N)
      atTop
      (𝓝 (0 : ℝ)) := by
  let K : ℝ → ℝ := fun t : ℝ =>
    Complex.binetAbelPlanaVerticalKernelMajorant t
  have htail :
      Tendsto
        (fun N : ℕ =>
          ∫ t : ℝ in Set.Ioi (N : ℝ), K t)
        atTop
        (𝓝 (∫ t : ℝ in ⋂ N : ℕ, Set.Ioi (N : ℝ), K t)) := by
    refine tendsto_setIntegral_of_antitone ?_ ?_ ?_
    · intro N
      exact measurableSet_Ioi
    · intro N M hNM
      exact Set.Ioi_subset_Ioi (Nat.cast_le.mpr hNM)
    · exact
        ⟨0,
          Complex.binetAbelPlanaVerticalKernelMajorant_integrableOn⟩
  have hInter :
      (⋂ N : ℕ, Set.Ioi (N : ℝ)) = (∅ : Set ℝ) := by
    ext t
    constructor
    · intro ht
      rcases exists_nat_gt t with ⟨N, hN⟩
      exact False.elim ((lt_asymm hN) (ht N))
    · intro ht
      exact False.elim ht
  have htail_zero :
      Tendsto
        (fun N : ℕ =>
          ∫ t : ℝ in Set.Ioi (N : ℝ), K t)
        atTop
        (𝓝 (0 : ℝ)) := by
    exact hInter ▸ htail
  have hscale :
      Tendsto
        (fun N : ℕ =>
          2 * ∫ t : ℝ in Set.Ioi (N : ℝ), K t)
        atTop
        (𝓝 ((2 : ℝ) * 0)) :=
    tendsto_const_nhds.mul htail_zero
  have heq :
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteLowerContourTailMajorant w N) =
      (fun N : ℕ =>
        2 * ∫ t : ℝ in Set.Ioi (N : ℝ), K t) := by
    funext N
    rfl
  exact (mul_zero (2 : ℝ)).symm ▸ (heq ▸ hscale)

/-- The finite-contour majorant tends to zero. -/
theorem Complex.binetAbelPlanaFiniteContourRemainderMajorant_tendsto_zero
    (w : ℂ) :
    Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteContourRemainderMajorant w N)
      atTop
      (𝓝 (0 : ℝ)) := by
  have hlower :
      Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaFiniteLowerContourTailMajorant w N)
        atTop
        (𝓝 (0 : ℝ)) :=
    Complex.binetAbelPlanaFiniteLowerContourTailMajorant_tendsto_zero w
  have hupper :
      Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N)
        atTop
        (𝓝 (0 : ℝ)) :=
    Complex.binetAbelPlanaFiniteUpperContourResidualMajorant_tendsto_zero w
  have hsum :
      Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaFiniteLowerContourTailMajorant w N +
            Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N)
        atTop
        (𝓝 ((0 : ℝ) + 0)) :=
    hlower.add hupper
  have heq :
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteContourRemainderMajorant w N) =
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteLowerContourTailMajorant w N +
          Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N) := by
    funext N
    rfl
  exact (zero_add (0 : ℝ)).symm ▸ (heq ▸ hsum)

/-- Exact finite Abel-Plana summation formula for the logarithmic summand. -/
theorem Complex.binetAbelPlana_logGammaFiniteApproximation_eq_finiteMain_add_boundary_add_contourRemainder_owner
    {w : ℂ}
    (hw : 0 < w.re) :
    ∀ N : ℕ,
      Complex.binetAbelPlanaLogGammaFiniteApproximation N w =
        Complex.binetAbelPlanaFiniteMainTerm N w +
          Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
            Complex.binetAbelPlanaFiniteContourRemainder N w := by
  exact
    Complex.binetAbelPlana_logGammaFiniteApproximation_eq_finiteMain_add_boundary_add_contourRemainder_core
      hw

/-- Exact finite Abel-Plana residual identity for the logarithmic summand.

This is the finite contour theorem: after separating the finite main term and
the lower Abel-Plana boundary correction, the remaining error is exactly the
total contour remainder: lower truncation tail plus upper vertical residual. -/
theorem Complex.binetAbelPlanaFiniteRemainderError_eq_contourRemainder_owner
    {w : ℂ}
    (hw : 0 < w.re) :
    ∀ N : ℕ,
      Complex.binetAbelPlanaFiniteRemainderError N w =
        Complex.binetAbelPlanaFiniteContourRemainder N w := by
  intro N
  have hfinite :
      Complex.binetAbelPlanaLogGammaFiniteApproximation N w =
        Complex.binetAbelPlanaFiniteMainTerm N w +
          Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
            Complex.binetAbelPlanaFiniteContourRemainder N w :=
    Complex.binetAbelPlana_logGammaFiniteApproximation_eq_finiteMain_add_boundary_add_contourRemainder_owner
      hw N
  dsimp [Complex.binetAbelPlanaFiniteRemainderError]
  calc
    Complex.binetAbelPlanaLogGammaFiniteApproximation N w -
        (Complex.binetAbelPlanaFiniteMainTerm N w +
          Complex.binetAbelPlanaFiniteBoundaryCorrection N w)
        =
        (Complex.binetAbelPlanaFiniteMainTerm N w +
          Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
            Complex.binetAbelPlanaFiniteContourRemainder N w) -
          (Complex.binetAbelPlanaFiniteMainTerm N w +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N w) := by
          exact congrArg
            (fun z : ℂ =>
              z - (Complex.binetAbelPlanaFiniteMainTerm N w +
                Complex.binetAbelPlanaFiniteBoundaryCorrection N w))
            hfinite
    _ = Complex.binetAbelPlanaFiniteContourRemainder N w := by
          exact Complex.add_add_sub_add_eq_right
            (Complex.binetAbelPlanaFiniteMainTerm N w)
            (Complex.binetAbelPlanaFiniteBoundaryCorrection N w)
            (Complex.binetAbelPlanaFiniteContourRemainder N w)

/-- The real coordinate is bounded by the complex norm. -/
theorem Complex.abs_re_le_norm_owner
    (z : ℂ) :
    |z.re| ≤ ‖z‖ := by
  have habs : |z.re| ≤ Complex.abs z :=
    Complex.abs_re_le_abs z
  have hnorm : ‖z‖ = Complex.abs z :=
    Complex.norm_eq_abs z
  exact Eq.subst
    (motive := fun r : ℝ => |z.re| ≤ r)
    hnorm.symm
    habs

/-- The real part of the upper endpoint line is the endpoint real part. -/
theorem Complex.binetAbelPlana_upperEndpointLine_re
    (w : ℂ)
    (N : ℕ)
    (s : ℝ) :
    (w + (N + 1 : ℂ) + (s : ℂ) * Complex.I).re =
      w.re + (N + 1 : ℝ) := by
  calc
    (w + (N + 1 : ℂ) + (s : ℂ) * Complex.I).re
        =
        (w + (N + 1 : ℂ)).re + ((s : ℂ) * Complex.I).re := by
          exact Complex.add_re (w + (N + 1 : ℂ)) ((s : ℂ) * Complex.I)
    _ = w.re + (N + 1 : ℝ) + ((s : ℂ) * Complex.I).re := by
          exact congrArg
            (fun r : ℝ => r + ((s : ℂ) * Complex.I).re)
            (Complex.add_re w (N + 1 : ℂ))
    _ = w.re + (N + 1 : ℝ) := by
          exact Real.add_right_zero_after_eq_zero
            w.re
            (N + 1 : ℝ)
            (((s : ℂ) * Complex.I).re)
            (Complex.real_cast_mul_I_re s)

/-- The upper endpoint line has norm bounded below by its positive real
coordinate. -/
theorem Complex.upperEndpointLine_endpoint_re_le_norm
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (s : ℝ) :
    w.re + (N + 1 : ℝ) ≤
      ‖w + (N + 1 : ℂ) + (s : ℂ) * Complex.I‖ := by
  let z : ℂ := w + (N + 1 : ℂ) + (s : ℂ) * Complex.I
  have hN_pos : 0 < (N + 1 : ℝ) := by
    exact Nat.cast_pos.mpr (Nat.succ_pos N)
  have hre_pos : 0 < z.re := by
    have hre :
        z.re = w.re + (N + 1 : ℝ) :=
      Complex.binetAbelPlana_upperEndpointLine_re w N s
    exact hre.symm ▸ add_pos hw hN_pos
  have h_re_abs : z.re = |z.re| :=
    (abs_of_pos hre_pos).symm
  calc
    w.re + (N + 1 : ℝ)
        = z.re := by
          exact
            (Complex.binetAbelPlana_upperEndpointLine_re w N s).symm
    _ = |z.re| :=
          h_re_abs
    _ ≤ ‖z‖ :=
          Complex.abs_re_le_norm_owner z

/-- The upper endpoint vertical line lies in the principal logarithm slit
plane. -/
theorem Complex.binetAbelPlanaUpperEndpointLine_mem_slitPlane
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (s : ℝ) :
    w + (N + 1 : ℂ) + (s : ℂ) * Complex.I ∈ Complex.slitPlane := by
  have hre_pos :
      0 < (w + (N + 1 : ℂ) + (s : ℂ) * Complex.I).re :=
    Complex.binetAbelPlanaUpperLogJumpSegmentDenominator_re_pos hw N s
  exact Or.inl hre_pos

/-- Real derivative of the principal logarithm along the upper endpoint
vertical line. -/
theorem Complex.hasDerivAt_binetAbelPlanaUpperEndpointLine_log
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (s : ℝ) :
    HasDerivAt
      (fun u : ℝ =>
        Complex.log (w + (N + 1 : ℂ) + (u : ℂ) * Complex.I))
      (Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s)
      s := by
  exact
    Complex.hasDerivAt_binetAbelPlanaUpperEndpointLine_log_shared
      hw N s

/-- The upper endpoint differential-log integrand is interval-integrable on
every finite segment. -/
theorem Complex.intervalIntegrable_binetAbelPlanaUpperLogJumpSegmentIntegrand
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (a b : ℝ) :
    IntervalIntegrable
      (fun s : ℝ =>
        Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s)
      volume
      a
      b := by
  exact
    Complex.intervalIntegrable_binetAbelPlanaUpperLogJumpSegmentIntegrand_shared
      hw N a b

/-- Fundamental theorem of calculus for the upper endpoint logarithmic line. -/
theorem Complex.integral_binetAbelPlanaUpperLogJumpSegmentIntegrand_eq_log_sub
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (a b : ℝ) :
    ∫ s : ℝ in a..b,
        Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s =
      Complex.log (w + (N + 1 : ℂ) + (b : ℂ) * Complex.I) -
        Complex.log (w + (N + 1 : ℂ) + (a : ℂ) * Complex.I) := by
  exact
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _hs =>
        Complex.hasDerivAt_binetAbelPlanaUpperEndpointLine_log hw N s)
      (Complex.intervalIntegrable_binetAbelPlanaUpperLogJumpSegmentIntegrand
        hw N a b)

/-- Differential-log segment estimate for the upper Abel-Plana logarithmic
jump. -/
theorem Complex.binetAbelPlanaFiniteUpperLogJump_eq_segmentIntegral_owner
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
      Complex.binetAbelPlanaFiniteUpperLogJump N w t =
        ∫ s : ℝ in (-t)..t,
          Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s := by
  filter_upwards with t
  have hftc :
      ∫ s : ℝ in (-t)..t,
          Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s =
        Complex.log (w + (N + 1 : ℂ) + (t : ℂ) * Complex.I) -
          Complex.log (w + (N + 1 : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) :=
    Complex.integral_binetAbelPlanaUpperLogJumpSegmentIntegrand_eq_log_sub
      hw N (-t) t
  calc
    Complex.binetAbelPlanaFiniteUpperLogJump N w t =
        Complex.log (w + (N + 1 : ℂ) + (t : ℂ) * Complex.I) -
          Complex.log (w + (N + 1 : ℂ) + (-(t : ℂ) * Complex.I)) := by
      rfl
    _ =
        Complex.log (w + (N + 1 : ℂ) + (t : ℂ) * Complex.I) -
          Complex.log (w + (N + 1 : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) := by
      exact congrArg
        (fun z : ℂ =>
          Complex.log (w + (N + 1 : ℂ) + (t : ℂ) * Complex.I) -
            Complex.log (w + (N + 1 : ℂ) + z))
        (Complex.ofReal_neg_mul_I t).symm
    _ =
        ∫ s : ℝ in (-t)..t,
          Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s :=
      hftc.symm

/-- Pointwise denominator estimate for the upper endpoint differential-log
segment integrand. -/
theorem Complex.norm_binetAbelPlanaUpperLogJumpSegmentIntegrand_le_endpoint_re_inv
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    ∀ s : ℝ,
      ‖Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s‖ ≤
        (w.re + (N + 1 : ℝ))⁻¹ := by
  intro s
  let z : ℂ := w + (N + 1 : ℂ) + (s : ℂ) * Complex.I
  have hN_pos : 0 < (N + 1 : ℝ) := by
    exact Nat.cast_pos.mpr (Nat.succ_pos N)
  have hendpoint_pos : 0 < w.re + (N + 1 : ℝ) :=
    add_pos hw hN_pos
  have hendpoint_le_norm :
      w.re + (N + 1 : ℝ) ≤ ‖z‖ :=
    Complex.upperEndpointLine_endpoint_re_le_norm hw N s
  have hinv_le :
      ‖z‖⁻¹ ≤ (w.re + (N + 1 : ℝ))⁻¹ :=
    calc
      ‖z‖⁻¹ = (1 : ℝ) / ‖z‖ := by
        exact inv_eq_one_div ‖z‖
      _ ≤ (1 : ℝ) / (w.re + (N + 1 : ℝ)) :=
        one_div_le_one_div_of_le hendpoint_pos hendpoint_le_norm
      _ = (w.re + (N + 1 : ℝ))⁻¹ := by
        exact (inv_eq_one_div (w.re + (N + 1 : ℝ))).symm
  calc
    ‖Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s‖
        = ‖Complex.I / z‖ := by
          rfl
    _ = ‖Complex.I‖ / ‖z‖ := by
          exact norm_div Complex.I z
    _ = ‖z‖⁻¹ := by
          exact Complex.norm_I_div_eq_inv_norm z
    _ ≤ (w.re + (N + 1 : ℝ))⁻¹ :=
          hinv_le

/-- Interval-length integration of the pointwise segment-integrand bound. -/
theorem Complex.norm_binetAbelPlanaUpperLogJumpSegmentIntegral_le_length_mul_endpoint_re_inv
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
      ‖∫ s : ℝ in (-t)..t,
          Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s‖ ≤
        (2 * t) * (w.re + (N + 1 : ℝ))⁻¹ := by
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
  have ht_nonneg : 0 ≤ t := le_of_lt ht
  have hpoint :
      ∀ s : ℝ,
        ‖Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s‖ ≤
          (w.re + (N + 1 : ℝ))⁻¹ :=
    Complex.norm_binetAbelPlanaUpperLogJumpSegmentIntegrand_le_endpoint_re_inv
      hw N
  have hinterval :
      ‖∫ s : ℝ in (-t)..t,
          Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s‖ ≤
        (w.re + (N + 1 : ℝ))⁻¹ * |t - (-t)| :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (fun s hs => hpoint s)
  have habs : |t - (-t)| = 2 * t := by
    calc
      |t - (-t)| = |2 * t| := by
        exact congrArg abs (Real.sub_neg_eq_two_mul t)
      _ = 2 * t := abs_of_nonneg (mul_nonneg zero_le_two ht_nonneg)
  calc
    ‖∫ s : ℝ in (-t)..t,
        Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s‖
        ≤ (w.re + (N + 1 : ℝ))⁻¹ * |t - (-t)| := hinterval
    _ = (w.re + (N + 1 : ℝ))⁻¹ * (2 * t) := by
          exact congrArg
            (fun x : ℝ => (w.re + (N + 1 : ℝ))⁻¹ * x)
            habs
    _ = (2 * t) * (w.re + (N + 1 : ℝ))⁻¹ := by
          exact mul_comm (w.re + (N + 1 : ℝ))⁻¹ (2 * t)

/-- Norm bound for the differential-log segment integral. -/
theorem Complex.norm_binetAbelPlanaUpperLogJumpSegmentIntegral_le_two_mul_t_div_endpoint_re
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
      ‖∫ s : ℝ in (-t)..t,
          Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s‖ ≤
        (2 * t) / (w.re + (N + 1 : ℝ)) := by
  have hlength :
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
        ‖∫ s : ℝ in (-t)..t,
            Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s‖ ≤
          (2 * t) * (w.re + (N + 1 : ℝ))⁻¹ :=
    Complex.norm_binetAbelPlanaUpperLogJumpSegmentIntegral_le_length_mul_endpoint_re_inv
      hw N
  filter_upwards [hlength] with t ht
  change ‖∫ s : ℝ in (-t)..t,
      Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s‖ ≤
    (2 * t) * (w.re + (N + 1 : ℝ))⁻¹
  exact ht

/-- Differential-log segment estimate for the upper Abel-Plana logarithmic
jump. -/
theorem Complex.norm_binetAbelPlanaFiniteUpperLogJump_le_two_mul_t_div_endpoint_re
    {w : ℂ}
    (hw : 0 < w.re) :
    ∀ N : ℕ,
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
        ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t‖ ≤
          (2 * t) / (w.re + (N + 1 : ℝ)) := by
  intro N
  have hidentity :
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
        Complex.binetAbelPlanaFiniteUpperLogJump N w t =
          ∫ s : ℝ in (-t)..t,
            Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s :=
    Complex.binetAbelPlanaFiniteUpperLogJump_eq_segmentIntegral_owner hw N
  have hbound :
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
        ‖∫ s : ℝ in (-t)..t,
            Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s‖ ≤
          (2 * t) / (w.re + (N + 1 : ℝ)) :=
    Complex.norm_binetAbelPlanaUpperLogJumpSegmentIntegral_le_two_mul_t_div_endpoint_re
      hw N
  filter_upwards [hidentity, hbound] with t ht_eq ht_bound
  exact ht_eq ▸ ht_bound

/-- Endpoint real-part comparison for the upper Abel-Plana logarithmic jump. -/
theorem Complex.two_mul_t_div_upperEndpoint_re_le_public_logJump_majorant
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    ∀ t : ℝ,
      t ∈ Set.Ioi (0 : ℝ) →
        (2 * t) / (w.re + (N + 1 : ℝ)) ≤
          (4 * (1 + ‖w‖) / (N + 1 : ℝ)) * t := by
  intro t ht
  have hN_pos : 0 < (N + 1 : ℝ) := by
    exact Nat.cast_pos.mpr (Nat.succ_pos N)
  have hendpoint_pos : 0 < w.re + (N + 1 : ℝ) :=
    add_pos hw hN_pos
  have hone_le : 1 ≤ 1 + ‖w‖ :=
    le_add_of_nonneg_right (norm_nonneg w)
  have hbase :
      (2 : ℝ) / (w.re + (N + 1 : ℝ)) ≤
        4 * (1 + ‖w‖) / (N + 1 : ℝ) := by
    have hden_le :
        (N + 1 : ℝ) ≤ w.re + (N + 1 : ℝ) :=
      le_add_of_nonneg_left hw.le
    have hrecip :
        (1 : ℝ) / (w.re + (N + 1 : ℝ)) ≤
          1 / (N + 1 : ℝ) := by
      exact one_div_le_one_div_of_le hN_pos hden_le
    have htwo :
        (2 : ℝ) / (w.re + (N + 1 : ℝ)) ≤
          2 / (N + 1 : ℝ) := by
      exact mul_le_mul_of_nonneg_left hrecip zero_le_two
    have htwo_le_four :
        (2 : ℝ) / (N + 1 : ℝ) ≤
          4 * (1 + ‖w‖) / (N + 1 : ℝ) := by
      have hnum : (2 : ℝ) ≤ 4 * (1 + ‖w‖) := by
        exact Real.two_le_four_mul_of_one_le hone_le
      exact div_le_div_of_nonneg_right hnum hN_pos.le
    exact htwo.trans htwo_le_four
  calc
    (2 * t) / (w.re + (N + 1 : ℝ))
        = ((2 : ℝ) / (w.re + (N + 1 : ℝ))) * t := by
          exact Real.two_mul_div_eq_div_mul t (w.re + (N + 1 : ℝ))
    _ ≤ (4 * (1 + ‖w‖) / (N + 1 : ℝ)) * t := by
          exact mul_le_mul_of_nonneg_right hbase ht.le

/-- Upper-endpoint logarithmic jump bound along the finite Abel-Plana
vertical contour. -/
theorem Complex.norm_binetAbelPlanaFiniteUpperLogJump_le_endpoint_kernel
    {w : ℂ}
    (hw : 0 < w.re) :
    ∀ᶠ N : ℕ in atTop,
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
        ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t‖ ≤
          (4 * (1 + ‖w‖) / (N + 1 : ℝ)) * t := by
  have hsegment :
      ∀ N : ℕ,
        ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
          ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t‖ ≤
            (2 * t) / (w.re + (N + 1 : ℝ)) :=
    Complex.norm_binetAbelPlanaFiniteUpperLogJump_le_two_mul_t_div_endpoint_re
      hw
  filter_upwards with N
  filter_upwards [hsegment N, ae_restrict_mem measurableSet_Ioi] with t ht_segment ht_mem
  exact
    ht_segment.trans
      (Complex.two_mul_t_div_upperEndpoint_re_le_public_logJump_majorant
        hw N t ht_mem)

/-- Pointwise majorization of the upper-contour residual integrand. -/
theorem Complex.norm_binetAbelPlanaFiniteUpperContourResidual_integrand_le_majorant
    {w : ℂ}
    (hw : 0 < w.re) :
    ∀ᶠ N : ℕ in atTop,
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
        ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖ ≤
          (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
            Complex.binetAbelPlanaVerticalKernelMajorant t := by
  have hjump :
      ∀ᶠ N : ℕ in atTop,
        ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
          ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t‖ ≤
            (4 * (1 + ‖w‖) / (N + 1 : ℝ)) * t :=
    Complex.norm_binetAbelPlanaFiniteUpperLogJump_le_endpoint_kernel hw
  filter_upwards [hjump] with N hN
  filter_upwards [hN, ae_restrict_mem measurableSet_Ioi] with t ht_jump ht_mem
  have ht_pos : 0 < t := ht_mem
  have hden_pos :
      0 < Real.exp ((2 : ℝ) * Real.pi * t) - 1 :=
    Real.binetSecondFormula_exp_denominator_pos ht_pos
  dsimp [Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand]
  calc
      ‖Complex.I *
        (Complex.binetAbelPlanaFiniteUpperLogJump N w t /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))‖
        =
        ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t‖ /
          (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
          calc
            ‖Complex.I *
                (Complex.binetAbelPlanaFiniteUpperLogJump N w t /
                  (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))‖
                = ‖Complex.I‖ *
                    ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t /
                      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ := by
                  exact norm_mul _ _
            _ = ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t /
                  (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ := by
                  exact (one_mul
                    ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t /
                      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖)
                    ▸ congrArg
                      (fun r : ℝ =>
                        r *
                          ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t /
                            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖)
                      Complex.norm_I
            _ = ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t‖ /
                  ‖Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1‖ := by
                  exact norm_div _ _
            _ = ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t‖ /
                  ‖Real.exp ((2 : ℝ) * Real.pi * t) - 1‖ := by
                  exact congrArg (fun x : ℝ => ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t‖ / x)
                    (Complex.binetSecondFormula_exp_denominator_norm_eq t)
            _ = ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t‖ /
                  (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
                  exact congrArg
                    (fun x : ℝ => ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t‖ / x)
                    (Real.binetSecondFormula_exp_denominator_norm_eq ht_pos)
    _ ≤
        ((4 * (1 + ‖w‖) / (N + 1 : ℝ)) * t) /
          (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
          exact div_le_div_of_nonneg_right ht_jump hden_pos.le
    _ =
        (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
          Complex.binetAbelPlanaVerticalKernelMajorant t := by
          dsimp [Complex.binetAbelPlanaVerticalKernelMajorant]
          exact Real.mul_mul_div_eq_mul_div
            (4 * (1 + ‖w‖) / (N + 1 : ℝ))
            t
            (Real.exp (2 * Real.pi * t) - 1)

/-- Integral transport from a pointwise upper-contour integrand majorant to
the vertical-kernel mass. -/
theorem Complex.integral_norm_binetAbelPlanaFiniteUpperContourResidualIntegrand_le_kernelMass
    {w : ℂ}
    {N : ℕ}
    (hmajorant :
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
        ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖ ≤
          (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
            Complex.binetAbelPlanaVerticalKernelMajorant t) :
    ∫ t : ℝ in Set.Ioi (0 : ℝ),
        ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖ ≤
      (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
        Complex.binetAbelPlanaVerticalKernelMass := by
  have hcoef_nonneg :
      0 ≤ 4 * (1 + ‖w‖) / (N + 1 : ℝ) := by
    have hN_pos : 0 < (N + 1 : ℝ) := by
      exact Nat.cast_pos.mpr (Nat.succ_pos N)
    have hfour_nonneg : (0 : ℝ) ≤ 4 := by
      exact mul_nonneg zero_le_two zero_le_two
    exact div_nonneg
      (mul_nonneg hfour_nonneg
        (le_trans zero_le_one
          (le_add_of_nonneg_right (norm_nonneg w))))
      hN_pos.le
  have hmajorant_integrable :
      IntegrableOn
        (fun t : ℝ =>
          (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
            Complex.binetAbelPlanaVerticalKernelMajorant t)
        (Set.Ioi (0 : ℝ)) :=
    Complex.binetAbelPlanaVerticalKernelMajorant_integrableOn.const_mul
      (4 * (1 + ‖w‖) / (N + 1 : ℝ))
  have hintegrable :
      IntegrableOn
        (fun t : ℝ =>
          ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖)
        (Set.Ioi (0 : ℝ)) :=
    Complex.integrableOn_norm_binetAbelPlanaFiniteUpperContourResidualIntegrand_of_majorant
      (w := w)
      (N := N)
      hmajorant
  have hmono :
      ∫ t : ℝ in Set.Ioi (0 : ℝ),
          ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖ ≤
        ∫ t : ℝ in Set.Ioi (0 : ℝ),
          (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
            Complex.binetAbelPlanaVerticalKernelMajorant t :=
    setIntegral_mono_ae_restrict
      hintegrable
      hmajorant_integrable
      hmajorant
  have hconst :
      ∫ t : ℝ in Set.Ioi (0 : ℝ),
          (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
            Complex.binetAbelPlanaVerticalKernelMajorant t =
        (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
          Complex.binetAbelPlanaVerticalKernelMass := by
    dsimp [Complex.binetAbelPlanaVerticalKernelMass]
    exact integral_const_mul
  exact hmono.trans_eq hconst

/-- Fixed-index integral comparison for the upper-contour residual. -/
theorem Complex.norm_binetAbelPlanaFiniteUpperContourResidual_le_kernelMass_of_integrand_majorant
    {w : ℂ}
    {N : ℕ}
    (hmajorant :
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
        ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖ ≤
          (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
            Complex.binetAbelPlanaVerticalKernelMajorant t) :
    ‖Complex.binetAbelPlanaFiniteUpperContourResidual N w‖ ≤
      (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
        Complex.binetAbelPlanaVerticalKernelMass := by
  have hnorm_integral :
      ‖Complex.binetAbelPlanaFiniteUpperContourResidual N w‖ ≤
        ∫ t : ℝ in Set.Ioi (0 : ℝ),
          ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖ := by
    exact
      (Complex.binetAbelPlanaFiniteUpperContourResidual_eq_integral_integrand
        (N := N) (w := w)).trans_le
        (norm_integral_le_integral_norm _)
  have hkernel_integral :
      ∫ t : ℝ in Set.Ioi (0 : ℝ),
          ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖ ≤
        (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
          Complex.binetAbelPlanaVerticalKernelMass :=
    Complex.integral_norm_binetAbelPlanaFiniteUpperContourResidualIntegrand_le_kernelMass
      (w := w)
      (N := N)
      hmajorant
  exact hnorm_integral.trans hkernel_integral

/-- Integral-level upper-contour residual estimate in terms of the vertical
kernel mass. -/
theorem Complex.norm_binetAbelPlanaFiniteUpperContourResidual_le_kernelMass_owner
    {w : ℂ}
    (hw : 0 < w.re) :
    ∀ᶠ N : ℕ in atTop,
      ‖Complex.binetAbelPlanaFiniteUpperContourResidual N w‖ ≤
        (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
          Complex.binetAbelPlanaVerticalKernelMass := by
  have hpointwise :
      ∀ᶠ N : ℕ in atTop,
        ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
          ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖ ≤
            (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
              Complex.binetAbelPlanaVerticalKernelMajorant t :=
    Complex.norm_binetAbelPlanaFiniteUpperContourResidual_integrand_le_majorant
      hw
  filter_upwards [hpointwise] with N hN
  exact
    Complex.norm_binetAbelPlanaFiniteUpperContourResidual_le_kernelMass_of_integrand_majorant
      (w := w)
      (N := N)
      hN

/-- The kernel-mass bound is dominated by the upper-residual majorant. -/
theorem Complex.binetAbelPlanaFiniteUpperContourResidual_kernelMass_bound_le_majorant
    (w : ℂ)
    (N : ℕ) :
    (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
        Complex.binetAbelPlanaVerticalKernelMass ≤
      Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N := by
  have hden_pos : 0 < (N + 1 : ℝ) := by
    exact Nat.cast_pos.mpr (Nat.succ_pos N)
  have hone_le_scale : 1 ≤ 1 + ‖w‖ := by
    exact le_add_of_nonneg_right (norm_nonneg w)
  have hmass_le :
      Complex.binetAbelPlanaVerticalKernelMass ≤
        1 + |Complex.binetAbelPlanaVerticalKernelMass| := by
    exact
      (le_abs_self Complex.binetAbelPlanaVerticalKernelMass).trans
        (le_add_of_nonneg_left zero_le_one)
  have hcoef_nonneg :
      0 ≤ 4 * (1 + ‖w‖) / (N + 1 : ℝ) := by
    have hfour_nonneg : (0 : ℝ) ≤ 4 := by
      exact mul_nonneg zero_le_two zero_le_two
    exact div_nonneg
      (mul_nonneg hfour_nonneg
        (le_trans zero_le_one hone_le_scale))
      hden_pos.le
  have hcoef_le :
      4 * (1 + ‖w‖) ≤ 8 * (1 + ‖w‖) ^ 2 := by
    exact Real.four_mul_le_eight_mul_sq_of_one_le hone_le_scale
  have hscaled_mass :
      (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
          Complex.binetAbelPlanaVerticalKernelMass ≤
        (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
          (1 + |Complex.binetAbelPlanaVerticalKernelMass|) :=
    mul_le_mul_of_nonneg_left hmass_le hcoef_nonneg
  have hscaled_coef :
      (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
          (1 + |Complex.binetAbelPlanaVerticalKernelMass|) ≤
        (8 * (1 + ‖w‖) ^ 2 / (N + 1 : ℝ)) *
          (1 + |Complex.binetAbelPlanaVerticalKernelMass|) := by
    have hdiv :
        4 * (1 + ‖w‖) / (N + 1 : ℝ) ≤
          8 * (1 + ‖w‖) ^ 2 / (N + 1 : ℝ) :=
      div_le_div_of_nonneg_right hcoef_le hden_pos.le
    exact
      mul_le_mul_of_nonneg_right hdiv
        (add_nonneg zero_le_one (abs_nonneg _))
  exact
    hscaled_mass.trans
      (hscaled_coef.trans
        (by
          dsimp [Complex.binetAbelPlanaFiniteUpperContourResidualMajorant]
          exact mul_div_assoc
            (8 * (1 + ‖w‖) ^ 2)
            (1 + |Complex.binetAbelPlanaVerticalKernelMass|)
            (N + 1 : ℝ)))

/-- Owner upper-contour residual estimate in majorant form. -/
theorem Complex.norm_binetAbelPlanaFiniteUpperContourResidual_le_majorant_owner
    {w : ℂ}
    (hw : 0 < w.re) :
    ∀ᶠ N : ℕ in atTop,
      ‖Complex.binetAbelPlanaFiniteUpperContourResidual N w‖ ≤
        Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N := by
  have hkernel :
      ∀ᶠ N : ℕ in atTop,
        ‖Complex.binetAbelPlanaFiniteUpperContourResidual N w‖ ≤
          (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
            Complex.binetAbelPlanaVerticalKernelMass :=
    Complex.norm_binetAbelPlanaFiniteUpperContourResidual_le_kernelMass_owner
      hw
  filter_upwards [hkernel] with N hN
  exact
    hN.trans
      (Complex.binetAbelPlanaFiniteUpperContourResidual_kernelMass_bound_le_majorant
        w N)

/-- The lower finite Abel-Plana tail integrand equals twice the principal
Binet arctangent kernel on its positive vertical contour. -/
theorem Complex.binetAbelPlanaFiniteLowerContourTail_integrand_eq_two_arctanKernel
    {w : ℂ}
    (hw : 0 < w.re) :
    ∀ N : ℕ,
      ∀ᵐ t ∂volume.restrict (Set.Ioi (N : ℝ)),
        (-Complex.I) *
          ((Complex.log (w + (t : ℂ) * Complex.I) -
              Complex.log (w - (t : ℂ) * Complex.I)) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)) =
          2 *
            (Complex.arctan ((t : ℂ) / w) /
              (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)) := by
  intro N
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht_pos : 0 < t :=
    lt_of_le_of_lt (Nat.cast_nonneg N) ht
  exact
    Complex.binetAbelPlana_logJump_integrand_eq_two_arctanKernel
      hw ht_pos

/-- Pointwise lower-tail domination by twice the Binet vertical kernel
majorant. -/
theorem Complex.norm_binetAbelPlanaFiniteLowerContourTail_integrand_le_majorant
    {w : ℂ}
    (hw : 0 < w.re) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ N : ℕ in atTop,
          ∀ᵐ t ∂volume.restrict (Set.Ioi (N : ℝ)),
            ‖(-Complex.I) *
              ((Complex.log (w + (t : ℂ) * Complex.I) -
                  Complex.log (w - (t : ℂ) * Complex.I)) /
                (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))‖ ≤
              C * Complex.binetAbelPlanaVerticalKernelMajorant t := by
  rcases
      Complex.binetSecondFormula_arctanKernel_tail_norm_le_majorant_owner
        hw with
    ⟨C, hC_nonneg, hC⟩
  refine ⟨2 * C, mul_nonneg zero_le_two hC_nonneg, ?_⟩
  rcases exists_nat_gt (‖w‖ / 2) with ⟨N₀, hN₀⟩
  filter_upwards [eventually_ge_atTop N₀] with N hN
  filter_upwards
    [Complex.binetAbelPlanaFiniteLowerContourTail_integrand_eq_two_arctanKernel
      hw N,
      ae_restrict_mem measurableSet_Ioi] with t ht_eq ht_mem
  have hN₀_le_N : (N₀ : ℝ) ≤ (N : ℝ) := by
    exact Nat.cast_le.mpr hN
  have ht_tail : t ∈ Set.Ioi (‖w‖ / 2) := by
    exact lt_of_lt_of_le hN₀ (le_trans hN₀_le_N (le_of_lt ht_mem))
  have hkernel :
      ‖Complex.arctan ((t : ℂ) / w) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ ≤
        C * Complex.binetAbelPlanaVerticalKernelMajorant t :=
    hC t ht_tail
  have hmajorant_nonneg :
      0 ≤ Complex.binetAbelPlanaVerticalKernelMajorant t :=
    Complex.binetAbelPlanaVerticalKernelMajorant_nonneg_on_Ioi
      t
      (lt_of_lt_of_le hN₀
        (le_trans hN₀_le_N (le_of_lt ht_mem)))
  calc
    ‖(-Complex.I) *
        ((Complex.log (w + (t : ℂ) * Complex.I) -
            Complex.log (w - (t : ℂ) * Complex.I)) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))‖
        =
        ‖2 *
          (Complex.arctan ((t : ℂ) / w) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))‖ := by
          exact congrArg norm ht_eq
    _ =
        2 *
          ‖Complex.arctan ((t : ℂ) / w) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ := by
          have htwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by
            exact Complex.norm_two_natCast
          calc
            ‖2 *
              (Complex.arctan ((t : ℂ) / w) /
                (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))‖
                =
                ‖(2 : ℂ)‖ *
                  ‖Complex.arctan ((t : ℂ) / w) /
                    (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ := by
                  exact norm_mul _ _
            _ =
                2 *
                  ‖Complex.arctan ((t : ℂ) / w) /
                    (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ := by
                  exact congrArg
                    (fun x : ℝ =>
                      x *
                        ‖Complex.arctan ((t : ℂ) / w) /
                          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖)
                    htwo
    _ ≤ 2 * (C * Complex.binetAbelPlanaVerticalKernelMajorant t) := by
          exact mul_le_mul_of_nonneg_left hkernel zero_le_two
    _ = (2 * C) * Complex.binetAbelPlanaVerticalKernelMajorant t := by
          exact Real.two_mul_assoc C
            (Complex.binetAbelPlanaVerticalKernelMajorant t)

/-- The lower finite Abel-Plana tail positive vertical line is measurable. -/
theorem Complex.measurable_binetAbelPlanaFiniteLowerContourTail_plusLine
    (w : ℂ) :
    Measurable
      (fun t : ℝ => w + (t : ℂ) * Complex.I) := by
  exact
    measurable_const.add
      ((Complex.measurable_ofReal.comp measurable_id).mul measurable_const)

/-- The lower finite Abel-Plana tail negative vertical line is measurable. -/
theorem Complex.measurable_binetAbelPlanaFiniteLowerContourTail_minusLine
    (w : ℂ) :
    Measurable
      (fun t : ℝ => w - (t : ℂ) * Complex.I) := by
  exact
    measurable_const.sub
      ((Complex.measurable_ofReal.comp measurable_id).mul measurable_const)

/-- The lower finite Abel-Plana tail logarithmic jump is measurable. -/
theorem Complex.measurable_binetAbelPlanaFiniteLowerContourTail_logJump
    (w : ℂ) :
    Measurable
      (fun t : ℝ =>
        Complex.log (w + (t : ℂ) * Complex.I) -
          Complex.log (w - (t : ℂ) * Complex.I)) := by
  exact
    (Complex.measurable_binetAbelPlanaFiniteLowerContourTail_plusLine w).clog.sub
      (Complex.measurable_binetAbelPlanaFiniteLowerContourTail_minusLine w).clog

/-- The lower finite Abel-Plana tail exponential denominator is measurable. -/
theorem Complex.measurable_binetAbelPlanaFiniteLowerContourTail_denominator :
    Measurable
      (fun t : ℝ =>
        Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) :=
  Complex.binetSecondFormula_exp_denominator_measurable

/-- The lower finite Abel-Plana tail integrand is measurable. -/
theorem Complex.measurable_binetAbelPlanaFiniteLowerContourTail_integrand
    (w : ℂ) :
    Measurable
      (fun t : ℝ =>
        (-Complex.I) *
          ((Complex.log (w + (t : ℂ) * Complex.I) -
              Complex.log (w - (t : ℂ) * Complex.I)) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))) := by
  exact
    measurable_const.mul
      ((Complex.measurable_binetAbelPlanaFiniteLowerContourTail_logJump w).div
        Complex.measurable_binetAbelPlanaFiniteLowerContourTail_denominator)

/-- The norm of the lower finite Abel-Plana tail integrand is measurable. -/
theorem Complex.measurable_norm_binetAbelPlanaFiniteLowerContourTail_integrand
    (w : ℂ) :
    Measurable
      (fun t : ℝ =>
        ‖(-Complex.I) *
          ((Complex.log (w + (t : ℂ) * Complex.I) -
              Complex.log (w - (t : ℂ) * Complex.I)) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))‖) := by
  exact
    (Complex.measurable_binetAbelPlanaFiniteLowerContourTail_integrand w).norm

/-- The norm of the lower finite Abel-Plana tail integrand is strongly
measurable on every lower tail. -/
theorem Complex.aestronglyMeasurable_norm_binetAbelPlanaFiniteLowerContourTail_integrand
    (N : ℕ)
    (w : ℂ) :
    AEStronglyMeasurable
      (fun t : ℝ =>
        ‖(-Complex.I) *
          ((Complex.log (w + (t : ℂ) * Complex.I) -
              Complex.log (w - (t : ℂ) * Complex.I)) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))‖)
      (volume.restrict (Set.Ioi (N : ℝ))) := by
  exact
    (Complex.measurable_norm_binetAbelPlanaFiniteLowerContourTail_integrand
      w).aestronglyMeasurable

/-- Integral comparison for the omitted lower Abel-Plana tail. -/
theorem Complex.norm_binetAbelPlanaFiniteLowerContourTail_le_tailKernelMass
    {w : ℂ}
    (hw : 0 < w.re) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ N : ℕ in atTop,
          ‖Complex.binetAbelPlanaFiniteLowerContourTail N w‖ ≤
            C * ∫ t : ℝ in Set.Ioi (N : ℝ),
              Complex.binetAbelPlanaVerticalKernelMajorant t := by
  rcases
      Complex.norm_binetAbelPlanaFiniteLowerContourTail_integrand_le_majorant
        hw with
    ⟨C, hC_nonneg, hC⟩
  refine ⟨C, hC_nonneg, ?_⟩
  filter_upwards [hC] with N hN
  let I : ℝ → ℂ := fun t : ℝ =>
    (-Complex.I) *
      ((Complex.log (w + (t : ℂ) * Complex.I) -
          Complex.log (w - (t : ℂ) * Complex.I)) /
        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
  let K : ℝ → ℝ := fun t : ℝ =>
    Complex.binetAbelPlanaVerticalKernelMajorant t
  have htail_subset :
      Set.Ioi (N : ℝ) ⊆ Set.Ioi (0 : ℝ) := by
    intro t ht
    exact lt_of_le_of_lt (Nat.cast_nonneg N) ht
  have hCK_integrable :
      IntegrableOn (fun t : ℝ => C * K t) (Set.Ioi (N : ℝ)) :=
    (Complex.binetAbelPlanaVerticalKernelMajorant_integrableOn.mono_set
      htail_subset).const_mul C
  have hnorm_meas :
      AEStronglyMeasurable (fun t : ℝ => ‖I t‖)
        (volume.restrict (Set.Ioi (N : ℝ))) := by
    dsimp [I]
    exact
      Complex.aestronglyMeasurable_norm_binetAbelPlanaFiniteLowerContourTail_integrand
        N w
  have hnorm_integrable :
      IntegrableOn (fun t : ℝ => ‖I t‖) (Set.Ioi (N : ℝ)) := by
    have hpointwise :
        ∀ᵐ t ∂volume.restrict (Set.Ioi (N : ℝ)),
          ‖‖I t‖‖ ≤ C * K t := by
      filter_upwards [hN] with t ht
      have hnorm_nonneg : 0 ≤ ‖I t‖ := norm_nonneg _
      exact (Real.norm_of_nonneg hnorm_nonneg) ▸ ht
    exact hCK_integrable.mono' hnorm_meas hpointwise
  have hmono :
      ∫ t : ℝ in Set.Ioi (N : ℝ), ‖I t‖ ≤
        ∫ t : ℝ in Set.Ioi (N : ℝ), C * K t :=
    setIntegral_mono_ae_restrict
      hnorm_integrable
      hCK_integrable
      hN
  have hconst :
      ∫ t : ℝ in Set.Ioi (N : ℝ), C * K t =
        C * ∫ t : ℝ in Set.Ioi (N : ℝ), K t := by
    exact integral_const_mul
  have hnorm_integral :
      ‖Complex.binetAbelPlanaFiniteLowerContourTail N w‖ ≤
        ∫ t : ℝ in Set.Ioi (N : ℝ), ‖I t‖ := by
    dsimp [Complex.binetAbelPlanaFiniteLowerContourTail, I]
    exact norm_integral_le_integral_norm _
  exact hnorm_integral.trans (hmono.trans_eq hconst)

/-- Owner lower-tail estimate in fixed-ray kernel-tail form. -/
theorem Complex.exists_norm_binetAbelPlanaFiniteLowerContourTail_le_kernelTail_owner
    {w : ℂ}
    (hw : 0 < w.re) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ N : ℕ in atTop,
          ‖Complex.binetAbelPlanaFiniteLowerContourTail N w‖ ≤
            C * ∫ t : ℝ in Set.Ioi (N : ℝ),
              Complex.binetAbelPlanaVerticalKernelMajorant t := by
  exact
    Complex.norm_binetAbelPlanaFiniteLowerContourTail_le_tailKernelMass
      hw

/-- Owner estimate for the honest total finite Abel-Plana contour remainder.

The total remainder is the sum of the lower truncation tail and the upper
endpoint residual.  This theorem is the analytic tail estimate replacing the
old false upper-only remainder bridge. -/
theorem Complex.exists_norm_binetAbelPlanaFiniteContourRemainder_le_kernelTail_add_upperMajorant_owner
    {w : ℂ}
    (hw : 0 < w.re) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ N : ℕ in atTop,
          ‖Complex.binetAbelPlanaFiniteContourRemainder N w‖ ≤
            C * ∫ t : ℝ in Set.Ioi (N : ℝ),
                Complex.binetAbelPlanaVerticalKernelMajorant t +
              Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N := by
  rcases
      Complex.exists_norm_binetAbelPlanaFiniteLowerContourTail_le_kernelTail_owner
        hw with
    ⟨C, hC_nonneg, hlower⟩
  refine ⟨C, hC_nonneg, ?_⟩
  have hupper :
      ∀ᶠ N : ℕ in atTop,
        ‖Complex.binetAbelPlanaFiniteUpperContourResidual N w‖ ≤
          Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N :=
    Complex.norm_binetAbelPlanaFiniteUpperContourResidual_le_majorant_owner hw
  filter_upwards [hlower, hupper] with N hN_lower hN_upper
  calc
    ‖Complex.binetAbelPlanaFiniteContourRemainder N w‖
        ≤
        ‖Complex.binetAbelPlanaFiniteLowerContourTail N w‖ +
          ‖Complex.binetAbelPlanaFiniteUpperContourResidual N w‖ := by
          dsimp [Complex.binetAbelPlanaFiniteContourRemainder]
          exact norm_add_le
            (Complex.binetAbelPlanaFiniteLowerContourTail N w)
            (Complex.binetAbelPlanaFiniteUpperContourResidual N w)
    _ ≤
        C * ∫ t : ℝ in Set.Ioi (N : ℝ),
            Complex.binetAbelPlanaVerticalKernelMajorant t +
          Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N := by
          exact add_le_add hN_lower hN_upper

/-- Owner finite-contour remainder estimate in majorant form. -/
theorem Complex.exists_norm_binetAbelPlanaFiniteRemainderError_le_kernelTail_add_upperMajorant_owner
    {w : ℂ}
    (hw : 0 < w.re) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ N : ℕ in atTop,
          ‖Complex.binetAbelPlanaFiniteRemainderError N w‖ ≤
            C * ∫ t : ℝ in Set.Ioi (N : ℝ),
                Complex.binetAbelPlanaVerticalKernelMajorant t +
              Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N := by
  have hidentity :
      ∀ N : ℕ,
        Complex.binetAbelPlanaFiniteRemainderError N w =
          Complex.binetAbelPlanaFiniteContourRemainder N w :=
    Complex.binetAbelPlanaFiniteRemainderError_eq_contourRemainder_owner
      hw
  rcases
      Complex.exists_norm_binetAbelPlanaFiniteContourRemainder_le_kernelTail_add_upperMajorant_owner
        hw with
    ⟨C, hC_nonneg, hbound⟩
  refine ⟨C, hC_nonneg, ?_⟩
  filter_upwards [hbound] with N hN
  exact hidentity N ▸ hN

/-- Norm convergence from a fixed-ray lower kernel-tail estimate and the
upper-endpoint majorant estimate. -/
theorem Complex.binetAbelPlanaFiniteRemainderError_norm_tendsto_zero_of_kernelTail_add_upperMajorant
    {w : ℂ}
    {C : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hbound :
      ∀ᶠ N : ℕ in atTop,
        ‖Complex.binetAbelPlanaFiniteRemainderError N w‖ ≤
          C * ∫ t : ℝ in Set.Ioi (N : ℝ),
              Complex.binetAbelPlanaVerticalKernelMajorant t +
            Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N) :
    Tendsto
      (fun N : ℕ =>
        ‖Complex.binetAbelPlanaFiniteRemainderError N w‖)
      atTop
      (𝓝 (0 : ℝ)) := by
  have hlower_tail :
      Tendsto
        (fun N : ℕ =>
          ∫ t : ℝ in Set.Ioi (N : ℝ),
            Complex.binetAbelPlanaVerticalKernelMajorant t)
        atTop
        (𝓝 (0 : ℝ)) := by
    have hmajorant :
        Tendsto
          (fun N : ℕ =>
            Complex.binetAbelPlanaFiniteLowerContourTailMajorant w N)
          atTop
          (𝓝 (0 : ℝ)) :=
      Complex.binetAbelPlanaFiniteLowerContourTailMajorant_tendsto_zero w
    have hscale :
        Tendsto
          (fun N : ℕ =>
            (2 : ℝ) * ∫ t : ℝ in Set.Ioi (N : ℝ),
              Complex.binetAbelPlanaVerticalKernelMajorant t)
          atTop
          (𝓝 (0 : ℝ)) := by
      have heq :
          (fun N : ℕ =>
            Complex.binetAbelPlanaFiniteLowerContourTailMajorant w N) =
          (fun N : ℕ =>
            (2 : ℝ) * ∫ t : ℝ in Set.Ioi (N : ℝ),
              Complex.binetAbelPlanaVerticalKernelMajorant t) := by
        funext N
        rfl
      exact heq ▸ hmajorant
    have hinv :
        Tendsto
          (fun N : ℕ =>
            (1 / 2 : ℝ) *
              ((2 : ℝ) * ∫ t : ℝ in Set.Ioi (N : ℝ),
                Complex.binetAbelPlanaVerticalKernelMajorant t))
          atTop
          (𝓝 ((1 / 2 : ℝ) * 0)) :=
      tendsto_const_nhds.mul hscale
    have heq_tail :
        (fun N : ℕ =>
          (1 / 2 : ℝ) *
            ((2 : ℝ) * ∫ t : ℝ in Set.Ioi (N : ℝ),
              Complex.binetAbelPlanaVerticalKernelMajorant t)) =
        (fun N : ℕ =>
          ∫ t : ℝ in Set.Ioi (N : ℝ),
            Complex.binetAbelPlanaVerticalKernelMajorant t) := by
      funext N
      exact Real.half_mul_two_mul
        (∫ t : ℝ in Set.Ioi (N : ℝ),
          Complex.binetAbelPlanaVerticalKernelMajorant t)
    exact (mul_zero (1 / 2 : ℝ)).symm ▸ (heq_tail ▸ hinv)
  have hlower_scaled :
      Tendsto
        (fun N : ℕ =>
          C * ∫ t : ℝ in Set.Ioi (N : ℝ),
            Complex.binetAbelPlanaVerticalKernelMajorant t)
        atTop
        (𝓝 (C * 0)) :=
    tendsto_const_nhds.mul hlower_tail
  have hupper :
      Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N)
        atTop
        (𝓝 (0 : ℝ)) :=
    Complex.binetAbelPlanaFiniteUpperContourResidualMajorant_tendsto_zero w
  have hsum :
      Tendsto
        (fun N : ℕ =>
          C * ∫ t : ℝ in Set.Ioi (N : ℝ),
              Complex.binetAbelPlanaVerticalKernelMajorant t +
            Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N)
        atTop
        (𝓝 (C * 0 + 0)) :=
    hlower_scaled.add hupper
  exact
    squeeze_zero'
      (Eventually.of_forall
        (fun N : ℕ =>
          norm_nonneg
            (Complex.binetAbelPlanaFiniteRemainderError N w)))
      hbound
      ((Real.mul_zero_add_zero C) ▸ hsum)

/-- Norm decay of the finite Abel-Plana contour remainder.

This is the finite-contour estimate for the logarithmic summand.  It is stated
as norm convergence because the classical proof bounds the top and vertical
finite-contour residuals before passing to the complex limit. -/
theorem Complex.binetAbelPlanaFiniteRemainderError_norm_tendsto_zero_owner
    {w : ℂ}
    (hw : 0 < w.re) :
    Tendsto
      (fun N : ℕ =>
        ‖Complex.binetAbelPlanaFiniteRemainderError N w‖)
      atTop
      (𝓝 (0 : ℝ)) := by
  have hnorm_bound :
      ∃ C : ℝ,
        0 ≤ C ∧
          ∀ᶠ N : ℕ in atTop,
            ‖Complex.binetAbelPlanaFiniteRemainderError N w‖ ≤
              C * ∫ t : ℝ in Set.Ioi (N : ℝ),
                  Complex.binetAbelPlanaVerticalKernelMajorant t +
                Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N :=
    Complex.exists_norm_binetAbelPlanaFiniteRemainderError_le_kernelTail_add_upperMajorant_owner
      hw
  rcases hnorm_bound with ⟨C, hC_nonneg, hbound⟩
  exact
    Complex.binetAbelPlanaFiniteRemainderError_norm_tendsto_zero_of_kernelTail_add_upperMajorant
      hC_nonneg
      hbound

/-- Algebraic/topological assembly of complex convergence from norm decay of
the finite Abel-Plana contour remainder. -/
theorem Complex.binetAbelPlanaFiniteRemainderError_tendsto_zero_of_norm_tendsto_zero
    {w : ℂ}
    (hnorm :
      Tendsto
        (fun N : ℕ =>
          ‖Complex.binetAbelPlanaFiniteRemainderError N w‖)
        atTop
        (𝓝 (0 : ℝ))) :
    Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteRemainderError N w)
      atTop
      (𝓝 (0 : ℂ)) := by
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

/-- Finite Abel-Plana contour-remainder decay in complex form. -/
theorem Complex.binetAbelPlanaFiniteRemainderError_tendsto_zero_from_contourNorm_owner
    {w : ℂ}
    (hw : 0 < w.re) :
    Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteRemainderError N w)
      atTop
      (𝓝 (0 : ℂ)) := by
  exact
    Complex.binetAbelPlanaFiniteRemainderError_tendsto_zero_of_norm_tendsto_zero
      (Complex.binetAbelPlanaFiniteRemainderError_norm_tendsto_zero_owner hw)

end

end LFunctions
end Boundary
