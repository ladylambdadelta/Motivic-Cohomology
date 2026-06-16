import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaClassicalInputs

/-!
# Owner theorems for the Abel-Plana derivation of Binet's formula

This file contains the irreducible classical inputs needed for Binet's second
formula.  The public package should consume these named owner theorems through
`BinetAbelPlana.lean`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Exponentiating the finite logarithmic approximation recovers mathlib's
complex Euler `GammaSeq`, after the index shift used by the Abel-Plana finite
formula.

This is the correct branch-safe bridge.  The finite approximation itself is a
chosen logarithm of `GammaSeq`; it should not be identified with the principal
`Complex.log (GammaSeq ...)` without a separate branch-normalization theorem. -/
theorem Complex.exp_binetAbelPlanaLogGammaFiniteApproximation_eq_GammaSeq
    {N : ℕ}
    {w : ℂ}
    (hw : 0 < w.re) :
    Complex.exp (Complex.binetAbelPlanaLogGammaFiniteApproximation N w) =
      Complex.GammaSeq w (N + 1) := by
  let M : ℕ := N + 1
  have hM_ne : (M : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero N)
  have hfactorial_ne : (((Nat.factorial M : ℕ) : ℂ) ≠ 0) := by
    exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero M)
  have hterm_ne :
      ∀ n : ℕ, n ∈ Finset.range (M + 1) → w + n ≠ 0 := by
    intro n _hn hzero
    have hre_zero : (w + (n : ℂ)).re = 0 := by
      exact congrArg Complex.re hzero
    have hre_sum : (w + (n : ℂ)).re = w.re + n := by
      exact Complex.add_re w (n : ℂ)
    have hn_nonneg : (0 : ℝ) ≤ n := by
      exact Nat.cast_nonneg n
    have hw_nonpos : w.re ≤ 0 := by
      have hsum_zero : w.re + n = 0 :=
        hre_sum.symm.trans hre_zero
      have hw_eq_neg : w.re = -(n : ℝ) := by
        calc
          w.re = w.re + (n : ℝ) - (n : ℝ) := by
            exact (add_sub_cancel_right w.re (n : ℝ)).symm
          _ = 0 - (n : ℝ) := by
            exact congrArg (fun x : ℝ => x - (n : ℝ)) hsum_zero
          _ = -(n : ℝ) := zero_sub (n : ℝ)
      calc
        w.re = -(n : ℝ) := hw_eq_neg
        _ ≤ 0 := neg_nonpos.mpr hn_nonneg
    exact not_lt_of_ge hw_nonpos hw
  calc
    Complex.exp (Complex.binetAbelPlanaLogGammaFiniteApproximation N w)
        =
        Complex.exp
          (w * Complex.log (M : ℂ) +
            Complex.log ((Nat.factorial M : ℕ) : ℂ) -
              ∑ n in Finset.range (M + 1), Complex.log (w + n)) := by
      dsimp [Complex.binetAbelPlanaLogGammaFiniteApproximation, M]
      rfl
    _ =
        Complex.exp (w * Complex.log (M : ℂ)) *
          Complex.exp (Complex.log ((Nat.factorial M : ℕ) : ℂ)) /
            Complex.exp
              (∑ n in Finset.range (M + 1), Complex.log (w + n)) := by
      exact Complex.exp_sub _ _
    _ =
        Complex.exp (Complex.log (M : ℂ) * w) *
          ((Nat.factorial M : ℕ) : ℂ) /
            (∏ n in Finset.range (M + 1), w + n) := by
      have hnum :
          Complex.exp (Complex.log ((Nat.factorial M : ℕ) : ℂ)) =
            ((Nat.factorial M : ℕ) : ℂ) := by
        exact Complex.exp_log hfactorial_ne
      have hden :
          Complex.exp
            (∑ n in Finset.range (M + 1), Complex.log (w + n)) =
          ∏ n in Finset.range (M + 1), (w + n) := by
        exact
          (Complex.exp_sum (s := Finset.range (M + 1))
            (f := fun n => Complex.log (w + n))).trans
              (Finset.prod_congr rfl
                (fun n hn => Complex.exp_log (hterm_ne n hn)))
      have hfrac :
          Complex.exp (Complex.log (M : ℂ) * w) *
            Complex.exp (Complex.log ((Nat.factorial M : ℕ) : ℂ)) /
              Complex.exp
                (∑ n in Finset.range (M + 1), Complex.log (w + n)) =
          Complex.exp (Complex.log (M : ℂ) * w) *
            ((Nat.factorial M : ℕ) : ℂ) /
              (∏ n in Finset.range (M + 1), w + n) := by
        calc
          Complex.exp (Complex.log (M : ℂ) * w) *
              Complex.exp (Complex.log ((Nat.factorial M : ℕ) : ℂ)) /
                Complex.exp
                  (∑ n in Finset.range (M + 1), Complex.log (w + n)) =
            Complex.exp (Complex.log (M : ℂ) * w) *
              (((Nat.factorial M : ℕ) : ℂ) /
                Complex.exp
                  (∑ n in Finset.range (M + 1), Complex.log (w + n))) := by
              exact congrArg
                (fun z : ℂ => Complex.exp (Complex.log (M : ℂ) * w) * z /
                  Complex.exp
                    (∑ n in Finset.range (M + 1), Complex.log (w + n))) hnum
          _ = Complex.exp (Complex.log (M : ℂ) * w) *
              (((Nat.factorial M : ℕ) : ℂ) /
                (∏ n in Finset.range (M + 1), w + n)) := by
              exact congrArg
                (fun z : ℂ => Complex.exp (Complex.log (M : ℂ) * w) * z) (
                  congrArg (fun z : ℂ => ((Nat.factorial M : ℕ) : ℂ) / z) hden)
      exact hfrac
      exact hsum
    _ =
        (M : ℂ) ^ w * ((Nat.factorial M : ℕ) : ℂ) /
          (∏ n in Finset.range (M + 1), w + n) := by
      have hpow : (M : ℂ) ^ w = Complex.exp (Complex.log (M : ℂ) * w) := by
        exact Complex.cpow_def_of_ne_zero hM_ne
      exact hpow
    _ = Complex.GammaSeq w (N + 1) := by
      dsimp [Complex.GammaSeq, M]
      rfl

/-- Truncating an integrable function on `(0,N]` tends to its integral on the
positive half-line.  This is the local improper-integral API needed by the
Binet Abel-Plana boundary term. -/
theorem Complex.tendsto_integral_Ioc_natCast_of_integrableOn_Ioi
    {f : ℝ → ℂ}
    (hf : IntegrableOn f (Set.Ioi (0 : ℝ))) :
    Tendsto
      (fun N : ℕ => ∫ t : ℝ in Set.Ioc (0 : ℝ) (N : ℝ), f t)
      atTop
      (𝓝 (∫ t : ℝ in Set.Ioi (0 : ℝ), f t)) := by
  let s : ℕ → Set ℝ := fun N : ℕ => Set.Ioc (0 : ℝ) (N : ℝ)
  have hs_measurable :
      ∀ N : ℕ, MeasurableSet (s N) := by
    intro N
    exact measurableSet_Ioc
  have hs_monotone : Monotone s := by
    intro N M hNM
    intro x hx
    exact ⟨hx.1, le_trans hx.2 (Nat.cast_le.mpr hNM)⟩
  have hs_union :
      (⋃ N : ℕ, s N) = Set.Ioi (0 : ℝ) := by
    exact iUnion_Ioc_eq_Ioi_self_iff.mpr
      (fun x _hx => exists_nat_ge x)
  have h_integrable_union :
      IntegrableOn f (⋃ N : ℕ, s N) := by
    exact hs_union.symm ▸ hf
  have h_tendsto :
      Tendsto
        (fun N : ℕ => ∫ t in s N, f t)
        atTop
        (𝓝 (∫ t in ⋃ N : ℕ, s N, f t)) :=
    tendsto_setIntegral_of_monotone
      hs_measurable hs_monotone h_integrable_union
  exact hs_union ▸ h_tendsto

/-- Reassemble an expression from two named finite Abel-Plana summands and
the remainder defined by subtracting them. -/
theorem add_add_sub_add_remainder
    (A M B : ℂ) :
    A = M + B + (A - (M + B)) := by
  calc
    A = (M + B) + (A - (M + B)) := by
      exact (add_sub_cancel'_right A (M + B)).symm
    _ = M + B + (A - (M + B)) := rfl

/-- Reassemble a finite main term from its limiting term and the endpoint
Stirling remainder. -/
theorem add_sub_remainder
    (F L : ℂ) :
    F = L + (F - L) := by
  exact (add_sub_cancel'_right F L).symm

/-- Dropping a terminal zero from a Binet main-plus-remainder expression. -/
theorem binet_branch_add_zero_eq
    (M R : ℂ) :
    M + R + 0 = M + R := by
  exact add_zero (M + R)

/-- Exact finite Abel-Plana transform for the logarithmic summand in the Euler
Gamma approximants.

The finite formula must use a finite main term.  Replacing this by the limiting
`binetLogGammaMainTerm` before taking limits is the false shortcut this owner
file is designed to avoid. -/
theorem Complex.binetAbelPlana_logGammaFiniteApproximation_eq_finiteMainTerm_add_boundary_add_error
    {N : ℕ}
    {w : ℂ}
    (hw : 0 < w.re) :
    Complex.binetAbelPlanaLogGammaFiniteApproximation N w =
      Complex.binetAbelPlanaFiniteMainTerm N w +
        Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
          Complex.binetAbelPlanaFiniteRemainderError N w := by
  dsimp [Complex.binetAbelPlanaFiniteRemainderError]
  exact add_add_sub_add_remainder
    (Complex.binetAbelPlanaLogGammaFiniteApproximation N w)
    (Complex.binetAbelPlanaFiniteMainTerm N w)
    (Complex.binetAbelPlanaFiniteBoundaryCorrection N w)

/-- Exact split of the finite main term into the limiting Binet main term and
the endpoint/Stirling remainder. -/
theorem Complex.binetAbelPlana_finiteMainTerm_eq_binetMainTerm_add_endpointStirlingRemainder
    {N : ℕ}
    {w : ℂ} :
    Complex.binetAbelPlanaFiniteMainTerm N w =
      Complex.binetLogGammaMainTerm w +
        Complex.binetAbelPlanaFiniteEndpointStirlingRemainder N w := by
  dsimp [Complex.binetAbelPlanaFiniteEndpointStirlingRemainder]
  exact add_sub_remainder
    (Complex.binetAbelPlanaFiniteMainTerm N w)
    (Complex.binetLogGammaMainTerm w)

/-- Endpoint/Stirling convergence in its finite-main-term form.

This is the exact local reduction needed by the endpoint remainder root: once
the finite Abel-Plana main term is proved to converge to the Binet main term,
the named endpoint remainder is just the difference of those two terms. -/
theorem Complex.binetAbelPlana_endpointStirlingRemainder_tendsto_zero_of_finiteMainTerm
    {w : ℂ}
    (hmain :
      Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaFiniteMainTerm N w)
        atTop
        (𝓝 (Complex.binetLogGammaMainTerm w))) :
    Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteEndpointStirlingRemainder N w)
      atTop
      (𝓝 (0 : ℂ)) := by
  have hdiff :
      Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaFiniteMainTerm N w -
            Complex.binetLogGammaMainTerm w)
        atTop
        (𝓝 (Complex.binetLogGammaMainTerm w -
          Complex.binetLogGammaMainTerm w)) :=
    hmain.sub tendsto_const_nhds
  have heq :
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteEndpointStirlingRemainder N w) =
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteMainTerm N w -
          Complex.binetLogGammaMainTerm w) := by
    funext N
    dsimp [Complex.binetAbelPlanaFiniteEndpointStirlingRemainder]
  exact (sub_self _).symm ▸ (heq ▸ hdiff)

/-- Endpoint/Stirling remainder vanishes in the Euler limit. -/
theorem Complex.binetAbelPlana_endpointStirlingRemainder_tendsto_zero
    {w : ℂ}
    (hw : 0 < w.re) :
    Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteEndpointStirlingRemainder N w)
      atTop
      (𝓝 (0 : ℂ)) := by
  exact
    Complex.binetAbelPlana_endpointStirlingRemainder_tendsto_zero_of_finiteMainTerm
      (Complex.binetAbelPlanaFiniteMainTerm_tendsto_binetMainTerm_owner hw)

/-- Finite endpoint/Stirling asymptotics: the explicit finite Abel-Plana main
term converges to the Binet logarithmic main term. -/
theorem Complex.binetAbelPlana_finiteMainTerm_tendsto_binetMainTerm_from_endpointStirling
    {w : ℂ}
    (hw : 0 < w.re) :
    Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteMainTerm N w)
      atTop
      (𝓝 (Complex.binetLogGammaMainTerm w)) := by
  exact
    Complex.binetAbelPlanaFiniteMainTerm_tendsto_binetMainTerm_owner hw

/-- The finite Abel-Plana remainder error vanishes in the Euler limit. -/
theorem Complex.binetAbelPlana_finiteRemainderError_tendsto_zero
    {w : ℂ}
    (hw : 0 < w.re) :
    Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteRemainderError N w)
      atTop
      (𝓝 (0 : ℂ)) := by
  exact
    Complex.binetAbelPlanaFiniteRemainderError_tendsto_zero_owner hw

/-- If the exact finite Abel-Plana formula has no residual term at a given
index, the named finite remainder error is zero at that index.

The hypothesis is the concrete finite Abel-Plana identity for the exact
logarithmic summand and exact endpoint/boundary terms; it is not a generic
interface. -/
theorem Complex.binetAbelPlana_finiteRemainderError_eq_zero_of_exact_finiteAbelPlana
    {N : ℕ}
    {w : ℂ}
    (hfinite :
      Complex.binetAbelPlanaLogGammaFiniteApproximation N w =
        Complex.binetAbelPlanaFiniteMainTerm N w +
          Complex.binetAbelPlanaFiniteBoundaryCorrection N w) :
    Complex.binetAbelPlanaFiniteRemainderError N w = 0 := by
  dsimp [Complex.binetAbelPlanaFiniteRemainderError]
  calc
    Complex.binetAbelPlanaLogGammaFiniteApproximation N w -
        Complex.binetAbelPlanaFiniteMainTerm N w -
        Complex.binetAbelPlanaFiniteBoundaryCorrection N w = 0 := by
      have h' :
          Complex.binetAbelPlanaLogGammaFiniteApproximation N w -
            (Complex.binetAbelPlanaFiniteMainTerm N w +
              Complex.binetAbelPlanaFiniteBoundaryCorrection N w) = 0 := by
        calc
          Complex.binetAbelPlanaLogGammaFiniteApproximation N w -
              (Complex.binetAbelPlanaFiniteMainTerm N w +
                Complex.binetAbelPlanaFiniteBoundaryCorrection N w)
              =
            (Complex.binetAbelPlanaFiniteMainTerm N w +
              Complex.binetAbelPlanaFiniteBoundaryCorrection N w) -
              (Complex.binetAbelPlanaFiniteMainTerm N w +
                Complex.binetAbelPlanaFiniteBoundaryCorrection N w) := by
              exact congrArg
                (fun z : ℂ => z - (Complex.binetAbelPlanaFiniteMainTerm N w +
                  Complex.binetAbelPlanaFiniteBoundaryCorrection N w)) hfinite
          _ = 0 := by
            exact sub_self _
      exact h'

/-- Eventual exact finite Abel-Plana identities force the finite remainder
error to converge to zero.

This packages the exact finite remainder API separately from the analytic
proof of the finite Abel-Plana identity itself. -/
theorem Complex.binetAbelPlana_finiteRemainderError_tendsto_zero_of_eventually_exact_finiteAbelPlana
    {w : ℂ}
    (hfinite :
      ∀ᶠ N : ℕ in atTop,
        Complex.binetAbelPlanaLogGammaFiniteApproximation N w =
          Complex.binetAbelPlanaFiniteMainTerm N w +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N w) :
    Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteRemainderError N w)
      atTop
      (𝓝 (0 : ℂ)) := by
  have hzero :
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteRemainderError N w) =ᶠ[atTop]
      (fun _N : ℕ => (0 : ℂ)) :=
    hfinite.mono
      (fun N hN =>
        Complex.binetAbelPlana_finiteRemainderError_eq_zero_of_exact_finiteAbelPlana
          (N := N) (w := w) hN)
  exact hzero.tendsto_iff.mpr tendsto_const_nhds

/-- The Abel-Plana logarithmic jump equals the normalized arctangent-kernel
boundary correction. -/
theorem Complex.binetAbelPlana_boundaryCorrection_eq_normalizedBoundary
    {N : ℕ}
    {w : ℂ}
    (hw : 0 < w.re) :
    Complex.binetAbelPlanaFiniteBoundaryCorrection N w =
      Complex.binetAbelPlanaFiniteNormalizedBoundary N w := by
  let L : ℝ → ℂ := fun t : ℝ =>
    (-Complex.I) *
      ((Complex.log (w + (t : ℂ) * Complex.I) -
          Complex.log (w - (t : ℂ) * Complex.I)) /
        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
  let K : ℝ → ℂ := fun t : ℝ =>
    Complex.arctan ((t : ℂ) / w) /
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)
  have hpointwise :
      ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) (N : ℝ)),
        L t = 2 * K t :=
    (ae_restrict_mem measurableSet_Ioc).mono
      (fun t ht =>
        Complex.binetAbelPlana_logJump_integrand_eq_two_arctanKernel
          hw ht.1)
  have hintegral :
      ∫ t : ℝ in Set.Ioc (0 : ℝ) (N : ℝ), L t =
        ∫ t : ℝ in Set.Ioc (0 : ℝ) (N : ℝ), 2 * K t :=
    integral_congr_ae hpointwise
  have hscale :
      ∫ t : ℝ in Set.Ioc (0 : ℝ) (N : ℝ), 2 * K t =
        2 * ∫ t : ℝ in Set.Ioc (0 : ℝ) (N : ℝ), K t :=
    integral_const_mul 2 K
  exact
    Eq.trans
      (by
        dsimp [Complex.binetAbelPlanaFiniteBoundaryCorrection, L]
        rfl)
      (Eq.trans hintegral
        (Eq.trans hscale
          (by
            dsimp [Complex.binetAbelPlanaFiniteNormalizedBoundary, K]
            rfl).symm))

/-- The normalized finite Binet boundary integral converges to the full
second-formula remainder. -/
theorem Complex.binetAbelPlana_normalizedBoundaryKernel_integrableOn_Ioi
    {w : ℂ}
    (hw : 0 < w.re) :
    IntegrableOn
      (fun t : ℝ =>
        Complex.arctan ((t : ℂ) / w) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
      (Set.Ioi (0 : ℝ)) := by
  exact
    Complex.binetSecondFormula_arctanKernel_integrable_owner hw

/-- The normalized finite Binet boundary integrals converge to the full
positive-half-line arctangent integral. -/
theorem Complex.binetAbelPlana_normalizedBoundary_tendsto_fullIntegral
    {w : ℂ}
    (hw : 0 < w.re) :
    Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteNormalizedBoundary N w)
      atTop
      (𝓝 (2 * ∫ t : ℝ in Set.Ioi (0 : ℝ),
        Complex.arctan ((t : ℂ) / w) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))) := by
  let K : ℝ → ℂ := fun t : ℝ =>
    Complex.arctan ((t : ℂ) / w) /
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)
  have hK :
      IntegrableOn K (Set.Ioi (0 : ℝ)) :=
    Complex.binetAbelPlana_normalizedBoundaryKernel_integrableOn_Ioi hw
  have htrunc :
      Tendsto
        (fun N : ℕ => ∫ t : ℝ in Set.Ioc (0 : ℝ) (N : ℝ), K t)
        atTop
        (𝓝 (∫ t : ℝ in Set.Ioi (0 : ℝ), K t)) :=
    Complex.tendsto_integral_Ioc_natCast_of_integrableOn_Ioi hK
  have hscaled :
      Tendsto
        (fun N : ℕ => 2 * ∫ t : ℝ in Set.Ioc (0 : ℝ) (N : ℝ), K t)
        atTop
        (𝓝 (2 * ∫ t : ℝ in Set.Ioi (0 : ℝ), K t)) :=
    tendsto_const_nhds.mul htrunc
  exact hscaled

/-- The normalized full positive-half-line arctangent integral is the Binet
second-formula remainder. -/
theorem Complex.binetAbelPlana_fullIntegral_eq_binetRemainder
    {w : ℂ} :
    2 * ∫ t : ℝ in Set.Ioi (0 : ℝ),
        Complex.arctan ((t : ℂ) / w) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) =
      Complex.binetSecondFormulaRemainder w := by
  rfl

/-- The normalized finite Binet boundary integral converges to the full
second-formula remainder. -/
theorem Complex.binetAbelPlana_normalizedBoundary_tendsto_binetRemainder
    {w : ℂ}
    (hw : 0 < w.re) :
    Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteNormalizedBoundary N w)
      atTop
      (𝓝 (Complex.binetSecondFormulaRemainder w)) := by
  have hfull :
      Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaFiniteNormalizedBoundary N w)
        atTop
        (𝓝 (2 * ∫ t : ℝ in Set.Ioi (0 : ℝ),
          Complex.arctan ((t : ℂ) / w) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))) :=
    Complex.binetAbelPlana_normalizedBoundary_tendsto_fullIntegral hw
  exact
    (Complex.binetAbelPlana_fullIntegral_eq_binetRemainder (w := w)) ▸ hfull

/-- Kernel normalization: the Abel-Plana boundary correction converges to the
arctangent kernel used by Binet's second formula. -/
theorem Complex.binetAbelPlana_boundaryCorrection_tendsto_binetRemainder
    {w : ℂ}
    (hw : 0 < w.re) :
    Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteBoundaryCorrection N w)
      atTop
      (𝓝 (Complex.binetSecondFormulaRemainder w)) := by
  have hnormalized :
      Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaFiniteNormalizedBoundary N w)
        atTop
        (𝓝 (Complex.binetSecondFormulaRemainder w)) :=
    Complex.binetAbelPlana_normalizedBoundary_tendsto_binetRemainder hw
  have heq :
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteBoundaryCorrection N w) =
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteNormalizedBoundary N w) := by
    funext N
    exact
      Complex.binetAbelPlana_boundaryCorrection_eq_normalizedBoundary
        (N := N) hw
  exact heq ▸ hnormalized

/-- The Abel-Plana deformed tail kernel is integrable on the split tail. -/
theorem Complex.binetSecondFormula_abelPlanaDeformedTailKernel_integrableOn_tail
    {w : ℂ}
    (hw : 0 < w.re) :
    IntegrableOn
      (fun t : ℝ =>
        Complex.binetSecondFormulaAbelPlanaDeformedTailKernel w t)
      (Set.Ioi (‖w‖ / 2)) := by
  let P : ℝ → ℂ := fun t : ℝ =>
    Complex.binetSecondFormulaPrincipalTailKernel w t
  let M : ℝ → ℝ := fun t : ℝ =>
    t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
  have hP_integrable :
      IntegrableOn P (Set.Ioi (‖w‖ / 2)) :=
    Complex.binetSecondFormula_arctanKernel_integrableOn_tail_interval_owner
      hw
  have hM_integrable_Ioi : IntegrableOn M (Set.Ioi (0 : ℝ)) :=
    Real.binetSecondFormula_kernel_majorant_integrableOn
  have hcut_nonneg : (0 : ℝ) ≤ ‖w‖ / 2 :=
    div_nonneg (norm_nonneg w) zero_le_two
  have hM_tail : IntegrableOn M (Set.Ioi (‖w‖ / 2)) :=
    hM_integrable_Ioi.mono_set (Ioi_subset_Ioi hcut_nonneg)
  have hP_norm :
      IntegrableOn (fun t : ℝ => ‖P t‖) (Set.Ioi (‖w‖ / 2)) :=
    hP_integrable.norm
  have hM_scaled_abs :
      IntegrableOn
        (fun t : ℝ => |((1 : ℝ) / ‖w‖) * M t|)
        (Set.Ioi (‖w‖ / 2)) :=
    (hM_tail.const_mul ((1 : ℝ) / ‖w‖)).norm
  have hsum :
      IntegrableOn
        (fun t : ℝ =>
          (‖P t‖ + |((1 : ℝ) / ‖w‖) * M t| : ℝ))
        (Set.Ioi (‖w‖ / 2)) :=
    hP_norm.add hM_scaled_abs
  exact
    Eq.ndrec
      (Complex.ofRealCLM.integrable_comp hsum)
      (by
        funext t
        dsimp [Complex.binetSecondFormulaAbelPlanaDeformedTailKernel,
          Complex.binetSecondFormulaContourTailMajorantKernel, P, M]
        rfl)

/-- The deformed tail kernel was normalized to contain the principal tail norm,
so the pointwise comparison is an immediate kernel-normalization fact. -/
theorem Complex.binetSecondFormula_principalTailKernel_norm_le_abelPlanaDeformedTailKernel_norm
    (w : ℂ)
    (t : ℝ) :
    ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
      ‖Complex.binetSecondFormulaAbelPlanaDeformedTailKernel w t‖ := by
  let P : ℂ := Complex.binetSecondFormulaPrincipalTailKernel w t
  let A : ℝ :=
    |((1 : ℝ) / ‖w‖) *
      (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))|
  have hnonneg : 0 ≤ ‖P‖ + A :=
    add_nonneg (norm_nonneg P) (abs_nonneg _)
  have hnorm :
      ‖((‖P‖ + A : ℝ) : ℂ)‖ = ‖P‖ + A := by
    calc
      ‖((‖P‖ + A : ℝ) : ℂ)‖ = |(‖P‖ + A : ℝ)| := Complex.norm_ofReal _
      _ = ‖P‖ + A := by
        exact abs_of_nonneg hnonneg
  have hle : ‖P‖ ≤ ‖P‖ + A :=
    le_add_of_nonneg_right (abs_nonneg _)
  dsimp [Complex.binetSecondFormulaAbelPlanaDeformedTailKernel,
    Complex.binetSecondFormulaContourTailMajorantKernel, P, A] at hnorm ⊢
  exact hnorm.symm ▸ hle

/-- Abel-Plana contour deformation gives the branch-safe pointwise tail
comparison. -/
theorem Complex.binetSecondFormula_abelPlanaDeformedTail_pointwiseComparison :
    Complex.BinetSecondFormulaAbelPlanaDeformedTailPointwiseComparison
      Complex.binetSecondFormulaAbelPlanaDeformedTailKernel 2 := by
  intro w _hw _hR
  filter_upwards with t
  exact
    Complex.binetSecondFormula_principalTailKernel_norm_le_abelPlanaDeformedTailKernel_norm
      w t

/-- Integrating the Abel-Plana pointwise contour comparison gives the principal
tail integral comparison. -/
theorem Complex.binetSecondFormula_abelPlanaDeformedTail_integralComparison :
    Complex.BinetSecondFormulaPrincipalTailKernelIntegralComparison
      Complex.binetSecondFormulaAbelPlanaDeformedTailKernel 2 := by
  intro w hw hR
  let P : ℝ → ℂ := fun t : ℝ =>
    Complex.binetSecondFormulaPrincipalTailKernel w t
  let K : ℝ → ℂ := fun t : ℝ =>
    Complex.binetSecondFormulaAbelPlanaDeformedTailKernel w t
  have hP_integrable :
      IntegrableOn P (Set.Ioi (‖w‖ / 2)) := by
    exact
      Complex.binetSecondFormula_arctanKernel_integrableOn_tail_interval_owner
        hw
  have hK_integrable :
      IntegrableOn K (Set.Ioi (‖w‖ / 2)) :=
    Complex.binetSecondFormula_abelPlanaDeformedTailKernel_integrableOn_tail hw
  have hpointwise :
      ∀ᵐ t ∂volume.restrict (Set.Ioi (‖w‖ / 2)),
        ‖P t‖ ≤ ‖K t‖ :=
    Complex.binetSecondFormula_abelPlanaDeformedTail_pointwiseComparison
      w hw hR
  exact
    setIntegral_mono_ae
      hP_integrable.norm
      hK_integrable.norm
      hpointwise

/-- Limit assembly for the Euler/Binet logarithm branch from the finite
Abel-Plana identity and the two convergence statements. -/
theorem Complex.binetAbelPlanaLogGammaFiniteApproximation_tendsto_binetLogGammaBranch
    (w : ℂ)
    (hw : 0 < w.re) :
    Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaLogGammaFiniteApproximation N w)
      atTop
      (𝓝 (Complex.binetLogGammaBranch w)) := by
  have hboundary :
      Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaFiniteBoundaryCorrection N w)
        atTop
        (𝓝 (Complex.binetSecondFormulaRemainder w)) :=
    Complex.binetAbelPlana_boundaryCorrection_tendsto_binetRemainder hw
  have hmain :
      Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaFiniteMainTerm N w)
        atTop
        (𝓝 (Complex.binetLogGammaMainTerm w)) :=
    Complex.binetAbelPlana_finiteMainTerm_tendsto_binetMainTerm_from_endpointStirling hw
  have herror :
      Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaFiniteRemainderError N w)
        atTop
        (𝓝 (0 : ℂ)) :=
    Complex.binetAbelPlana_finiteRemainderError_tendsto_zero hw
  have hsum :
      Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaFiniteMainTerm N w +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
              Complex.binetAbelPlanaFiniteRemainderError N w)
        atTop
        (𝓝 (Complex.binetLogGammaMainTerm w +
          Complex.binetSecondFormulaRemainder w + 0)) :=
    (hmain.add hboundary).add herror
  have hfinite_eq :
      (fun N : ℕ =>
        Complex.binetAbelPlanaLogGammaFiniteApproximation N w) =
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteMainTerm N w +
          Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
            Complex.binetAbelPlanaFiniteRemainderError N w) := by
    funext N
    exact
      Complex.binetAbelPlana_logGammaFiniteApproximation_eq_finiteMainTerm_add_boundary_add_error
        (N := N) hw
  have hfinite_as_sum :
      Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaFiniteMainTerm N w +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
              Complex.binetAbelPlanaFiniteRemainderError N w)
        atTop
        (𝓝 (Complex.binetLogGammaMainTerm w +
          Complex.binetSecondFormulaRemainder w + 0)) :=
    hsum
  have htarget :
      Complex.binetLogGammaMainTerm w +
          Complex.binetSecondFormulaRemainder w + 0 =
        Complex.binetLogGammaBranch w := by
    dsimp [Complex.binetLogGammaBranch]
    exact binet_branch_add_zero_eq
      (Complex.binetLogGammaMainTerm w)
      (Complex.binetSecondFormulaRemainder w)
  exact htarget ▸ (hfinite_eq.symm ▸ hfinite_as_sum)

/-- Abel-Plana constructs the analytic Euler/Binet logarithm branch of Gamma:
exponentiating the branch recovers `Gamma` on the open right half-plane. -/
theorem Complex.exp_binetLogGammaBranch_eq_Gamma_from_AbelPlanaOwner
    (w : ℂ)
    (hw : 0 < w.re) :
    Complex.exp (Complex.binetLogGammaBranch w) =
      Complex.Gamma w := by
  have hfinite_branch :
      Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaLogGammaFiniteApproximation N w)
        atTop
        (𝓝 (Complex.binetLogGammaBranch w)) :=
    Complex.binetAbelPlanaLogGammaFiniteApproximation_tendsto_binetLogGammaBranch
      w hw
  have hexp_branch :
      Tendsto
        (fun N : ℕ =>
          Complex.exp
            (Complex.binetAbelPlanaLogGammaFiniteApproximation N w))
        atTop
        (𝓝 (Complex.exp (Complex.binetLogGammaBranch w))) :=
    Complex.continuous_exp.continuousAt.tendsto.comp hfinite_branch
  have hGammaSeq :
      Tendsto
        (fun N : ℕ => Complex.GammaSeq w (N + 1))
        atTop
        (𝓝 (Complex.Gamma w)) :=
    (Complex.GammaSeq_tendsto_Gamma w).comp
      (tendsto_add_atTop_nat 1)
  have hsame :
      (fun N : ℕ =>
        Complex.exp
          (Complex.binetAbelPlanaLogGammaFiniteApproximation N w)) =
      (fun N : ℕ => Complex.GammaSeq w (N + 1)) := by
    funext N
    exact
      Complex.exp_binetAbelPlanaLogGammaFiniteApproximation_eq_GammaSeq
        (N := N) hw
  exact tendsto_nhds_unique (hsame ▸ hexp_branch) hGammaSeq

/-- The contour-deformed tail comparison produced by the Abel-Plana
deformation. -/
theorem Complex.binetSecondFormula_principalTailKernel_branchSingularity_absorbed_by_AbelPlanaContourOwner :
    Complex.BinetSecondFormulaPrincipalTailKernelIntegralComparison
      Complex.binetSecondFormulaContourTailMajorantKernel 2 := by
  exact
    Complex.binetSecondFormula_abelPlanaDeformedTail_integralComparison

end

end LFunctions
end Boundary
