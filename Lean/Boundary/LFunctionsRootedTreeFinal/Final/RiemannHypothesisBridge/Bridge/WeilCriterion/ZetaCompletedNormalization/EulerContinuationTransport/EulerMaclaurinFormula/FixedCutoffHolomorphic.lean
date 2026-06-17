import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.FixedCutoffCore

/-!
# Fixed-cutoff Euler-Maclaurin holomorphic package

This file owns the fixed-cutoff punctured-strip holomorphic declarations that
were previously embedded in `EulerMaclaurinFormula.Owner`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
open MeasureTheory
local notation "π" => Real.pi

/-- `ζ` is holomorphic on the fixed-cutoff punctured strip, where the pole
point `1` is excluded. -/
theorem eulerMaclaurin_riemannZeta_holomorphicOn_fixedCutoff_puncturedStrip :
    DifferentiableOn ℂ
      riemannZeta
      ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  intro z hz
  exact (differentiableAt_riemannZeta hz.2.2).differentiableWithinAt

/-- Fixed finite Dirichlet polynomial is holomorphic in the complex variable. -/
theorem eulerMaclaurinZetaFinitePartWithCutoff_holomorphicOn_puncturedStrip
    (N : ℕ) :
    DifferentiableOn ℂ
      (eulerMaclaurinZetaFinitePartWithCutoff N)
      ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  unfold eulerMaclaurinZetaFinitePartWithCutoff
  exact
    DifferentiableOn.sum
      (fun n hn => by
        have hn_bounds : n ∈ Finset.Icc 1 N := hn
        have hn_one : 1 ≤ n := (Finset.mem_Icc.mp hn_bounds).1
        have hn_pos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn_one
        have hbase_ne : ((n : ℕ) : ℂ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn_pos)
        have hden :
            DifferentiableOn ℂ
              (fun z : ℂ => (((n : ℕ) : ℂ) ^ z))
              ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
          differentiableOn_id.const_cpow (Or.inl hbase_ne)
        have hnum :
            DifferentiableOn ℂ
              (fun _ : ℂ => (1 : ℂ))
              ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
          differentiableOn_const (1 : ℂ)
        exact
          hnum.div hden
            (fun z hz => by
              intro hzero
              have hbase_zero : ((n : ℕ) : ℂ) = 0 :=
                (Complex.cpow_eq_zero_iff ((n : ℕ) : ℂ) z).mp hzero |>.1
              exact hbase_ne hbase_zero))

/-- Fixed-cutoff main term is holomorphic on the punctured strip. -/
theorem eulerMaclaurinZetaMainTermWithCutoff_holomorphicOn_puncturedStrip
    (N : ℕ)
    (hN : 0 < N) :
    DifferentiableOn ℂ
      (eulerMaclaurinZetaMainTermWithCutoff N)
      ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  unfold eulerMaclaurinZetaMainTermWithCutoff
  have hbase_ne : ((N : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hone :
      DifferentiableOn ℂ
        (fun _ : ℂ => (1 : ℂ))
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    differentiableOn_const (1 : ℂ)
  have hid :
      DifferentiableOn ℂ
        (fun z : ℂ => z)
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    differentiableOn_id
  have hexponent :
      DifferentiableOn ℂ
        (fun z : ℂ => (1 : ℂ) - z)
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    hone.sub hid
  have hnum :
      DifferentiableOn ℂ
        (fun z : ℂ => ((N : ℕ) : ℂ) ^ ((1 : ℂ) - z))
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    hexponent.const_cpow (Or.inl hbase_ne)
  have hden :
      DifferentiableOn ℂ
        (fun z : ℂ => z - 1)
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    hid.sub hone
  exact
    hnum.div hden
      (fun z hz => sub_ne_zero.mpr hz.2.2)

/-- Fixed-cutoff endpoint term is holomorphic on the punctured strip. -/
theorem eulerMaclaurinZetaEndpointTermWithCutoff_holomorphicOn_puncturedStrip
    (N : ℕ)
    (hN : 0 < N) :
    DifferentiableOn ℂ
      (eulerMaclaurinZetaEndpointTermWithCutoff N)
      ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  unfold eulerMaclaurinZetaEndpointTermWithCutoff
  have hbase_ne : ((N : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hid :
      DifferentiableOn ℂ
        (fun z : ℂ => z)
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    differentiableOn_id
  have hden :
      DifferentiableOn ℂ
        (fun z : ℂ => (((N : ℕ) : ℂ) ^ z))
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    hid.const_cpow (Or.inl hbase_ne)
  have hrecip :
      DifferentiableOn ℂ
        (fun z : ℂ => (1 : ℂ) / (((N : ℕ) : ℂ) ^ z))
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    (differentiableOn_const (1 : ℂ)).div hden
      (fun z hz => by
        intro hzero
        have hbase_zero : ((N : ℕ) : ℂ) = 0 :=
          (Complex.cpow_eq_zero_iff ((N : ℕ) : ℂ) z).mp hzero |>.1
        exact hbase_ne hbase_zero)
  have hhalf :
      DifferentiableOn ℂ
        (fun _ : ℂ => -(1 / 2 : ℂ))
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    differentiableOn_const (-(1 / 2 : ℂ))
  exact hhalf.mul hrecip

/-- Pointwise parameter-holomorphicity of the fixed-cutoff Bernoulli kernel.

For each positive real `x`, the parameter dependence
`z ↦ B₁({x}) x^(-(z+1))` is entire.  This is the local kernel theorem used
before applying differentiation under the improper integral. -/
theorem eulerMaclaurinBernoulliKernel_parameter_differentiableOn
    (x : ℝ)
    (hx : 0 < x) :
    DifferentiableOn ℂ
      (fun z : ℂ =>
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((x : ℝ) : ℂ) ^ (-(z + 1))))
      ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  have hbase_ne : ((x : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  have hid :
      DifferentiableOn ℂ
        (fun z : ℂ => z)
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    differentiableOn_id
  have hone :
      DifferentiableOn ℂ
        (fun _ : ℂ => (1 : ℂ))
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    differentiableOn_const (1 : ℂ)
  have hexponent :
      DifferentiableOn ℂ
        (fun z : ℂ => -(z + 1))
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    (hid.add hone).neg
  have hpow :
      DifferentiableOn ℂ
        (fun z : ℂ => (((x : ℝ) : ℂ) ^ (-(z + 1))))
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    hexponent.const_cpow (Or.inl hbase_ne)
  have hfactor :
      DifferentiableOn ℂ
        (fun _ : ℂ => ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ))
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    differentiableOn_const
      (((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ))
  exact hfactor.mul hpow

/-- Local version of the first periodic Bernoulli bound, placed before the
punctured-strip majorant so the local proof does not depend on later
closed-strip estimates. -/
theorem eulerMaclaurinFirstPeriodicBernoulli_norm_cast_le_one_local
    (x : ℝ) :
    ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ ≤ 1 := by
  exact eulerMaclaurinFirstPeriodicBernoulli_norm_cast_le_one_finite x

/-- The first periodic Bernoulli sawtooth is measurable. -/
theorem eulerMaclaurinFirstPeriodicBernoulli_measurable :
    Measurable eulerMaclaurinFirstPeriodicBernoulli := by
  exact eulerMaclaurinFirstPeriodicBernoulli_measurable_finite

/-- The complex-valued first periodic Bernoulli factor is strongly measurable
on every measurable restricted tail. -/
theorem eulerMaclaurinFirstPeriodicBernoulli_cast_aestronglyMeasurable_restrict
    (s : Set ℝ)
    (hs : MeasurableSet s) :
    AEStronglyMeasurable
      (fun x : ℝ => ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ))
      (volume.restrict s) := by
  exact
    eulerMaclaurinFirstPeriodicBernoulli_cast_aestronglyMeasurable_restrict_finite
      s hs

/-- The positive-tail complex-power kernel is continuous on any positive
cutoff tail. -/
theorem eulerMaclaurin_cpow_tail_continuousOn_Ioi
    (N : ℕ)
    (hN : 0 < N)
    (z : ℂ) :
    ContinuousOn
      (fun x : ℝ => (((x : ℝ) : ℂ) ^ (-(z + 1))))
      (Set.Ioi (((N : ℕ) : ℝ))) := by
  intro x hx
  have hx_pos : 0 < x :=
    lt_trans (Nat.cast_pos.mpr hN) hx
  exact
    (Complex.continuousAt_ofReal_cpow_const x (-(z + 1))
      (Or.inr (ne_of_gt hx_pos))).continuousWithinAt

/-- The positive-tail complex-power kernel is a.e.-strongly measurable on a
fixed positive cutoff tail. -/
theorem eulerMaclaurin_cpow_tail_aestronglyMeasurable
    (N : ℕ)
    (hN : 0 < N)
    (z : ℂ) :
    AEStronglyMeasurable
      (fun x : ℝ => (((x : ℝ) : ℂ) ^ (-(z + 1))))
      (volume.restrict (Set.Ioi (((N : ℕ) : ℝ)))) :=
  (eulerMaclaurin_cpow_tail_continuousOn_Ioi N hN z).aestronglyMeasurable
    measurableSet_Ioi

/-- The fixed-parameter Bernoulli/cpow kernel is a.e.-strongly measurable on
a positive cutoff tail. -/
theorem eulerMaclaurinBernoulliKernel_aestronglyMeasurable
    (N : ℕ)
    (hN : 0 < N)
    (z : ℂ) :
    AEStronglyMeasurable
      (fun x : ℝ =>
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((x : ℝ) : ℂ) ^ (-(z + 1))))
      (volume.restrict (Set.Ioi (((N : ℕ) : ℝ)))) := by
  exact
    (eulerMaclaurinFirstPeriodicBernoulli_cast_aestronglyMeasurable_restrict
      (Set.Ioi (((N : ℕ) : ℝ))) measurableSet_Ioi).mul
      (eulerMaclaurin_cpow_tail_aestronglyMeasurable N hN z)
