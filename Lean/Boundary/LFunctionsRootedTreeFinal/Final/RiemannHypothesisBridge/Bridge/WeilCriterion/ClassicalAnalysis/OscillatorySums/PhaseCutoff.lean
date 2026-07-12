import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.FinitePoissonReconstruction
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Smooth cutoff extensions of real oscillatory phases

The cutoff is kept as an explicit amplitude.  Its support and smoothness are
used to form a Schwartz extension, and its values at integers determine the
finite sample family reconstructed by Poisson summation.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped ContDiff FourierTransform

/-- A real oscillatory phase multiplied by a real smooth cutoff. -/
def Complex.phaseCutoffFunction
    (phase cutoff : ℝ → ℝ)
    (x : ℝ) : ℂ :=
  cutoff x • Complex.exp (Complex.I * (phase x : ℂ))

/-- Pointwise smoothness of a phase-cutoff function. -/
theorem Complex.contDiffAt_phaseCutoffFunction
    (phase cutoff : ℝ → ℝ)
    (x : ℝ)
    (hphase : ContDiffAt ℝ ∞ phase x)
    (hcutoff : ContDiffAt ℝ ∞ cutoff x) :
    ContDiffAt ℝ ∞ (Complex.phaseCutoffFunction phase cutoff) x := by
  have hphaseComplex :
      ContDiffAt ℝ ∞ (fun y : ℝ => (phase y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hphase
  have hexponent :
      ContDiffAt ℝ ∞
        (fun y : ℝ => Complex.I * (phase y : ℂ)) x :=
    contDiffAt_const.mul hphaseComplex
  have hoscillation :
      ContDiffAt ℝ ∞
        (fun y : ℝ => Complex.exp (Complex.I * (phase y : ℂ))) x :=
    hexponent.cexp
  exact hcutoff.smul hoscillation

/-- Smoothness of the phase-cutoff function. -/
theorem Complex.contDiff_phaseCutoffFunction
    (phase cutoff : ℝ → ℝ)
    (hphase : ContDiff ℝ ∞ phase)
    (hcutoff : ContDiff ℝ ∞ cutoff) :
    ContDiff ℝ ∞ (Complex.phaseCutoffFunction phase cutoff) := by
  have hphaseComplex :
      ContDiff ℝ ∞ (fun x : ℝ => (phase x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hphase
  have hexponent :
      ContDiff ℝ ∞ (fun x : ℝ => Complex.I * (phase x : ℂ)) :=
    contDiff_const.mul hphaseComplex
  have hoscillation :
      ContDiff ℝ ∞
        (fun x : ℝ => Complex.exp (Complex.I * (phase x : ℂ))) :=
    hexponent.cexp
  exact hcutoff.smul hoscillation

/-- Compact support of the phase-cutoff function comes entirely from the
cutoff amplitude. -/
theorem Complex.hasCompactSupport_phaseCutoffFunction
    (phase cutoff : ℝ → ℝ)
    (hcutoff : HasCompactSupport cutoff) :
    HasCompactSupport (Complex.phaseCutoffFunction phase cutoff) := by
  exact hcutoff.smul_right

/-- Canonical Schwartz extension of a smooth real phase through a smooth
compactly supported cutoff. -/
def Complex.phaseCutoffSchwartzOfSmoothProduct
    (phase cutoff : ℝ → ℝ)
    (hsmooth : ContDiff ℝ ∞ (Complex.phaseCutoffFunction phase cutoff))
    (hcutoffCompact : HasCompactSupport cutoff) : SchwartzMap ℝ ℂ :=
  SchwartzMap.ofSmoothCompactSupport
    (Complex.phaseCutoffFunction phase cutoff)
    hsmooth
    (Complex.hasCompactSupport_phaseCutoffFunction
      phase cutoff hcutoffCompact)

/-- Evaluation of the product-smooth cutoff Schwartz extension. -/
theorem Complex.phaseCutoffSchwartzOfSmoothProduct_apply
    (phase cutoff : ℝ → ℝ)
    (hsmooth : ContDiff ℝ ∞ (Complex.phaseCutoffFunction phase cutoff))
    (hcutoffCompact : HasCompactSupport cutoff)
    (x : ℝ) :
    Complex.phaseCutoffSchwartzOfSmoothProduct
        phase cutoff hsmooth hcutoffCompact x =
      cutoff x • Complex.exp (Complex.I * (phase x : ℂ)) :=
  rfl

/-- Canonical Schwartz extension when phase and cutoff smoothness are supplied
separately. -/
def Complex.phaseCutoffSchwartz
    (phase cutoff : ℝ → ℝ)
    (hphase : ContDiff ℝ ∞ phase)
    (hcutoffSmooth : ContDiff ℝ ∞ cutoff)
    (hcutoffCompact : HasCompactSupport cutoff) : SchwartzMap ℝ ℂ :=
  Complex.phaseCutoffSchwartzOfSmoothProduct
    phase cutoff
    (Complex.contDiff_phaseCutoffFunction phase cutoff hphase hcutoffSmooth)
    hcutoffCompact

/-- Evaluation of the canonical phase-cutoff Schwartz extension. -/
theorem Complex.phaseCutoffSchwartz_apply
    (phase cutoff : ℝ → ℝ)
    (hphase : ContDiff ℝ ∞ phase)
    (hcutoffSmooth : ContDiff ℝ ∞ cutoff)
    (hcutoffCompact : HasCompactSupport cutoff)
    (x : ℝ) :
    Complex.phaseCutoffSchwartz
        phase cutoff hphase hcutoffSmooth hcutoffCompact x =
      cutoff x • Complex.exp (Complex.I * (phase x : ℂ)) :=
  rfl

/-- At a point where the cutoff is one, the extension is the original
oscillation. -/
theorem Complex.phaseCutoffSchwartz_eq_oscillation_of_cutoff_eq_one
    (phase cutoff : ℝ → ℝ)
    (hphase : ContDiff ℝ ∞ phase)
    (hcutoffSmooth : ContDiff ℝ ∞ cutoff)
    (hcutoffCompact : HasCompactSupport cutoff)
    (x : ℝ)
    (hx : cutoff x = 1) :
    Complex.phaseCutoffSchwartz
        phase cutoff hphase hcutoffSmooth hcutoffCompact x =
      Complex.exp (Complex.I * (phase x : ℂ)) := by
  exact
    (congrArg
      (fun value : ℝ =>
        value • Complex.exp (Complex.I * (phase x : ℂ)))
      hx).trans
      (one_smul ℝ (Complex.exp (Complex.I * (phase x : ℂ))))

/-- At a point where the cutoff is zero, the extension vanishes. -/
theorem Complex.phaseCutoffSchwartz_eq_zero_of_cutoff_eq_zero
    (phase cutoff : ℝ → ℝ)
    (hphase : ContDiff ℝ ∞ phase)
    (hcutoffSmooth : ContDiff ℝ ∞ cutoff)
    (hcutoffCompact : HasCompactSupport cutoff)
    (x : ℝ)
    (hx : cutoff x = 0) :
    Complex.phaseCutoffSchwartz
        phase cutoff hphase hcutoffSmooth hcutoffCompact x = 0 := by
  exact
    (congrArg
      (fun value : ℝ =>
        value • Complex.exp (Complex.I * (phase x : ℂ)))
      hx).trans
      (zero_smul ℝ (Complex.exp (Complex.I * (phase x : ℂ))))

/-- Exact finite Poisson reconstruction of a real oscillatory sample family
from a cutoff which is one precisely on the selected integer samples and zero
at all other integers. -/
theorem Complex.finite_realPhase_poisson_reconstruction
    (phase cutoff : ℝ → ℝ)
    (hphase : ContDiff ℝ ∞ phase)
    (hcutoffSmooth : ContDiff ℝ ∞ cutoff)
    (hcutoffCompact : HasCompactSupport cutoff)
    (samples : Finset ℤ)
    (hcutoffOne :
      ∀ n : ℤ,
        n ∈ samples → cutoff (n : ℝ) = 1)
    (hcutoffZero :
      ∀ n : ℤ,
        n ∉ samples → cutoff (n : ℝ) = 0) :
    (∑ n ∈ samples,
        Complex.exp (Complex.I * (phase (n : ℝ) : ℂ))) =
      ∑' m : ℤ,
        SchwartzMap.fourierTransformCLM ℝ
          (Complex.phaseCutoffSchwartz
            phase cutoff hphase hcutoffSmooth hcutoffCompact)
          (m : ℝ) := by
  let extension : SchwartzMap ℝ ℂ :=
    Complex.phaseCutoffSchwartz
      phase cutoff hphase hcutoffSmooth hcutoffCompact
  have hextensionSupport :
      ∀ n : ℤ,
        n ∉ samples → extension (n : ℝ) = 0 := by
    intro n hn
    exact
      Complex.phaseCutoffSchwartz_eq_zero_of_cutoff_eq_zero
        phase cutoff hphase hcutoffSmooth hcutoffCompact
        (n : ℝ) (hcutoffZero n hn)
  have hreconstruction :=
    Complex.finite_integerSample_poisson_reconstruction
      extension samples hextensionSupport
  have hsamples :
      (∑ n ∈ samples, extension (n : ℝ)) =
        ∑ n ∈ samples,
          Complex.exp (Complex.I * (phase (n : ℝ) : ℂ)) := by
    exact
      Finset.sum_congr rfl
        (fun n hn =>
          Complex.phaseCutoffSchwartz_eq_oscillation_of_cutoff_eq_one
            phase cutoff hphase hcutoffSmooth hcutoffCompact
            (n : ℝ) (hcutoffOne n hn))
  exact hsamples.symm.trans hreconstruction

end

end LFunctions
end Boundary
