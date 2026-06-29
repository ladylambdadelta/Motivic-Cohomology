import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ConjugateSymmetricTransforms
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.MellinConjugateLaws
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.MellinInversionConjugacy
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AdmissibleConjugacyComposition
import Boundary.LFunctions.ZetaTransformCalculus

/-!
# Conditional admissible conjugacy from Mellin-side symmetry

The lemmas in this file transport an explicitly supplied Hermitian symmetry
hypothesis through the elementary admissible-function operations used by the
prime boundary files.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open LSeries ArithmeticFunction
open MeasureTheory
open scoped Topology

namespace AdmissibleMellinTheory

/-- A supplied Hermitian time-side hypothesis gives conjugate symmetry. -/
theorem admissibleFunction_conjugateSymmetric
    (f : ZetaAdmissibleFunction)
    (hconj : ∀ c : ℝ,
      f.toZetaTestFunction (-c) = star (f.toZetaTestFunction c))
    (c : ℝ) :
    f.toZetaTestFunction (-c) = star (f.toZetaTestFunction c) :=
  AdmissibleConjugacyComposition.admissible_conjugateSymmetric_composition
    f hconj c

/-- Alternative formulation: The boundary values at opposite logarithmic centers
are conjugates. -/
theorem admissibleFunction_boundary_conjugateSymmetry
    (f : ZetaAdmissibleFunction)
    (hconj : ∀ c : ℝ,
      f.toZetaTestFunction (-c) = star (f.toZetaTestFunction c))
    (c : ℝ) :
    zetaCompletedTimeBoundaryValue f (-c) =
    star (zetaCompletedTimeBoundaryValue f c) := by
  exact admissibleFunction_conjugateSymmetric f hconj c

/-- For natural prime logarithmic centers, admissible functions exhibit the
reflection-dagger property. -/
theorem admissibleFunction_primeCenter_reflectionDagger
    (f : ZetaAdmissibleFunction)
    (hconj : ∀ c : ℝ,
      f.toZetaTestFunction (-c) = star (f.toZetaTestFunction c))
    {n : ℕ} (hn : n ≠ 0) :
    f.toZetaTestFunction (-(zetaCompletedExplicitFormulaPrimeNaturalCenter n)) =
    star (f.toZetaTestFunction (zetaCompletedExplicitFormulaPrimeNaturalCenter n)) :=
  admissibleFunction_conjugateSymmetric
    f hconj (zetaCompletedExplicitFormulaPrimeNaturalCenter n)

/-- The zero admissible function trivially satisfies conjugate symmetry. -/
theorem zero_admissible_conjugateSymmetric :
    ∀ c : ℝ,
    (0 : ZetaAdmissibleFunction).toZetaTestFunction (-c) =
    star ((0 : ZetaAdmissibleFunction).toZetaTestFunction c) := by
  intro c
  simp

/-- Conjugate symmetry is preserved by scalar multiplication (real scalars). -/
theorem scalar_multiple_conjugateSymmetric
    (f : ZetaAdmissibleFunction)
    (hconj : ∀ c : ℝ,
      f.toZetaTestFunction (-c) = star (f.toZetaTestFunction c))
    (r : ℝ) (c : ℝ) :
    (r • f).toZetaTestFunction (-c) =
    star ((r • f).toZetaTestFunction c) := by
  have hf := admissibleFunction_conjugateSymmetric f hconj c
  have h_scalar_at_neg : (r • f).toZetaTestFunction (-c) = (r : ℂ) * f.toZetaTestFunction (-c) := by
    exact rfl
  have h_scalar_at_c : (r • f).toZetaTestFunction c = (r : ℂ) * f.toZetaTestFunction c := by
    exact rfl
  calc
    (r • f).toZetaTestFunction (-c)
        = (r : ℂ) * f.toZetaTestFunction (-c) := h_scalar_at_neg
      _ = (r : ℂ) * star (f.toZetaTestFunction c) := by exact congr_arg (fun x => (r : ℂ) * x) hf
      _ = star ((r : ℂ) * f.toZetaTestFunction c) := by
          exact (star_mul_of_real r (f.toZetaTestFunction c)).symm
      _ = star ((r • f).toZetaTestFunction c) := by exact congr_arg star h_scalar_at_c.symm

/-- Conjugate symmetry is preserved by addition. -/
theorem add_conjugateSymmetric
    (f g : ZetaAdmissibleFunction)
    (hfconj : ∀ c : ℝ,
      f.toZetaTestFunction (-c) = star (f.toZetaTestFunction c))
    (hgconj : ∀ c : ℝ,
      g.toZetaTestFunction (-c) = star (g.toZetaTestFunction c))
    (c : ℝ) :
    (f + g).toZetaTestFunction (-c) =
    star ((f + g).toZetaTestFunction c) := by
  have hf := admissibleFunction_conjugateSymmetric f hfconj c
  have hg := admissibleFunction_conjugateSymmetric g hgconj c
  calc
    (f + g).toZetaTestFunction (-c)
        = f.toZetaTestFunction (-c) + g.toZetaTestFunction (-c) := by rfl
      _ = star (f.toZetaTestFunction c) + star (g.toZetaTestFunction c) := by
          rw [hf, hg]
      _ = star (f.toZetaTestFunction c + g.toZetaTestFunction c) := by
          exact (star_add (f.toZetaTestFunction c) (g.toZetaTestFunction c)).symm
      _ = star ((f + g).toZetaTestFunction c) := by rfl

end AdmissibleMellinTheory

end LFunctions
end Boundary
