import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleRectangleTraceCorQ.Owner

/-!
# Zero-pole rectangle-certified typed homs

This file lifts the rectangle-certified zero-pole residue generator from a raw
`TraceCorQ` formal sum to a typed hom in the trace-correspondence category.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The typed source object for the rectangle-certified zero-pole residue step. -/
def completedZetaZeroPoleResidueRectangleHomSource
    (R : ℝ) :
    TraceCorQObject :=
  completedZetaZeroPoleResiduePresentationWithRectangle R

/-- The typed target object for the rectangle-certified zero-pole residue step. -/
def completedZetaZeroPoleResidueRectangleHomTarget :
    TraceCorQObject :=
  completedZetaZeroPoleResidueOutput

/-- The rectangle-certified residue generator as a typed hom term. -/
def completedZetaZeroPoleResidueRectangleTraceCorQHomTerm
    (R : ℝ) :
    TraceCorQHomTerm
      (completedZetaZeroPoleResidueRectangleHomSource R)
      completedZetaZeroPoleResidueRectangleHomTarget :=
  TraceCorQHomTerm.ofGenerator
    (completedZetaZeroPoleResidueRectangleHomSource R)
    completedZetaZeroPoleResidueRectangleHomTarget
    1
    (completedZetaZeroPoleResidueRectangleTraceCorQGenerator R)
    rfl
    rfl

/-- The typed rectangle-certified residue term has coefficient one. -/
theorem completedZetaZeroPoleResidueRectangleTraceCorQHomTerm_coefficient
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleTraceCorQHomTerm R).coefficient =
      1 :=
  rfl

/-- The typed rectangle-certified residue term has the rectangle-certified generator. -/
theorem completedZetaZeroPoleResidueRectangleTraceCorQHomTerm_generator
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleTraceCorQHomTerm R).generator =
      completedZetaZeroPoleResidueRectangleTraceCorQGenerator R :=
  rfl

/-- The typed rectangle-certified residue term carries the generator rewrite-step payload. -/
theorem completedZetaZeroPoleResidueRectangleTraceCorQHomTerm_rewriteStepCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleTraceCorQHomTerm R).rewriteStepCount =
      (completedZetaZeroPoleResidueRectangleTraceCorQGenerator R).rewriteStepCount :=
  rfl

/-- The rectangle-certified residue generator as a typed singleton formal sum. -/
def completedZetaZeroPoleResidueRectangleTraceCorQHomFormalSum
    (R : ℝ) :
    TraceCorQHomFormalSum
      (completedZetaZeroPoleResidueRectangleHomSource R)
      completedZetaZeroPoleResidueRectangleHomTarget :=
  TraceCorQHomFormalSum.singleton
    (completedZetaZeroPoleResidueRectangleHomSource R)
    completedZetaZeroPoleResidueRectangleHomTarget
    1
    (completedZetaZeroPoleResidueRectangleTraceCorQGenerator R)
    rfl
    rfl

/-- Forgetting endpoint proofs recovers the raw rectangle-certified singleton. -/
theorem completedZetaZeroPoleResidueRectangleTraceCorQHomFormalSum_raw
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleTraceCorQHomFormalSum R).raw =
      completedZetaZeroPoleResidueRectangleTraceCorQFormalSum R :=
  rfl

/-- The typed singleton carries the same certificate ledger as the raw rectangle-certified singleton. -/
theorem completedZetaZeroPoleResidueRectangleTraceCorQHomFormalSum_certificateLedger
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleTraceCorQHomFormalSum R).certificateLedger =
      (completedZetaZeroPoleResidueRectangleTraceCorQFormalSum R).certificateLedger :=
  congrArg
    TraceCorQFormalSum.certificateLedger
    (completedZetaZeroPoleResidueRectangleTraceCorQHomFormalSum_raw R)

/-- The typed singleton carries the same rectangle list as the raw rectangle-certified singleton. -/
theorem completedZetaZeroPoleResidueRectangleTraceCorQHomFormalSum_importedRectangles
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleTraceCorQHomFormalSum R).importedRectangles =
      (completedZetaZeroPoleResidueRectangleTraceCorQFormalSum R).importedRectangles :=
  congrArg
    TraceCorQFormalSum.importedRectangles
    (completedZetaZeroPoleResidueRectangleTraceCorQHomFormalSum_raw R)

/-- The typed singleton carries the same rewrite-step payload as the raw rectangle singleton. -/
theorem completedZetaZeroPoleResidueRectangleTraceCorQHomFormalSum_rewriteStepCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleTraceCorQHomFormalSum R).rewriteStepCount =
      (completedZetaZeroPoleResidueRectangleTraceCorQFormalSum R).rewriteStepCount :=
  congrArg
    TraceCorQFormalSum.rewriteStepCount
    (completedZetaZeroPoleResidueRectangleTraceCorQHomFormalSum_raw R)

/-- The rectangle-certified residue typed hom class. -/
def completedZetaZeroPoleResidueRectangleTraceCorQHom
    (R : ℝ) :
    TraceCorQHom
      (completedZetaZeroPoleResidueRectangleHomSource R)
      completedZetaZeroPoleResidueRectangleHomTarget :=
  TraceCorQHom.ofFormalSum
    (completedZetaZeroPoleResidueRectangleTraceCorQHomFormalSum R)

/-- The typed hom is represented by the rectangle-certified singleton formal sum. -/
theorem completedZetaZeroPoleResidueRectangleTraceCorQHom_eq_ofFormalSum
    (R : ℝ) :
    completedZetaZeroPoleResidueRectangleTraceCorQHom R =
      TraceCorQHom.ofFormalSum
        (completedZetaZeroPoleResidueRectangleTraceCorQHomFormalSum R) :=
  rfl

/--
The rectangle-certified typed hom is sound at the height recorded by its
source rectangle certificate.
-/
theorem completedZetaZeroPoleResidueRectangleTraceCorQHom_sound
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {R : ℝ} (hR : 0 < R) :
    completedZetaZeroPoleFiniteSquareBoundaryTrace f R =
      completedZetaZeroPoleFiniteSquareResidueTrace f :=
  completedZetaZeroPoleResidueRectangleTraceCorQGenerator_sound
    f hPhi hR

/--
The rectangle-certified typed hom is sound when the recorded rectangle height
is positive.
-/
theorem completedZetaZeroPoleResidueRectangleTraceCorQHom_sound_of_rectangleHeight
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {R : ℝ}
    (hT : 0 < (completedZetaZeroPoleFiniteSquareRectangle R).T) :
    completedZetaZeroPoleFiniteSquareBoundaryTrace f R =
      completedZetaZeroPoleFiniteSquareResidueTrace f :=
  completedZetaZeroPoleResidueRectangleTraceCorQHom_sound
    f hPhi hT

end AnalyticMotives
end LFunctions
end Boundary
