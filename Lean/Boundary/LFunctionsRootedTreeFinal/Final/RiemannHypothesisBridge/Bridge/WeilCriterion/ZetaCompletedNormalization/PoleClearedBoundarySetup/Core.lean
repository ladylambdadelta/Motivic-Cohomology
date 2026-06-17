import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Core pole-cleared zeta definition

This file owns the definition-level removable pole-clearing package, without
importing the later Gamma/Phragmen-Lindelöf boundary machinery.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology

def poleClearedRiemannZeta (z : ℂ) : ℂ :=
  Function.update (fun w : ℂ => (w - 1) * riemannZeta w) 1 1 z

/-- Away from the pole face, the removable pole-cleared factor is the ordinary product. -/
theorem poleClearedRiemannZeta_eq_of_ne_one
    {z : ℂ}
    (hz : z ≠ 1) :
    poleClearedRiemannZeta z = (z - 1) * riemannZeta z := by
  exact Function.update_noteq hz 1 (fun w : ℂ => (w - 1) * riemannZeta w)

/-- At the pole face, the removable pole-cleared factor has residue value `1`. -/
theorem poleClearedRiemannZeta_one :
    poleClearedRiemannZeta 1 = 1 := by
  exact Function.update_same 1 1 (fun w : ℂ => (w - 1) * riemannZeta w)

end

end LFunctions
end Boundary
