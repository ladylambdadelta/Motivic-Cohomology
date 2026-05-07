import Lake
open Lake DSL

package «tracecalc» where
  moreLeanArgs := #["-DautoImplicit=false"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.14.0"

@[default_target]
lean_lib TraceCalc where
  srcDir := "Lean"
