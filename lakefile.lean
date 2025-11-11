import Lake
open Lake DSL

package «biosim» where
  moreLeanArgs := #["-DwarningAsError=true"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.9.0"

@[default_target] lean_lib Biosim where
  roots := #[`Biosim]

lean_exe biosim_tests where
  root := `Tests.Main
  supportInterpreter := true

lean_exe veribiota where
  root := `Main
  supportInterpreter := true
