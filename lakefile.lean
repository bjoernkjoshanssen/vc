import Lake
open Lake DSL

package "VC" where
  -- add package configuration options here

lean_lib «VC» where
  -- add library configuration options here
  require "leanprover-community" / "mathlib"

@[default_target]
lean_exe "vc" where
  root := `Main
