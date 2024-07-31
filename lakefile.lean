import Lake
open Lake DSL

package «lcf-in-lean» where
  -- add package configuration options here

lean_lib «LcfInLean» where
  -- add library configuration options here

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.9.0"

@[default_target]
lean_exe «lcf-in-lean» where
  root := `Main
