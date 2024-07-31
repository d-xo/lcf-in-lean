import Lake
open Lake DSL

package «lcf-in-lean» where
  -- add package configuration options here

lean_lib «LcfInLean» where
  -- add library configuration options here

@[default_target]
lean_exe «lcf-in-lean» where
  root := `Main
