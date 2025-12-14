import Lake
open Lake DSL

def lean_version := "v4.24.0"

package "notebook" where
  require verso from git
    "https://github.com/leanprover/verso.git" @ lean_version
  require mathlib from git
    "https://github.com/leanprover-community/mathlib4.git" @ lean_version

lean_lib «Notebook» where

@[default_target]
lean_exe "notebook" where
  root := `Main

