import Lake
open Lake DSL

def lean_version := "v4.25.0"

package "notebook" where
  require verso from git
    "https://github.com/leanprover/verso.git" @ "v4.25.0"
  require mathlib from git
    "https://github.com/leanprover-community/mathlib4.git" @ "v4.25.0"
  require proofwidgets from git
    "https://github.com/leanprover-community/ProofWidgets4" @ "v0.0.79"

lean_lib «Notebook» where

@[default_target]
lean_exe "notebook" where
  root := `Main
