import Notebook

import VersoManual

def config : Verso.Genre.Manual.Config where
  emitTeX := false
  emitHtmlSingle := false
  emitHtmlMulti := true
  htmlDepth := 3

def main :=
  Verso.Genre.Manual.manualMain (%doc Notebook) (config := config)

-- def main : IO Unit :=
--   IO.println s!"Hello, {hello}!"
