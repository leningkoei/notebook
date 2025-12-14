import Notebook

import VersoManual

-- open Verso.Genre Manual
-- open Verso Code External

-- #print Verso.Genre.Manual.Config
def config : Verso.Genre.Manual.Config where
  emitTeX := false
  emitHtmlSingle := false
  emitHtmlMulti := true
  htmlDepth := 3

def main :=
  Verso.Genre.Manual.manualMain (%doc Notebook) (config := config.addKaTeX)

-- def main : IO Unit :=
--   IO.println s!"Hello, {hello}!"
