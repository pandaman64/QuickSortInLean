import Lake
open Lake DSL

package «QuickSortInLean» where
  -- add package configuration options here

lean_lib «QuickSortInLean» where
  -- add library configuration options here

@[default_target]
lean_exe «quicksortinlean» where
  root := `Main
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true

require «std» from git "https://github.com/leanprover/std4" @ "main"
