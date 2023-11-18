import QuickSortInLean

def main (args : List String) : IO Unit := do
  let orig := args.toArray
  let sorted := quickSort orig
  for s in sorted do
    IO.println s

  -- IO.println "Showing the original array necessiates a copy! (but only one)"
  -- for s in orig do
  --   IO.println s
