import Hackathon

def sort : [Ord α] → [Inhabited α] → Array α → Array α := Array.mergeSort

def getLines : IO (Array String) := do
  let stdin ← IO.getStdin
  let mut lines : Array String := #[]
  let mut currLine ← stdin.getLine
  while !currLine.isEmpty do
    -- Drop trailing newline:
    lines := lines.push (currLine.dropRight 1)
    currLine ← stdin.getLine
  return lines

def mainUnique : IO Unit := do
  let lines ← getLines
  for line in sort lines do
    IO.println line

def mainShared : IO Unit := do
  let lines ← getLines
  IO.println "--- Sorted lines: ---"
  for line in sort lines do
    IO.println line

  IO.println ""
  IO.println "--- Original data: ---"
  for line in lines do
    IO.println line

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--shared"] => mainShared; return 0
  | ["--unique"] => mainUnique; return 0
  | _ =>
    IO.println "Expected single argument, either \"--shared\" or \"--unique\""
    return 1
