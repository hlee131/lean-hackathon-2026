namespace Array

#check Array

def mergeSubarrays [Ord α] [Inhabited α] (as into : Vector α n) (iLeft iRight iEnd : Nat) : Vector α n :=
  if h : n ≤ iLeft ∨ iEnd ≤ iLeft then
    (dbgTraceIfShared "intoMergeSubarrays" into)
  else
    -- Clamp iEnd to n
    let iEnd := min iEnd n
    -- Clamp iRight to between iLeft and iEnd
    let iRight :=
      if iRight ≤ iLeft then iLeft
      else min iRight iEnd
    have : iRight ≤ n := by grind
    loop as into iLeft iRight iRight iEnd iLeft (by grind)
where
  loop (as into : Vector α n) (iLeft endLeft iRight endRight j : Nat)
    (hLoop : (endLeft - iLeft) + (endRight - iRight) = endRight - j)
    (hLeft : endLeft ≤ n := by omega)
    (hRight : endRight ≤ n := by omega)
    : Vector α n :=
  if hj : j >= endRight then
    into
  else
    let hLeftLERight :=
      let left : Option α :=
        if h : iLeft < endLeft then as[iLeft] else none
      let right : Option α :=
        if h : iRight < endRight then as[iRight] else none
      let comp := pure compare <*> left <*> right
      comp = some .lt ∨ comp = some .eq
    if h : iLeft < endLeft ∧ (iRight ≥ endRight ∨ hLeftLERight) then
      let into_new := (dbgTraceIfShared "intoMergeSubarrays1" into).set j as[iLeft]
      let bar := #[into.toArray[0]!]
      let baz := bar.drop 1
      let foo : Vector α 0 := ⟨baz, by rfl⟩

      loop as (into_new ++ foo) (iLeft+1) endLeft iRight endRight (j+1) (by omega)
    else
      let into_new := (dbgTraceIfShared "intoMergeSubarrays2" into).set j as[iRight]
      let bar := #[into.toArray[0]!]
      let baz := bar.drop 1
      let foo : Vector α 0 := ⟨baz, by rfl⟩

      loop as (into_new ++ foo) iLeft endLeft (iRight+1) endRight (j+1) (by omega)

def mergeSort [Ord α] [Inhabited α] (arr : Array α) : Array α :=
  loop arr.toVector (Array.mk arr.toList).toVector 1 |>.toArray
where
  loop {n : Nat} (as into : Vector α n) (width : Nat) : Vector α n :=
    if h : width = 0 ∨ width ≥ n then
      as
    else Id.run do
      let mut into := into
      for iLeft in { stop := n, step := 2*width, step_pos := by omega : Std.Range } do
        let iRight := min (iLeft + width) n
        let iEnd := min (iLeft + 2*width) n
        into := mergeSubarrays as into iLeft iRight iEnd
      loop into as (2*width)  -- Note as and into have swapped roles
  termination_by n - width

end Array
