import Lean

open Lean

/-- Lives in its own compiled module so the `initialize` block actually runs:
Lean only fires `[init]` declarations for modules that get *imported*, not for
declarations used in the very file that defines them. -/
initialize importedConstantsRef : IO.Ref (Std.HashMap Name ConstantInfo) ← IO.mkRef {}

/-- scripts/bump/gate2_batch.py: whether a library definition means in the new environment what it meant in the original,
decided once per definition per process. -/
initialize gate2bDefMemo : IO.Ref (Std.HashMap Name (Bool × String)) ← IO.mkRef {}
