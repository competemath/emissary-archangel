/-
  EvmAsm.Codegen.Programs.BalCapacities

  Named row-capacity contracts shared by the BAL producers and serializer.
  Keeping these values in one module prevents emitted callsites from quietly
  duplicating an arena bound as an unrelated assembly literal.
-/

module


-- @@ L11-11 verbatim
@[expose] public section

-- @@ L12-12 verbatim
namespace EvmAsm.Codegen


-- @@ L14-14 verbatim
def balBuilderAccountCapacity : Nat := 140000

-- @@ L15-15 verbatim
def balBuilderStorageChangeCapacity : Nat := 47522

-- @@ L16-17 verbatim
/-- Block cold-storage bound: `200_000_000 / 3_000 = 66_666` (GH #11186 D4). -/
def balBuilderStorageReadsCapacity : Nat := 66666

-- @@ L18-18 verbatim
def balBuilderBalanceCapacity : Nat := 105000

-- @@ L19-19 verbatim
def balBuilderNonceCapacity : Nat := 35000

-- @@ L20-20 verbatim
def balBuilderCodeCapacity : Nat := 13125


-- @@ L22-22 verbatim
end EvmAsm.Codegen
