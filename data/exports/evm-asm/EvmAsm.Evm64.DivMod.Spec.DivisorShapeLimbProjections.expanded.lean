/-
  EvmAsm.Evm64.DivMod.Spec.DivisorShapeLimbProjections

  Per-limb projection lemmas extracting the individual `getLimbN` facts
  from each `NkShapeIs` predicate.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.DivisorShapeNamed


-- @@ L12-12 verbatim
public section


-- @@ L14-14 verbatim
namespace EvmAsm.Evm64


-- @@ L16-16 verbatim
open EvmAsm.Rv64


-- @@ L18-18 verbatim
namespace N1ShapeIs


-- @@ L20-20 verbatim
theorem b3_eq_zero {b : EvmWord} (h : N1ShapeIs b) : b.getLimbN 3 = 0 := h.2.1

-- @@ L21-21 verbatim
theorem b2_eq_zero {b : EvmWord} (h : N1ShapeIs b) : b.getLimbN 2 = 0 := h.2.2.1

-- @@ L22-22 verbatim
theorem b1_eq_zero {b : EvmWord} (h : N1ShapeIs b) : b.getLimbN 1 = 0 := h.2.2.2.1

-- @@ L23-23 verbatim
theorem b0_ne_zero {b : EvmWord} (h : N1ShapeIs b) : b.getLimbN 0 ≠ 0 := h.2.2.2.2


-- @@ L25-25 verbatim
end N1ShapeIs


-- @@ L27-27 verbatim
namespace N2ShapeIs


-- @@ L29-29 verbatim
theorem b3_eq_zero {b : EvmWord} (h : N2ShapeIs b) : b.getLimbN 3 = 0 := h.2.1

-- @@ L30-30 verbatim
theorem b2_eq_zero {b : EvmWord} (h : N2ShapeIs b) : b.getLimbN 2 = 0 := h.2.2.1

-- @@ L31-31 verbatim
theorem b1_ne_zero {b : EvmWord} (h : N2ShapeIs b) : b.getLimbN 1 ≠ 0 := h.2.2.2


-- @@ L33-33 verbatim
end N2ShapeIs


-- @@ L35-35 verbatim
namespace N3ShapeIs


-- @@ L37-37 verbatim
theorem b3_eq_zero {b : EvmWord} (h : N3ShapeIs b) : b.getLimbN 3 = 0 := h.2.1

-- @@ L38-38 verbatim
theorem b2_ne_zero {b : EvmWord} (h : N3ShapeIs b) : b.getLimbN 2 ≠ 0 := h.2.2


-- @@ L40-40 verbatim
end N3ShapeIs


-- @@ L42-42 verbatim
namespace N4ShapeIs


-- @@ L44-44 verbatim
theorem b3_ne_zero {b : EvmWord} (h : N4ShapeIs b) : b.getLimbN 3 ≠ 0 := h.2


-- @@ L46-46 verbatim
end N4ShapeIs


-- @@ L48-48 verbatim
end EvmAsm.Evm64
