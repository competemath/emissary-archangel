/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.Incidence
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD


-- @@ L15-20 verbatim
/-! # Thirteen explicit candidate incidence representatives

The word “residual” is a historical label from exploratory computation. This
module defines the systems exactly but makes no claim that they exhaust all
normalized, balanced, pair-sparse incidence systems.
-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
namespace Erdos97Octagon


-- @@ L26-33 verbatim
/-- The exact residual incidence representative of class 0. -/
def residualRepresentative00 : OctagonIncidence where
  targets := ![
    {1, 2, 3, 4}, {0, 2, 3, 5}, {0, 4, 5, 6}, {2, 4, 5, 7},
    {3, 5, 6, 7}, {1, 2, 6, 7}, {0, 1, 4, 7}, {0, 1, 3, 6}
  ]
  card_targets v := by fin_cases v <;> decide
  centre_not_mem v := by fin_cases v <;> decide


-- @@ L35-42 verbatim
/-- The exact residual incidence representative of class 1. -/
def residualRepresentative01 : OctagonIncidence where
  targets := ![
    {1, 2, 3, 4}, {0, 2, 3, 5}, {0, 4, 5, 6}, {2, 4, 6, 7},
    {1, 3, 5, 7}, {0, 3, 6, 7}, {0, 1, 4, 7}, {1, 2, 5, 6}
  ]
  card_targets v := by fin_cases v <;> decide
  centre_not_mem v := by fin_cases v <;> decide


-- @@ L44-51 verbatim
/-- The exact residual incidence representative of class 2. -/
def residualRepresentative02 : OctagonIncidence where
  targets := ![
    {1, 2, 3, 4}, {0, 2, 3, 5}, {0, 5, 6, 7}, {2, 4, 6, 7},
    {1, 2, 5, 6}, {0, 3, 4, 7}, {1, 3, 5, 7}, {0, 1, 4, 6}
  ]
  card_targets v := by fin_cases v <;> decide
  centre_not_mem v := by fin_cases v <;> decide


-- @@ L53-60 verbatim
/-- The exact residual incidence representative of class 3. -/
def residualRepresentative03 : OctagonIncidence where
  targets := ![
    {1, 2, 3, 4}, {0, 2, 3, 5}, {0, 1, 4, 6}, {0, 4, 5, 7},
    {0, 3, 6, 7}, {2, 4, 6, 7}, {1, 3, 5, 7}, {1, 2, 5, 6}
  ]
  card_targets v := by fin_cases v <;> decide
  centre_not_mem v := by fin_cases v <;> decide


-- @@ L62-69 verbatim
/-- The exact residual incidence representative of class 4. -/
def residualRepresentative04 : OctagonIncidence where
  targets := ![
    {1, 2, 3, 4}, {0, 2, 3, 5}, {0, 1, 4, 6}, {2, 4, 6, 7},
    {1, 3, 5, 7}, {0, 3, 6, 7}, {0, 4, 5, 7}, {1, 2, 5, 6}
  ]
  card_targets v := by fin_cases v <;> decide
  centre_not_mem v := by fin_cases v <;> decide


-- @@ L71-78 verbatim
/-- The exact residual incidence representative of class 5. -/
def residualRepresentative05 : OctagonIncidence where
  targets := ![
    {1, 2, 3, 4}, {0, 2, 5, 6}, {3, 4, 5, 7}, {1, 2, 6, 7},
    {1, 3, 5, 6}, {0, 3, 6, 7}, {0, 2, 4, 7}, {0, 1, 4, 5}
  ]
  card_targets v := by fin_cases v <;> decide
  centre_not_mem v := by fin_cases v <;> decide


-- @@ L80-87 verbatim
/-- The exact residual incidence representative of class 6. -/
def residualRepresentative06 : OctagonIncidence where
  targets := ![
    {1, 2, 3, 4}, {0, 2, 3, 5}, {0, 1, 4, 6}, {0, 1, 5, 7},
    {1, 3, 6, 7}, {0, 2, 6, 7}, {3, 4, 5, 7}, {2, 4, 5, 6}
  ]
  card_targets v := by fin_cases v <;> decide
  centre_not_mem v := by fin_cases v <;> decide


-- @@ L89-96 verbatim
/-- The exact residual incidence representative of class 7. -/
def residualRepresentative07 : OctagonIncidence where
  targets := ![
    {1, 2, 3, 4}, {0, 2, 3, 5}, {3, 4, 6, 7}, {2, 5, 6, 7},
    {1, 3, 5, 6}, {0, 2, 4, 7}, {0, 1, 5, 7}, {0, 1, 4, 6}
  ]
  card_targets v := by fin_cases v <;> decide
  centre_not_mem v := by fin_cases v <;> decide


-- @@ L98-105 verbatim
/-- The exact residual incidence representative of class 8. -/
def residualRepresentative08 : OctagonIncidence where
  targets := ![
    {1, 2, 3, 4}, {0, 2, 3, 5}, {3, 4, 5, 6}, {2, 4, 5, 7},
    {0, 5, 6, 7}, {1, 4, 6, 7}, {0, 1, 3, 7}, {0, 1, 2, 6}
  ]
  card_targets v := by fin_cases v <;> decide
  centre_not_mem v := by fin_cases v <;> decide


-- @@ L107-114 verbatim
/-- The exact residual incidence representative of class 9. -/
def residualRepresentative09 : OctagonIncidence where
  targets := ![
    {1, 2, 3, 4}, {0, 2, 3, 5}, {3, 4, 5, 6}, {2, 4, 5, 7},
    {0, 5, 6, 7}, {1, 4, 6, 7}, {0, 1, 2, 7}, {0, 1, 3, 6}
  ]
  card_targets v := by fin_cases v <;> decide
  centre_not_mem v := by fin_cases v <;> decide


-- @@ L116-123 verbatim
/-- The exact residual incidence representative of class 10. -/
def residualRepresentative10 : OctagonIncidence where
  targets := ![
    {1, 2, 3, 4}, {0, 2, 3, 5}, {3, 4, 5, 6}, {2, 4, 5, 7},
    {1, 5, 6, 7}, {0, 4, 6, 7}, {0, 1, 3, 7}, {0, 1, 2, 6}
  ]
  card_targets v := by fin_cases v <;> decide
  centre_not_mem v := by fin_cases v <;> decide


-- @@ L125-132 verbatim
/-- The exact residual incidence representative of class 11. -/
def residualRepresentative11 : OctagonIncidence where
  targets := ![
    {1, 2, 3, 4}, {0, 2, 5, 6}, {3, 4, 5, 6}, {0, 4, 5, 7},
    {1, 2, 5, 7}, {1, 3, 6, 7}, {0, 2, 3, 7}, {0, 1, 4, 6}
  ]
  card_targets v := by fin_cases v <;> decide
  centre_not_mem v := by fin_cases v <;> decide


-- @@ L134-141 verbatim
/-- The exact residual incidence representative of class 12. -/
def residualRepresentative12 : OctagonIncidence where
  targets := ![
    {1, 2, 3, 4}, {0, 5, 6, 7}, {1, 3, 5, 6}, {1, 4, 5, 7},
    {1, 2, 6, 7}, {0, 2, 4, 7}, {0, 3, 4, 5}, {0, 2, 3, 6}
  ]
  card_targets v := by fin_cases v <;> decide
  centre_not_mem v := by fin_cases v <;> decide


-- @@ L143-150 verbatim
/-- The thirteen residual representatives as one finite family. -/
def residualRepresentative : Fin 13 → OctagonIncidence := ![
  residualRepresentative00, residualRepresentative01, residualRepresentative02,
  residualRepresentative03, residualRepresentative04, residualRepresentative05,
  residualRepresentative06, residualRepresentative07, residualRepresentative08,
  residualRepresentative09, residualRepresentative10, residualRepresentative11,
  residualRepresentative12
]


-- @@ L152-152 verbatim
end Erdos97Octagon
