import Mathlib


-- @@ L3-3 verbatim
set_option autoImplicit false


-- @@ L5-5 verbatim
open Module


-- @@ L7-7 verbatim
namespace TaylorWiles


-- @@ L9-9 verbatim
variable {k : Type*} [Field k]


-- @@ L11-11 verbatim
local notation "M₂ " k => Matrix (Fin 2) (Fin 2) k


-- @@ L13-14 verbatim
noncomputable def adAction (M : M₂ k) : Module.End k (M₂ k) :=
  LinearMap.mulLeft k M - LinearMap.mulRight k M


-- @@ L16-16 verbatim
@[simp] lemma adAction_apply (M X : M₂ k) : adAction M X = M * X - X * M := rfl


-- @@ L18-18 verbatim
def disc (M : M₂ k) : k := M.trace ^ 2 - 4 * M.det


-- @@ L20-23 verbatim
variable (k) in

noncomputable def traceZero : Submodule k (M₂ k) :=
  LinearMap.ker (Matrix.traceLinearMap (Fin 2) k k)


-- @@ L25-26 verbatim
@[simp] lemma mem_traceZero_iff {X : M₂ k} : X ∈ traceZero k ↔ X.trace = 0 :=
  Iff.rfl


-- @@ L28-28 verbatim
end TaylorWiles
