import Veles.Cert9


-- @@ L3-4 verbatim
/-! End-to-end test of the certificate pipeline on S(3,4,9), which fails divisibility, with
controls that must be rejected by the kernel. -/


-- @@ L6-6 verbatim
open Veles.Checker Veles.Cover Veles.CertKit


-- @@ L8-8 verbatim
namespace Veles.Tests


-- @@ L10-11 verbatim
theorem no_S_3_4_9 : IsEmpty (SteinerSystems.SteinerSystem 3 4 9) :=
  isEmpty_steiner_of_noExt rfl Veles.Cert9.noExt_empty


-- @@ L13-14 verbatim
/-- Control: swap two entries of the second permutation; the reduction must fail. -/
def badPerms : Ctx := { Veles.Cert9.T0.ctx with perms := [[0,1,2,3,4,5,6,7,8], [0,1,2,7,3,4,5,6,8]] ++ Veles.Cert9.T0.ctx.perms.drop 2 }


-- @@ L16-18 verbatim
theorem control_bad_perm :
    (node badPerms 1000000 Veles.Cert9.T0.root ⟨Veles.Cert9.T0.words, 0, 0⟩).isSome = false := by
  decide +kernel


-- @@ L20-23 verbatim
/-- Control: a stream cut short is rejected. -/
theorem control_short_stream :
    (node Veles.Cert9.T0.ctx 1000000 Veles.Cert9.T0.root ⟨[], 0, 0⟩).isSome = false := by
  decide +kernel


-- @@ L25-28 verbatim
/-- Control: replaying tree 0's stream from a different state (tree 1's root) is rejected. -/
theorem control_wrong_state :
    (node Veles.Cert9.T0.ctx 1000000 Veles.Cert9.T1.root ⟨Veles.Cert9.T0.words, 0, 0⟩).isSome = false := by
  decide +kernel


-- @@ L30-30 verbatim
end Veles.Tests


-- @@ L32-32 verbatim
#print axioms Veles.Tests.no_S_3_4_9
