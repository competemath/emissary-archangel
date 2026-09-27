/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/
module

public import LeanPool.Wallace.FullTopology


-- @@ L10-17 verbatim
/-!
# Pulling a character package back along an embedding

This module records a reusable transport principle for the topology construction.  If an
additive group `G` embeds in a group `H` carrying a full character package, and every prescribed
limit point for an embedded injective sequence has a chosen preimage in `G`, then the entire
package pulls back to `G`.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
open Filter Topology


-- @@ L23-23 verbatim
universe u v w


-- @@ L25-25 verbatim
namespace Wallace


-- @@ L27-27 verbatim
noncomputable section


-- @@ L29-29 verbatim
namespace FullCharacterPackage


-- @@ L31-31 verbatim
variable {G : Type u} {H : Type v} [AddCommGroup G] [AddCommGroup H]


-- @@ L33-37 verbatim
/-- The code in an ambient character package corresponding to an injective sequence after it is
mapped along an additive embedding. -/
def embeddedCode (C : FullCharacterPackage H) (e : G →+ H)
    (he : Function.Injective e) (s : InjectiveSequence' G) : C.Code :=
  C.codeEquiv.symm ⟨fun n ↦ e (s.1 n), he.comp s.2⟩


-- @@ L39-81 verbatim
/-- Pull a full character package back along an additive embedding.  The only extra datum needed
is a preimage, in `G`, of the ambient package's prescribed limit point for every embedded
injective sequence. -/
def pullback
    (C : FullCharacterPackage H) (e : G →+ H) (he : Function.Injective e)
    (limitPreimage : InjectiveSequence' G → G)
    (map_limitPreimage : ∀ s,
      e (limitPreimage s) = C.limitPoint (C.embeddedCode e he s)) :
    FullCharacterPackage G where
  Code := InjectiveSequence' G
  codeEquiv := Equiv.refl _
  subsequence s := C.subsequence (C.embeddedCode e he s)
  subsequence_strictMono s := C.subsequence_strictMono (C.embeddedCode e he s)
  ultrafilter s := C.ultrafilter (C.embeddedCode e he s)
  ultrafilter_free s := C.ultrafilter_free (C.embeddedCode e he s)
  limitPoint := limitPreimage
  limitPoint_ne_zero s := by
    intro hs
    have hambient := C.limitPoint_ne_zero (C.embeddedCode e he s)
    apply hambient
    rw [← map_limitPreimage s, hs, map_zero]
  CharacterIndex := C.CharacterIndex
  character j := (C.character j).comp e
  character_detects x hx := by
    have hex : e x ≠ 0 := by
      intro hzero
      exact hx (he (by simpa using hzero))
    obtain ⟨j, hj⟩ := C.character_detects (e x) hex
    exact ⟨j, hj⟩
  character_limit s j := by
    have hambient := C.character_limit (C.embeddedCode e he s) j
    have hcode :
        (C.codeEquiv (C.embeddedCode e he s)).1 = fun n ↦ e (s.1 n) := by
      exact congrArg Subtype.val (C.codeEquiv.apply_symm_apply
        ⟨fun n ↦ e (s.1 n), he.comp s.2⟩)
    rw [hcode] at hambient
    change Tendsto
      (fun n ↦ C.character j
        (e (s.1 (C.subsequence (C.embeddedCode e he s) n))))
      (C.ultrafilter (C.embeddedCode e he s))
      (nhds (C.character j (e (limitPreimage s))))
    rw [map_limitPreimage s]
    exact hambient


-- @@ L83-89 verbatim
/-- Pulling a character package back along an additive equivalence requires no separate choice
of limit-point preimages. -/
def comapAddEquiv (C : FullCharacterPackage H) (e : G ≃+ H) :
    FullCharacterPackage G :=
  C.pullback e.toAddMonoidHom e.injective
    (fun s ↦ e.symm (C.limitPoint (C.embeddedCode e.toAddMonoidHom e.injective s)))
    (fun _ ↦ e.apply_symm_apply _)


-- @@ L91-91 verbatim
end FullCharacterPackage


-- @@ L93-93 verbatim
end


-- @@ L95-95 verbatim
end Wallace
