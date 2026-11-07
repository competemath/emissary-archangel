/-
  EvmAsm.Codegen.Programs.TxSigningHashSpecSetup

  Prologue phases for K145 `tx_signing_hash` Spec (#12038): nonempty-length
  fallthrough, the total outer-RLP list-header parse (short AND long), and the
  `rlp_list_nth_item` ABI setup.  Split out of TxSigningHashSpecSuccess to stay
  under the Codegen/Programs file-size cap.
-/

import EvmAsm.Codegen.Programs.TxSigningHashSpecBodyLate
import EvmAsm.Codegen.Programs.TxSigningHashSpecPrefix


-- @@ L13-13 verbatim
namespace EvmAsm.Codegen.TxSigningHashSpec


-- @@ L15-15 verbatim
open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

-- @@ L16-16 verbatim
open EvmAsm.Codegen

-- @@ L17-17 verbatim
open EvmAsm.Codegen.TxSigningHashResidual

-- @@ L18-18 verbatim
open EvmAsm.Codegen.Proofs

-- @@ L19-19 verbatim
open EvmAsm.Stateless.SpecRef

-- @@ L20-20 verbatim
open EvmAsm.Rv64.Tactics


-- @@ L22-22 verbatim
/-! ## Setup → nonempty fallthrough (`H+36 → H+72`) -/


-- @@ L24-78 expanded
/-- Nonempty `len` (`a1 ≠ 0`) after setup + type-prefix store. -/
theorem tshSetupThenNonempty_spec (a0 a1 a2 a3 a4 v5 v8 v9 v18 v19 v20 wordOld : Word)
    (halign : alignToDword TshBuf = TshBuf) (hvalid : isValidByteAccess TshBuf = true)
    (hlen : a1 ≠ 0) :
    cpsTripleWithin (5 + 3 + 1) (H + 36) (H + 72) fullCode
      ((.x10 ↦ᵣ a0) **
        (.x11 ↦ᵣ a1) **
          (.x12 ↦ᵣ a2) **
            (.x13 ↦ᵣ a3) **
              (.x14 ↦ᵣ a4) **
                (.x5 ↦ᵣ v5) **
                  (.x8 ↦ᵣ v8) **
                    (.x9 ↦ᵣ v9) **
                      (.x18 ↦ᵣ v18) **
                        (.x19 ↦ᵣ v19) **
                          (.x20 ↦ᵣ v20) ** (.x0 ↦ᵣ (0 : Word)) ** (TshBuf ↦ₘ wordOld))
      ((.x10 ↦ᵣ a0) **
        (.x11 ↦ᵣ a1) **
          (.x12 ↦ᵣ a2) **
            (.x13 ↦ᵣ a3) **
              (.x14 ↦ᵣ a4) **
                (.x5 ↦ᵣ TshBuf) **
                  (.x8 ↦ᵣ a0) **
                    (.x9 ↦ᵣ a1) **
                      (.x18 ↦ᵣ a2) **
                        (.x19 ↦ᵣ a3) **
                          (.x20 ↦ᵣ a4) **
                            (.x0 ↦ᵣ (0 : Word)) **
                              (TshBuf ↦ₘ
                                replaceByte wordOld (byteOffset TshBuf) (a3.truncate 8))) :=
  by
  have hsetup := tshSetupThroughSb_spec a0 a1 a2 a3 a4 v5 v8 v9 v18 v19 v20 wordOld halign hvalid
  have hsetupF :=
    cpsTripleWithin_frameR (.x0 ↦ᵣ (0 : Word))
      (by
        repeat
          first
          | apply pcFree_sepConj
          | exact pcFree_regIs
          | exact pcFree_regOwn
          | exact pcFree_memIs
          | exact pcFree_memOwn
          | exact pcFree_emp
          | exact pcFree_pure
          | exact pcFree_instrAt
          | exact bytesRegion_pcFree _ _
          | exact pcFree_stackFree _ _
          | exact pcFree_dwordsIs _ _
          | exact pcFree_regsAt _ _
          | exact pcFree_frameSlotsOwn _ _
          | exact pcFree_frameSlotsSaved _ _ _
          | exact pcFree_regFileIs _)
      hsetup
  have hsetupW :
    cpsTripleWithin (5 + 3) (H + 36) (H + 68) fullCode
      ((.x10 ↦ᵣ a0) **
        (.x11 ↦ᵣ a1) **
          (.x12 ↦ᵣ a2) **
            (.x13 ↦ᵣ a3) **
              (.x14 ↦ᵣ a4) **
                (.x5 ↦ᵣ v5) **
                  (.x8 ↦ᵣ v8) **
                    (.x9 ↦ᵣ v9) **
                      (.x18 ↦ᵣ v18) **
                        (.x19 ↦ᵣ v19) **
                          (.x20 ↦ᵣ v20) ** (.x0 ↦ᵣ (0 : Word)) ** (TshBuf ↦ₘ wordOld))
      ((.x10 ↦ᵣ a0) **
        (.x11 ↦ᵣ a1) **
          (.x12 ↦ᵣ a2) **
            (.x13 ↦ᵣ a3) **
              (.x14 ↦ᵣ a4) **
                (.x5 ↦ᵣ TshBuf) **
                  (.x8 ↦ᵣ a0) **
                    (.x9 ↦ᵣ a1) **
                      (.x18 ↦ᵣ a2) **
                        (.x19 ↦ᵣ a3) **
                          (.x20 ↦ᵣ a4) **
                            (.x0 ↦ᵣ (0 : Word)) **
                              (TshBuf ↦ₘ
                                replaceByte wordOld (byteOffset TshBuf) (a3.truncate 8))) :=
    by
    refine
      cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hsetupF
  have hnt := tshEmptyLenBeq_ntaken a1 hlen
  have hntF :=
    cpsTripleWithin_frameR
      ((.x10 ↦ᵣ a0) **
        (.x11 ↦ᵣ a1) **
          (.x12 ↦ᵣ a2) **
            (.x13 ↦ᵣ a3) **
              (.x14 ↦ᵣ a4) **
                (.x5 ↦ᵣ TshBuf) **
                  (.x8 ↦ᵣ a0) **
                    (.x18 ↦ᵣ a2) **
                      (.x19 ↦ᵣ a3) **
                        (.x20 ↦ᵣ a4) **
                          (TshBuf ↦ₘ replaceByte wordOld (byteOffset TshBuf) (a3.truncate 8)))
      (by
        repeat
          first
          | apply pcFree_sepConj
          | exact pcFree_regIs
          | exact pcFree_regOwn
          | exact pcFree_memIs
          | exact pcFree_memOwn
          | exact pcFree_emp
          | exact pcFree_pure
          | exact pcFree_instrAt
          | exact bytesRegion_pcFree _ _
          | exact pcFree_stackFree _ _
          | exact pcFree_dwordsIs _ _
          | exact pcFree_regsAt _ _
          | exact pcFree_frameSlotsOwn _ _
          | exact pcFree_frameSlotsSaved _ _ _
          | exact pcFree_regFileIs _)
      hnt
  have hntW :
    cpsTripleWithin 1 (H + 68) (H + 72) fullCode
      ((.x10 ↦ᵣ a0) **
        (.x11 ↦ᵣ a1) **
          (.x12 ↦ᵣ a2) **
            (.x13 ↦ᵣ a3) **
              (.x14 ↦ᵣ a4) **
                (.x5 ↦ᵣ TshBuf) **
                  (.x8 ↦ᵣ a0) **
                    (.x9 ↦ᵣ a1) **
                      (.x18 ↦ᵣ a2) **
                        (.x19 ↦ᵣ a3) **
                          (.x20 ↦ᵣ a4) **
                            (.x0 ↦ᵣ (0 : Word)) **
                              (TshBuf ↦ₘ replaceByte wordOld (byteOffset TshBuf) (a3.truncate 8)))
      ((.x10 ↦ᵣ a0) **
        (.x11 ↦ᵣ a1) **
          (.x12 ↦ᵣ a2) **
            (.x13 ↦ᵣ a3) **
              (.x14 ↦ᵣ a4) **
                (.x5 ↦ᵣ TshBuf) **
                  (.x8 ↦ᵣ a0) **
                    (.x9 ↦ᵣ a1) **
                      (.x18 ↦ᵣ a2) **
                        (.x19 ↦ᵣ a3) **
                          (.x20 ↦ᵣ a4) **
                            (.x0 ↦ᵣ (0 : Word)) **
                              (TshBuf ↦ₘ
                                replaceByte wordOld (byteOffset TshBuf) (a3.truncate 8))) :=
    by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hntF
  exact cpsTripleWithin_seq_same_cr hsetupW hntW


-- @@ L80-84 verbatim
/-! ## Setup → outer-list header (`H+36 → H+108`)

    Nonempty length + any RLP list header (`0xc0 ≤ hdr ≤ 0xff`, short and
    long alike).  Carries the input `bytesRegion` and leaves
    `s5 := tshHdrLen input h0`. -/


-- @@ L86-162 expanded
theorem tshSetupThroughHdrAny_spec (a0 a1 a2 a3 a4 v5 v6 v8 v9 v18 v19 v20 v21 wordOld : Word)
    (input : List (BitVec 8)) (halignBuf : alignToDword TshBuf = TshBuf)
    (hvalidBuf : isValidByteAccess TshBuf = true) (hlen : a1 ≠ 0) (h0 : 0 < input.length)
    (halignIn : a0.toNat % 8 = 0) (hoverIn : a0.toNat < 2 ^ 64)
    (hvalidIn : isValidByteAccess a0 = true)
    (hge : ¬BitVec.ult (tshHdrByte input h0) (192 : Word)) :
    cpsTripleWithin (5 + 3 + 1 + 8) (H + 36) (H + 108) fullCode
      ((.x10 ↦ᵣ a0) **
        (.x11 ↦ᵣ a1) **
          (.x12 ↦ᵣ a2) **
            (.x13 ↦ᵣ a3) **
              (.x14 ↦ᵣ a4) **
                (.x5 ↦ᵣ v5) **
                  (.x6 ↦ᵣ v6) **
                    (.x8 ↦ᵣ v8) **
                      (.x9 ↦ᵣ v9) **
                        (.x18 ↦ᵣ v18) **
                          (.x19 ↦ᵣ v19) **
                            (.x20 ↦ᵣ v20) **
                              (.x21 ↦ᵣ v21) **
                                (.x0 ↦ᵣ (0 : Word)) ** (TshBuf ↦ₘ wordOld) ** bytesRegion a0 input)
      ((.x10 ↦ᵣ a0) **
        (.x11 ↦ᵣ a1) **
          (.x12 ↦ᵣ a2) **
            (.x13 ↦ᵣ a3) **
              (.x14 ↦ᵣ a4) **
                (.x5 ↦ᵣ tshHdrByte input h0) **
                  (.x6 ↦ᵣ (248 : Word)) **
                    (.x8 ↦ᵣ a0) **
                      (.x9 ↦ᵣ a1) **
                        (.x18 ↦ᵣ a2) **
                          (.x19 ↦ᵣ a3) **
                            (.x20 ↦ᵣ a4) **
                              (.x21 ↦ᵣ tshHdrLen input h0) **
                                (.x0 ↦ᵣ (0 : Word)) **
                                  (TshBuf ↦ₘ
                                      replaceByte wordOld (byteOffset TshBuf) (a3.truncate 8)) **
                                    bytesRegion a0 input) :=
  by
  have hne :=
    tshSetupThenNonempty_spec a0 a1 a2 a3 a4 v5 v8 v9 v18 v19 v20 wordOld halignBuf hvalidBuf hlen
  have hneF :=
    cpsTripleWithin_frameR ((.x6 ↦ᵣ v6) ** (.x21 ↦ᵣ v21) ** bytesRegion a0 input)
      (by
        repeat
          first
          | apply pcFree_sepConj
          | exact pcFree_regIs
          | exact bytesRegion_pcFree _ _)
      hne
  have hneW :
    cpsTripleWithin (5 + 3 + 1) (H + 36) (H + 72) fullCode
      ((.x10 ↦ᵣ a0) **
        (.x11 ↦ᵣ a1) **
          (.x12 ↦ᵣ a2) **
            (.x13 ↦ᵣ a3) **
              (.x14 ↦ᵣ a4) **
                (.x5 ↦ᵣ v5) **
                  (.x6 ↦ᵣ v6) **
                    (.x8 ↦ᵣ v8) **
                      (.x9 ↦ᵣ v9) **
                        (.x18 ↦ᵣ v18) **
                          (.x19 ↦ᵣ v19) **
                            (.x20 ↦ᵣ v20) **
                              (.x21 ↦ᵣ v21) **
                                (.x0 ↦ᵣ (0 : Word)) ** (TshBuf ↦ₘ wordOld) ** bytesRegion a0 input)
      ((.x10 ↦ᵣ a0) **
        (.x11 ↦ᵣ a1) **
          (.x12 ↦ᵣ a2) **
            (.x13 ↦ᵣ a3) **
              (.x14 ↦ᵣ a4) **
                (.x5 ↦ᵣ TshBuf) **
                  (.x6 ↦ᵣ v6) **
                    (.x8 ↦ᵣ a0) **
                      (.x9 ↦ᵣ a1) **
                        (.x18 ↦ᵣ a2) **
                          (.x19 ↦ᵣ a3) **
                            (.x20 ↦ᵣ a4) **
                              (.x21 ↦ᵣ v21) **
                                (.x0 ↦ᵣ (0 : Word)) **
                                  (TshBuf ↦ₘ
                                      replaceByte wordOld (byteOffset TshBuf) (a3.truncate 8)) **
                                    bytesRegion a0 input) :=
    by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hneF
  have hhdr := tshHdrParseAny_spec a0 TshBuf v6 v21 input h0 halignIn hoverIn hvalidIn hge
  have hhdrF :=
    cpsTripleWithin_frameR
      ((.x10 ↦ᵣ a0) **
        (.x11 ↦ᵣ a1) **
          (.x12 ↦ᵣ a2) **
            (.x13 ↦ᵣ a3) **
              (.x14 ↦ᵣ a4) **
                (.x9 ↦ᵣ a1) **
                  (.x18 ↦ᵣ a2) **
                    (.x19 ↦ᵣ a3) **
                      (.x20 ↦ᵣ a4) **
                        (.x0 ↦ᵣ (0 : Word)) **
                          (TshBuf ↦ₘ replaceByte wordOld (byteOffset TshBuf) (a3.truncate 8)))
      (by
        repeat
          first
          | apply pcFree_sepConj
          | exact pcFree_regIs
          | exact pcFree_regOwn
          | exact pcFree_memIs
          | exact pcFree_memOwn
          | exact pcFree_emp
          | exact pcFree_pure
          | exact pcFree_instrAt
          | exact bytesRegion_pcFree _ _
          | exact pcFree_stackFree _ _
          | exact pcFree_dwordsIs _ _
          | exact pcFree_regsAt _ _
          | exact pcFree_frameSlotsOwn _ _
          | exact pcFree_frameSlotsSaved _ _ _
          | exact pcFree_regFileIs _)
      hhdr
  have hhdrW :
    cpsTripleWithin 8 (H + 72) (H + 108) fullCode
      ((.x10 ↦ᵣ a0) **
        (.x11 ↦ᵣ a1) **
          (.x12 ↦ᵣ a2) **
            (.x13 ↦ᵣ a3) **
              (.x14 ↦ᵣ a4) **
                (.x5 ↦ᵣ TshBuf) **
                  (.x6 ↦ᵣ v6) **
                    (.x8 ↦ᵣ a0) **
                      (.x9 ↦ᵣ a1) **
                        (.x18 ↦ᵣ a2) **
                          (.x19 ↦ᵣ a3) **
                            (.x20 ↦ᵣ a4) **
                              (.x21 ↦ᵣ v21) **
                                (.x0 ↦ᵣ (0 : Word)) **
                                  (TshBuf ↦ₘ
                                      replaceByte wordOld (byteOffset TshBuf) (a3.truncate 8)) **
                                    bytesRegion a0 input)
      ((.x10 ↦ᵣ a0) **
        (.x11 ↦ᵣ a1) **
          (.x12 ↦ᵣ a2) **
            (.x13 ↦ᵣ a3) **
              (.x14 ↦ᵣ a4) **
                (.x5 ↦ᵣ tshHdrByte input h0) **
                  (.x6 ↦ᵣ (248 : Word)) **
                    (.x8 ↦ᵣ a0) **
                      (.x9 ↦ᵣ a1) **
                        (.x18 ↦ᵣ a2) **
                          (.x19 ↦ᵣ a3) **
                            (.x20 ↦ᵣ a4) **
                              (.x21 ↦ᵣ tshHdrLen input h0) **
                                (.x0 ↦ᵣ (0 : Word)) **
                                  (TshBuf ↦ₘ
                                      replaceByte wordOld (byteOffset TshBuf) (a3.truncate 8)) **
                                    bytesRegion a0 input) :=
    by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hhdrF
  exact cpsTripleWithin_seq_same_cr hneW hhdrW


-- @@ L164-166 verbatim
/-! ## Post-header → nth ABI setup (`H+108 → H+156`), `nFields ≠ 0`

    Leaves ABI args + scratch pointers ready for `tsh_nth_callWithin`. -/


-- @@ L168-169 verbatim
abbrev tshNthIndexW (nFields : Word) : Word :=
  nFields + signExtend12 (-1 : BitVec 12)


-- @@ L171-298 expanded
/-- From post-header-parse through pointer materialization. Requires `a2 ≠ 0`. -/
theorem tshNthSetupToJal_spec
    (inPtr lenW nFields typePrefix outPtr hdrByte v6 v10 v11 v12 v13 v14 v22 : Word)
    (hnz : nFields ≠ 0) :
    cpsTripleWithin (1 + 1 + 1 + 3 + 6) (H + 108) (H + 156) fullCode
      ((.x8 ↦ᵣ inPtr) **
        (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ nFields) **
            (.x19 ↦ᵣ typePrefix) **
              (.x20 ↦ᵣ outPtr) **
                (.x5 ↦ᵣ hdrByte) **
                  (.x6 ↦ᵣ v6) **
                    (.x10 ↦ᵣ v10) **
                      (.x11 ↦ᵣ v11) **
                        (.x12 ↦ᵣ v12) **
                          (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x22 ↦ᵣ v22) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x8 ↦ᵣ inPtr) **
        (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ nFields) **
            (.x19 ↦ᵣ typePrefix) **
              (.x20 ↦ᵣ outPtr) **
                (.x5 ↦ᵣ tshNthIndexW nFields) **
                  (.x6 ↦ᵣ v6) **
                    (.x10 ↦ᵣ inPtr) **
                      (.x11 ↦ᵣ lenW) **
                        (.x12 ↦ᵣ tshNthIndexW nFields) **
                          (.x13 ↦ᵣ tshNthOffPtr) **
                            (.x14 ↦ᵣ tshNthLenPtr) **
                              (.x22 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) :=
  by
  have hli := tshPayloadOffInit_spec v22
  have hliF :=
    cpsTripleWithin_frameR
      ((.x8 ↦ᵣ inPtr) **
        (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ nFields) **
            (.x19 ↦ᵣ typePrefix) **
              (.x20 ↦ᵣ outPtr) **
                (.x5 ↦ᵣ hdrByte) **
                  (.x6 ↦ᵣ v6) **
                    (.x10 ↦ᵣ v10) **
                      (.x11 ↦ᵣ v11) **
                        (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x0 ↦ᵣ (0 : Word)))
      (by
        repeat
          first
          | apply pcFree_sepConj
          | exact pcFree_regIs
          | exact pcFree_regOwn
          | exact pcFree_memIs
          | exact pcFree_memOwn
          | exact pcFree_emp
          | exact pcFree_pure
          | exact pcFree_instrAt
          | exact bytesRegion_pcFree _ _
          | exact pcFree_stackFree _ _
          | exact pcFree_dwordsIs _ _
          | exact pcFree_regsAt _ _
          | exact pcFree_frameSlotsOwn _ _
          | exact pcFree_frameSlotsSaved _ _ _
          | exact pcFree_regFileIs _)
      hli
  have hliW :
    cpsTripleWithin 1 (H + 108) (H + 112) fullCode
      ((.x8 ↦ᵣ inPtr) **
        (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ nFields) **
            (.x19 ↦ᵣ typePrefix) **
              (.x20 ↦ᵣ outPtr) **
                (.x5 ↦ᵣ hdrByte) **
                  (.x6 ↦ᵣ v6) **
                    (.x10 ↦ᵣ v10) **
                      (.x11 ↦ᵣ v11) **
                        (.x12 ↦ᵣ v12) **
                          (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x22 ↦ᵣ v22) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x8 ↦ᵣ inPtr) **
        (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ nFields) **
            (.x19 ↦ᵣ typePrefix) **
              (.x20 ↦ᵣ outPtr) **
                (.x5 ↦ᵣ hdrByte) **
                  (.x6 ↦ᵣ v6) **
                    (.x10 ↦ᵣ v10) **
                      (.x11 ↦ᵣ v11) **
                        (.x12 ↦ᵣ v12) **
                          (.x13 ↦ᵣ v13) **
                            (.x14 ↦ᵣ v14) ** (.x22 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) :=
    by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hliF
  have hnt := tshNFieldsBeq_ntaken nFields hnz
  have hntF :=
    cpsTripleWithin_frameR
      ((.x8 ↦ᵣ inPtr) **
        (.x9 ↦ᵣ lenW) **
          (.x19 ↦ᵣ typePrefix) **
            (.x20 ↦ᵣ outPtr) **
              (.x5 ↦ᵣ hdrByte) **
                (.x6 ↦ᵣ v6) **
                  (.x10 ↦ᵣ v10) **
                    (.x11 ↦ᵣ v11) **
                      (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x22 ↦ᵣ (0 : Word)))
      (by
        repeat
          first
          | apply pcFree_sepConj
          | exact pcFree_regIs
          | exact pcFree_regOwn
          | exact pcFree_memIs
          | exact pcFree_memOwn
          | exact pcFree_emp
          | exact pcFree_pure
          | exact pcFree_instrAt
          | exact bytesRegion_pcFree _ _
          | exact pcFree_stackFree _ _
          | exact pcFree_dwordsIs _ _
          | exact pcFree_regsAt _ _
          | exact pcFree_frameSlotsOwn _ _
          | exact pcFree_frameSlotsSaved _ _ _
          | exact pcFree_regFileIs _)
      hnt
  have hntW :
    cpsTripleWithin 1 (H + 112) (H + 116) fullCode
      ((.x8 ↦ᵣ inPtr) **
        (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ nFields) **
            (.x19 ↦ᵣ typePrefix) **
              (.x20 ↦ᵣ outPtr) **
                (.x5 ↦ᵣ hdrByte) **
                  (.x6 ↦ᵣ v6) **
                    (.x10 ↦ᵣ v10) **
                      (.x11 ↦ᵣ v11) **
                        (.x12 ↦ᵣ v12) **
                          (.x13 ↦ᵣ v13) **
                            (.x14 ↦ᵣ v14) ** (.x22 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x8 ↦ᵣ inPtr) **
        (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ nFields) **
            (.x19 ↦ᵣ typePrefix) **
              (.x20 ↦ᵣ outPtr) **
                (.x5 ↦ᵣ hdrByte) **
                  (.x6 ↦ᵣ v6) **
                    (.x10 ↦ᵣ v10) **
                      (.x11 ↦ᵣ v11) **
                        (.x12 ↦ᵣ v12) **
                          (.x13 ↦ᵣ v13) **
                            (.x14 ↦ᵣ v14) ** (.x22 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) :=
    by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hntF
  have c01 := cpsTripleWithin_seq_same_cr hliW hntW
  have hidx := tshNthIndex_spec nFields hdrByte
  have hidxF :=
    cpsTripleWithin_frameR
      ((.x8 ↦ᵣ inPtr) **
        (.x9 ↦ᵣ lenW) **
          (.x19 ↦ᵣ typePrefix) **
            (.x20 ↦ᵣ outPtr) **
              (.x6 ↦ᵣ v6) **
                (.x10 ↦ᵣ v10) **
                  (.x11 ↦ᵣ v11) **
                    (.x12 ↦ᵣ v12) **
                      (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x22 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      (by
        repeat
          first
          | apply pcFree_sepConj
          | exact pcFree_regIs
          | exact pcFree_regOwn
          | exact pcFree_memIs
          | exact pcFree_memOwn
          | exact pcFree_emp
          | exact pcFree_pure
          | exact pcFree_instrAt
          | exact bytesRegion_pcFree _ _
          | exact pcFree_stackFree _ _
          | exact pcFree_dwordsIs _ _
          | exact pcFree_regsAt _ _
          | exact pcFree_frameSlotsOwn _ _
          | exact pcFree_frameSlotsSaved _ _ _
          | exact pcFree_regFileIs _)
      hidx
  have hidxW :
    cpsTripleWithin 1 (H + 116) (H + 120) fullCode
      ((.x8 ↦ᵣ inPtr) **
        (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ nFields) **
            (.x19 ↦ᵣ typePrefix) **
              (.x20 ↦ᵣ outPtr) **
                (.x5 ↦ᵣ hdrByte) **
                  (.x6 ↦ᵣ v6) **
                    (.x10 ↦ᵣ v10) **
                      (.x11 ↦ᵣ v11) **
                        (.x12 ↦ᵣ v12) **
                          (.x13 ↦ᵣ v13) **
                            (.x14 ↦ᵣ v14) ** (.x22 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x8 ↦ᵣ inPtr) **
        (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ nFields) **
            (.x19 ↦ᵣ typePrefix) **
              (.x20 ↦ᵣ outPtr) **
                (.x5 ↦ᵣ tshNthIndexW nFields) **
                  (.x6 ↦ᵣ v6) **
                    (.x10 ↦ᵣ v10) **
                      (.x11 ↦ᵣ v11) **
                        (.x12 ↦ᵣ v12) **
                          (.x13 ↦ᵣ v13) **
                            (.x14 ↦ᵣ v14) ** (.x22 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) :=
    by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hidxF
  have c012 := cpsTripleWithin_seq_same_cr c01 hidxW
  have hmv := tshNthArgMoves_spec inPtr lenW (tshNthIndexW nFields) v10 v11 v12
  have hmvF :=
    cpsTripleWithin_frameR
      ((.x18 ↦ᵣ nFields) **
        (.x19 ↦ᵣ typePrefix) **
          (.x20 ↦ᵣ outPtr) **
            (.x6 ↦ᵣ v6) **
              (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x22 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      (by
        repeat
          first
          | apply pcFree_sepConj
          | exact pcFree_regIs
          | exact pcFree_regOwn
          | exact pcFree_memIs
          | exact pcFree_memOwn
          | exact pcFree_emp
          | exact pcFree_pure
          | exact pcFree_instrAt
          | exact bytesRegion_pcFree _ _
          | exact pcFree_stackFree _ _
          | exact pcFree_dwordsIs _ _
          | exact pcFree_regsAt _ _
          | exact pcFree_frameSlotsOwn _ _
          | exact pcFree_frameSlotsSaved _ _ _
          | exact pcFree_regFileIs _)
      hmv
  have hmvW :
    cpsTripleWithin 3 (H + 120) (H + 132) fullCode
      ((.x8 ↦ᵣ inPtr) **
        (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ nFields) **
            (.x19 ↦ᵣ typePrefix) **
              (.x20 ↦ᵣ outPtr) **
                (.x5 ↦ᵣ tshNthIndexW nFields) **
                  (.x6 ↦ᵣ v6) **
                    (.x10 ↦ᵣ v10) **
                      (.x11 ↦ᵣ v11) **
                        (.x12 ↦ᵣ v12) **
                          (.x13 ↦ᵣ v13) **
                            (.x14 ↦ᵣ v14) ** (.x22 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x8 ↦ᵣ inPtr) **
        (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ nFields) **
            (.x19 ↦ᵣ typePrefix) **
              (.x20 ↦ᵣ outPtr) **
                (.x5 ↦ᵣ tshNthIndexW nFields) **
                  (.x6 ↦ᵣ v6) **
                    (.x10 ↦ᵣ inPtr) **
                      (.x11 ↦ᵣ lenW) **
                        (.x12 ↦ᵣ tshNthIndexW nFields) **
                          (.x13 ↦ᵣ v13) **
                            (.x14 ↦ᵣ v14) ** (.x22 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) :=
    by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hmvF
  have c0123 := cpsTripleWithin_seq_same_cr c012 hmvW
  have hptr := tshNthPtrs_spec v13 v14
  have hptrF :=
    cpsTripleWithin_frameR
      ((.x8 ↦ᵣ inPtr) **
        (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ nFields) **
            (.x19 ↦ᵣ typePrefix) **
              (.x20 ↦ᵣ outPtr) **
                (.x5 ↦ᵣ tshNthIndexW nFields) **
                  (.x6 ↦ᵣ v6) **
                    (.x10 ↦ᵣ inPtr) **
                      (.x11 ↦ᵣ lenW) **
                        (.x12 ↦ᵣ tshNthIndexW nFields) **
                          (.x22 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      (by
        repeat
          first
          | apply pcFree_sepConj
          | exact pcFree_regIs
          | exact pcFree_regOwn
          | exact pcFree_memIs
          | exact pcFree_memOwn
          | exact pcFree_emp
          | exact pcFree_pure
          | exact pcFree_instrAt
          | exact bytesRegion_pcFree _ _
          | exact pcFree_stackFree _ _
          | exact pcFree_dwordsIs _ _
          | exact pcFree_regsAt _ _
          | exact pcFree_frameSlotsOwn _ _
          | exact pcFree_frameSlotsSaved _ _ _
          | exact pcFree_regFileIs _)
      hptr
  have hptrW :
    cpsTripleWithin 6 (H + 132) (H + 156) fullCode
      ((.x8 ↦ᵣ inPtr) **
        (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ nFields) **
            (.x19 ↦ᵣ typePrefix) **
              (.x20 ↦ᵣ outPtr) **
                (.x5 ↦ᵣ tshNthIndexW nFields) **
                  (.x6 ↦ᵣ v6) **
                    (.x10 ↦ᵣ inPtr) **
                      (.x11 ↦ᵣ lenW) **
                        (.x12 ↦ᵣ tshNthIndexW nFields) **
                          (.x13 ↦ᵣ v13) **
                            (.x14 ↦ᵣ v14) ** (.x22 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x8 ↦ᵣ inPtr) **
        (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ nFields) **
            (.x19 ↦ᵣ typePrefix) **
              (.x20 ↦ᵣ outPtr) **
                (.x5 ↦ᵣ tshNthIndexW nFields) **
                  (.x6 ↦ᵣ v6) **
                    (.x10 ↦ᵣ inPtr) **
                      (.x11 ↦ᵣ lenW) **
                        (.x12 ↦ᵣ tshNthIndexW nFields) **
                          (.x13 ↦ᵣ tshNthOffPtr) **
                            (.x14 ↦ᵣ tshNthLenPtr) **
                              (.x22 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) :=
    by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hptrF
  exact cpsTripleWithin_mono_nSteps (by omega) (cpsTripleWithin_seq_same_cr c0123 hptrW)


-- @@ L300-300 verbatim
/-! ## Glue: setup → header parse → nth ABI setup (`H+36 → H+156`) -/


-- @@ L302-355 expanded
/-- Nonempty short-list path through nth pointer materialization (`nFields ≠ 0`). -/
theorem tshSetupThroughNthSetup_spec (a0 a1 a2 a3 a4 v5 v6 v8 v9 v18 v19 v20 v21 v22 wordOld : Word)
    (input : List (BitVec 8)) (halignBuf : alignToDword TshBuf = TshBuf)
    (hvalidBuf : isValidByteAccess TshBuf = true) (hlen : a1 ≠ 0) (hnz : a2 ≠ 0)
    (h0 : 0 < input.length) (halignIn : a0.toNat % 8 = 0) (hoverIn : a0.toNat < 2 ^ 64)
    (hvalidIn : isValidByteAccess a0 = true)
    (hge : ¬BitVec.ult (tshHdrByte input h0) (192 : Word)) :
    cpsTripleWithin (5 + 3 + 1 + 8 + (1 + 1 + 1 + 3 + 6)) (H + 36) (H + 156) fullCode
      ((.x10 ↦ᵣ a0) **
        (.x11 ↦ᵣ a1) **
          (.x12 ↦ᵣ a2) **
            (.x13 ↦ᵣ a3) **
              (.x14 ↦ᵣ a4) **
                (.x5 ↦ᵣ v5) **
                  (.x6 ↦ᵣ v6) **
                    (.x8 ↦ᵣ v8) **
                      (.x9 ↦ᵣ v9) **
                        (.x18 ↦ᵣ v18) **
                          (.x19 ↦ᵣ v19) **
                            (.x20 ↦ᵣ v20) **
                              (.x21 ↦ᵣ v21) **
                                (.x22 ↦ᵣ v22) **
                                  (.x0 ↦ᵣ (0 : Word)) **
                                    (TshBuf ↦ₘ wordOld) ** bytesRegion a0 input)
      ((.x10 ↦ᵣ a0) **
        (.x11 ↦ᵣ a1) **
          (.x12 ↦ᵣ tshNthIndexW a2) **
            (.x13 ↦ᵣ tshNthOffPtr) **
              (.x14 ↦ᵣ tshNthLenPtr) **
                (.x5 ↦ᵣ tshNthIndexW a2) **
                  (.x6 ↦ᵣ (248 : Word)) **
                    (.x8 ↦ᵣ a0) **
                      (.x9 ↦ᵣ a1) **
                        (.x18 ↦ᵣ a2) **
                          (.x19 ↦ᵣ a3) **
                            (.x20 ↦ᵣ a4) **
                              (.x21 ↦ᵣ tshHdrLen input h0) **
                                (.x22 ↦ᵣ (0 : Word)) **
                                  (.x0 ↦ᵣ (0 : Word)) **
                                    (TshBuf ↦ₘ
                                        replaceByte wordOld (byteOffset TshBuf) (a3.truncate 8)) **
                                      bytesRegion a0 input) :=
  by
  let F : Assertion :=
    (.x21 ↦ᵣ tshHdrLen input h0) **
      (TshBuf ↦ₘ replaceByte wordOld (byteOffset TshBuf) (a3.truncate 8)) ** bytesRegion a0 input
  have hF : F.pcFree := by
    unfold F
    repeat
      first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact bytesRegion_pcFree _ _
  have hhdr :=
    tshSetupThroughHdrAny_spec a0 a1 a2 a3 a4 v5 v6 v8 v9 v18 v19 v20 v21 wordOld input halignBuf
      hvalidBuf hlen h0 halignIn hoverIn hvalidIn hge
  have hhdrF :=
    cpsTripleWithin_frameR (.x22 ↦ᵣ v22)
      (by
        repeat
          first
          | apply pcFree_sepConj
          | exact pcFree_regIs
          | exact pcFree_regOwn
          | exact pcFree_memIs
          | exact pcFree_memOwn
          | exact pcFree_emp
          | exact pcFree_pure
          | exact pcFree_instrAt
          | exact bytesRegion_pcFree _ _
          | exact pcFree_stackFree _ _
          | exact pcFree_dwordsIs _ _
          | exact pcFree_regsAt _ _
          | exact pcFree_frameSlotsOwn _ _
          | exact pcFree_frameSlotsSaved _ _ _
          | exact pcFree_regFileIs _)
      hhdr
  have hn :=
    tshNthSetupToJal_spec a0 a1 a2 a3 a4 (tshHdrByte input h0) (248 : Word) a0 a1 a2 a3 a4 v22 hnz
  have hnF := cpsTripleWithin_frameR F hF hn
  have c :=
    cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by
        -- mid: hdr post ** x22  →  nth pre ** F
        
        simp only [F] at hp ⊢
        xperm_hyp hp)
      hhdrF hnF
  exact
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by
        simp only [F] at hq
        xperm_hyp hq)
      c


-- @@ L358-358 verbatim
end EvmAsm.Codegen.TxSigningHashSpec
