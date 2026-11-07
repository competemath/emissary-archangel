/-
  EvmAsm.Codegen.GuestAddrs

  GENERATED — do not edit by hand.
  `python3 scripts/asm_to_program.py guest-addrs` regenerates this from
  `scripts/asm-fixtures/symbol-addresses.tsv` (the linker-facts table of
  bead evm-asm-4ch8f.6). One `Nat` constant per guest symbol that a
  converted `_prog` references — function entries (the `pc` base for a
  `la`/`jal` immediate) and `la`/cross-`jal` targets (data arenas, tables,
  callee entries).

  This is the SINGLE file that churns on guest layout drift: the per-
  function `_prog` defs reference these constants by name via
  `AsmReloc.{laHi,laLo,jalOff}`, so a `.text`/`.data` size change only
  requires regenerating the TSV + this file, never the 100s of `_prog`s.
  Guarded by `scripts/check-asm-to-program.sh` (regenerate + diff).

  Addresses are LINK_DEPENDENT (move on any layout change); the trusted
  arbiter that they are correct is the whole-guest byte-identity gate.
-/

module


-- @@ L24-24 verbatim
@[expose] public section

-- @@ L25-25 verbatim
namespace EvmAsm.Codegen.GuestAddrs


-- @@ L27-27 verbatim
def a77ra_cmp : Nat := 0xaa843a38

-- @@ L28-28 verbatim
def a77ra_secp256k1_half_n : Nat := 0xa0b00b7a

-- @@ L29-29 verbatim
def a77ra_secp256k1_n : Nat := 0xa0b00b5a

-- @@ L30-30 verbatim
def aa_value_len : Nat := 0xab704738

-- @@ L31-31 verbatim
def aa_value_scratch : Nat := 0xab704760

-- @@ L32-32 verbatim
def aab_bal32 : Nat := 0xa4386900

-- @@ L33-33 verbatim
def aab_bal_len : Nat := 0xa43868e8

-- @@ L34-34 verbatim
def aab_bal_off : Nat := 0xa43868e0

-- @@ L35-35 verbatim
def aab_enc : Nat := 0xa4386920

-- @@ L36-36 verbatim
def aab_enc_len : Nat := 0xa43868f0

-- @@ L37-37 verbatim
def aahsr_state_root : Nat := 0xab704380

-- @@ L38-38 verbatim
def ac2_inner_digest : Nat := 0xab7045c0

-- @@ L39-39 verbatim
def ac2_outer_digest : Nat := 0xab7045e0

-- @@ L40-40 verbatim
def ac2_preimage : Nat := 0xab704600

-- @@ L41-41 verbatim
def ac_buffer : Nat := 0xab704658

-- @@ L42-42 verbatim
def ac_digest : Nat := 0xab704680

-- @@ L43-43 verbatim
def ac_nonce_be : Nat := 0xab704678

-- @@ L44-44 verbatim
def access_list_count : Nat := 0x80027c1c

-- @@ L45-45 verbatim
def account_add_balance : Nat := 0x80005ea4

-- @@ L46-46 verbatim
def account_apply_storage_slot : Nat := 0x8000d954

-- @@ L47-47 verbatim
def account_apply_storage_slot_acc : Nat := 0x8000da7c

-- @@ L48-48 verbatim
def account_at_address : Nat := 0x80006898

-- @@ L49-49 verbatim
def account_at_header_state_root : Nat := 0x8001b1f0

-- @@ L50-50 verbatim
def account_at_header_state_root_tracked : Nat := 0x80025e0c

-- @@ L51-51 verbatim
def account_builder_block_code_hash : Nat := 0xb8db9908

-- @@ L52-52 verbatim
def account_builder_diag_balance_pairs : Nat := 0xb8db9928

-- @@ L53-53 verbatim
def account_builder_diag_nonce_pairs : Nat := 0xb8db9aa8

-- @@ L54-54 verbatim
def account_builder_post_code_hash : Nat := 0xb8db98e8

-- @@ L55-55 verbatim
def account_builder_pre_account : Nat := 0xb8db9880

-- @@ L56-56 verbatim
def account_charge_gas_pre_exec : Nat := 0x800272c4

-- @@ L57-57 verbatim
def account_decode : Nat := 0x800065e0

-- @@ L58-58 verbatim
def account_exists_at_header_state_root : Nat := 0x80030aa4

-- @@ L59-59 verbatim
def account_extract_balance : Nat := 0x8001b72c

-- @@ L60-60 verbatim
def account_extract_nonce : Nat := 0x8001b7b8

-- @@ L61-61 verbatim
def account_is_eip161_empty : Nat := 0x8000de6c

-- @@ L62-62 verbatim
def account_is_empty_at_header_state_root : Nat := 0x80030b7c

-- @@ L63-63 verbatim
def account_read_record : Nat := 0x80025ce8

-- @@ L64-64 verbatim
def account_reads_count : Nat := 0xb9dfdb80

-- @@ L65-65 verbatim
def account_reads_overflow : Nat := 0xb9dfdb88

-- @@ L66-66 verbatim
def account_resolve_execution_state : Nat := 0x80023044

-- @@ L67-67 verbatim
def account_resolve_pre_state : Nat := 0x80022e6c

-- @@ L68-68 verbatim
def account_set_storage_root : Nat := 0x8000d8a8

-- @@ L69-69 verbatim
def account_set_uint_field : Nat := 0x8000dda8

-- @@ L70-70 verbatim
def account_state_created : Nat := 0xbb07ee60

-- @@ L71-71 verbatim
def account_state_created_contains : Nat := 0x80031a98

-- @@ L72-72 verbatim
def account_state_created_count : Nat := 0xba702828

-- @@ L73-73 verbatim
def account_state_delete : Nat := 0xbb0bee60

-- @@ L74-74 verbatim
def account_state_delete_count : Nat := 0xba702830

-- @@ L75-75 verbatim
def account_state_overflow : Nat := 0xba702838

-- @@ L76-76 verbatim
def account_write_record : Nat := 0x800212dc

-- @@ L77-77 verbatim
def account_writes_apply_deletes : Nat := 0x800222e4

-- @@ L78-78 verbatim
def account_writes_auth_block : Nat := 0x800219f4

-- @@ L79-79 verbatim
def account_writes_auth_current : Nat := 0x80021884

-- @@ L80-80 verbatim
def account_writes_block_upsert : Nat := 0x80022120

-- @@ L81-81 verbatim
def account_writes_commit_pending : Nat := 0x80022574

-- @@ L82-82 verbatim
def account_writes_count : Nat := 0xb9deda98

-- @@ L83-83 verbatim
def account_writes_created_contains : Nat := 0x80021b00

-- @@ L84-84 verbatim
def account_writes_emit_builder_tx : Nat := 0x800226b8

-- @@ L85-85 verbatim
def account_writes_incorporate_tx : Nat := 0x80022bbc

-- @@ L86-86 verbatim
def account_writes_is_absent : Nat := 0x800225c4

-- @@ L87-87 verbatim
def account_writes_latest_balance : Nat := 0x8002151c

-- @@ L88-88 verbatim
def account_writes_latest_balance_block : Nat := 0x8002165c

-- @@ L89-89 verbatim
def account_writes_latest_nonce_block : Nat := 0x80021724

-- @@ L90-90 verbatim
def account_writes_latest_nonce_tx : Nat := 0x800217d4

-- @@ L91-91 verbatim
def account_writes_lookup_current : Nat := 0x80021ba4

-- @@ L92-92 verbatim
def account_writes_overflow : Nat := 0xb9dedaa0

-- @@ L93-93 verbatim
def account_writes_restore_frame : Nat := 0x80022d68

-- @@ L94-94 verbatim
def account_writes_tombstone_balance_zero : Nat := 0x80021d30

-- @@ L95-95 verbatim
def account_writes_undo_count : Nat := 0xb9dedab8

-- @@ L96-96 verbatim
def account_writes_undo_push : Nat := 0x80022c48

-- @@ L97-97 verbatim
def acpg_gas_fee : Nat := 0xaa843c40

-- @@ L98-98 verbatim
def ad_length : Nat := 0xab704730

-- @@ L99-99 verbatim
def ad_offset : Nat := 0xab704728

-- @@ L100-100 verbatim
def address_compute_create : Nat := 0x8002ae98

-- @@ L101-101 verbatim
def address_compute_create2 : Nat := 0x8002b01c

-- @@ L102-102 verbatim
def address_from_pubkey : Nat := 0x8002ae34

-- @@ L103-103 verbatim
def aer_bd_len : Nat := 0xb9e024e8

-- @@ L104-104 verbatim
def aer_bd_ptr : Nat := 0xb9e024e0

-- @@ L105-105 verbatim
def aer_be_len : Nat := 0xb9e024f8

-- @@ L106-106 verbatim
def aer_be_ptr : Nat := 0xb9e024f0

-- @@ L107-107 verbatim
def aex_acct_struct : Nat := 0xba5a1f20

-- @@ L108-108 verbatim
def aex_predicate : Nat := 0xba5a2028

-- @@ L109-109 verbatim
def aex_state_root : Nat := 0xba5a1f00

-- @@ L110-110 verbatim
def afp_digest : Nat := 0xaa8453a0

-- @@ L111-111 verbatim
def aie_acct_struct : Nat := 0xba5a1fc0

-- @@ L112-112 verbatim
def aie_empty_code_hash : Nat := 0xa0b00c80

-- @@ L113-113 verbatim
def aie_length : Nat := 0xab708ea0

-- @@ L114-114 verbatim
def aie_offset : Nat := 0xab708e98

-- @@ L115-115 verbatim
def aie_predicate : Nat := 0xba5a2030

-- @@ L116-116 verbatim
def aie_state_root : Nat := 0xba5a1fa0

-- @@ L117-117 verbatim
def alc_entry_length : Nat := 0xab706b00

-- @@ L118-118 verbatim
def alc_entry_offset : Nat := 0xab706af8

-- @@ L119-119 verbatim
def alc_keys_length : Nat := 0xab706b10

-- @@ L120-120 verbatim
def alc_keys_offset : Nat := 0xab706b08

-- @@ L121-121 verbatim
def alc_scratch : Nat := 0xab706af0

-- @@ L122-122 verbatim
def amsterdam_blob_gas_price_u256 : Nat := 0x8000b34c

-- @@ L123-123 verbatim
def aps_empty_root : Nat := 0xa0b00aa8

-- @@ L124-124 verbatim
def aps_len : Nat := 0xa55b7340

-- @@ L125-125 verbatim
def aps_newsroot : Nat := 0xa55b7360

-- @@ L126-126 verbatim
def aps_off : Nat := 0xa55b7338

-- @@ L127-127 verbatim
def aps_path : Nat := 0xa55b7380

-- @@ L128-128 verbatim
def aps_witness_len : Nat := 0xa55b7350

-- @@ L129-129 verbatim
def aps_witness_ptr : Nat := 0xa55b7348

-- @@ L130-130 verbatim
def asr_ref : Nat := 0xa55b7310

-- @@ L131-131 verbatim
def assemble_execution_requests : Nat := 0x8005420c

-- @@ L132-132 verbatim
def b1_sender_table_find : Nat := 0x8002ad78

-- @@ L133-133 verbatim
def b1an_auth_count : Nat := 0xb8a1e478

-- @@ L134-134 verbatim
def b1an_auth_len : Nat := 0xb8a1e460

-- @@ L135-135 verbatim
def b1an_auth_off : Nat := 0xb8a1e458

-- @@ L136-136 verbatim
def b1an_authority : Nat := 0xb8a1e4a8

-- @@ L137-137 verbatim
def b1an_field : Nat := 0xb8a1e498

-- @@ L138-138 verbatim
def b1an_item_len : Nat := 0xb8a1e490

-- @@ L139-139 verbatim
def b1an_item_off : Nat := 0xb8a1e488

-- @@ L140-140 verbatim
def b1an_recover_scratch : Nat := 0xb8a1e4c8

-- @@ L141-141 verbatim
def b1an_signed_nonce : Nat := 0xb8a1e4a0

-- @@ L142-142 verbatim
def b1an_target_len : Nat := 0xb8a1e470

-- @@ L143-143 verbatim
def b1an_target_off : Nat := 0xb8a1e468

-- @@ L144-144 verbatim
def baacd_fail_code : Nat := 0xab708e90

-- @@ L145-145 verbatim
def baacd_is_empty : Nat := 0xab708e88

-- @@ L146-146 verbatim
def baacd_value_len : Nat := 0xab708e80

-- @@ L147-147 verbatim
def baap_code_item_ptr : Nat := 0xab706e78

-- @@ L148-148 verbatim
def baap_delete_single_leaf_storage : Nat := 0x8000e3cc

-- @@ L149-149 verbatim
def baap_force_storage_clear : Nat := 0xab706da8

-- @@ L150-150 verbatim
def baap_item_len : Nat := 0xab706e18

-- @@ L151-151 verbatim
def baap_item_off : Nat := 0xab706e10

-- @@ L152-152 verbatim
def baap_storage_paths : Nat := 0xaf414900

-- @@ L153-153 verbatim
def baap_storage_root_ptr : Nat := 0xab706db0

-- @@ L154-154 verbatim
def baap_val_len : Nat := 0xab706e48

-- @@ L155-155 verbatim
def baap_walk_val : Nat := 0xab7075c8

-- @@ L156-156 verbatim
def baap_walk_val_len : Nat := 0xab706db8

-- @@ L157-157 verbatim
def bacp_hash : Nat := 0xab708e60

-- @@ L158-158 verbatim
def bacv_fail_code : Nat := 0xab708ea8

-- @@ L159-159 verbatim
def bah_bal_start : Nat := 0xa55aa668

-- @@ L160-160 verbatim
def bah_u32le : Nat := 0x8000caa4

-- @@ L161-161 verbatim
def bal_account_change_descriptor : Nat := 0x8000f9e4

-- @@ L162-162 verbatim
def bal_account_has_state_change : Nat := 0x8000e01c

-- @@ L163-163 verbatim
def bal_account_nonstorage_finals : Nat := 0x800265b0

-- @@ L164-164 verbatim
def bal_account_path : Nat := 0x8000e0e0

-- @@ L165-165 verbatim
def bal_account_post_fields : Nat := 0x8000e158

-- @@ L166-166 verbatim
def bal_account_record_array : Nat := 0x8000fb14

-- @@ L167-167 verbatim
def bal_acct_struct : Nat := 0xba5a1e40

-- @@ L168-168 verbatim
def bal_addr_padded : Nat := 0xba5a1ea8

-- @@ L169-169 verbatim
def bal_builder_account_count : Nat := 0xb8dd1bd8

-- @@ L170-170 verbatim
def bal_builder_accounts : Nat := 0xb8dd1ca0

-- @@ L171-171 verbatim
def bal_builder_append_balance : Nat := 0x80025a4c

-- @@ L172-172 verbatim
def bal_builder_append_code : Nat := 0x80025c10

-- @@ L173-173 verbatim
def bal_builder_append_nonce : Nat := 0x80025b34

-- @@ L174-174 verbatim
def bal_builder_balance_changes : Nat := 0xb9560228

-- @@ L175-175 verbatim
def bal_builder_balance_count : Nat := 0xb8dd1c48

-- @@ L176-176 verbatim
def bal_builder_balance_overflow : Nat := 0xb8dd1c70

-- @@ L177-177 verbatim
def bal_builder_code_changes : Nat := 0xb9d1e8e8

-- @@ L178-178 verbatim
def bal_builder_code_count : Nat := 0xb8dd1c58

-- @@ L179-179 verbatim
def bal_builder_code_overflow : Nat := 0xb8dd1c80

-- @@ L180-180 verbatim
def bal_builder_ensure_account : Nat := 0x8002542c

-- @@ L181-181 verbatim
def bal_builder_incorporate_touched_accounts : Nat := 0x80025538

-- @@ L182-182 verbatim
def bal_builder_nonce_changes : Nat := 0xb9bc8c28

-- @@ L183-183 verbatim
def bal_builder_nonce_count : Nat := 0xb8dd1c50

-- @@ L184-184 verbatim
def bal_builder_nonce_overflow : Nat := 0xb8dd1c78

-- @@ L185-185 verbatim
def bal_builder_overflow : Nat := 0xb8dd1c60

-- @@ L186-186 verbatim
def bal_builder_record_storage_change : Nat := 0x8002559c

-- @@ L187-187 verbatim
def bal_builder_storage_change_count : Nat := 0xb8dd1c40

-- @@ L188-188 verbatim
def bal_builder_storage_change_overflow : Nat := 0xb8dd1c68

-- @@ L189-189 verbatim
def bal_builder_storage_changes : Nat := 0xb9106568

-- @@ L190-190 verbatim
def bal_canonical_sort : Nat := 0x80023838

-- @@ L191-191 verbatim
def bal_emit_storage_changes : Nat := 0x80025764

-- @@ L192-192 verbatim
def bal_find_account_by_address : Nat := 0x8001ce30

-- @@ L193-193 verbatim
def bal_gas_valid_from_builder : Nat := 0x8001b050

-- @@ L194-194 verbatim
def bal_map_builder_consistent : Nat := 0x80023748

-- @@ L195-195 verbatim
def bal_map_final_value_matches : Nat := 0x800234a0

-- @@ L196-196 verbatim
def bal_rlp_emit_bytes : Nat := 0x80023d20

-- @@ L197-197 verbatim
def bal_rlp_emit_list_header : Nat := 0x80023e60

-- @@ L198-198 verbatim
def bal_rlp_emit_scalar : Nat := 0x80023b90

-- @@ L199-199 verbatim
def bal_rlp_list_header_len : Nat := 0x80023f78

-- @@ L200-200 verbatim
def bal_rlp_measure_into_throwaway : Nat := 0x80023cf0

-- @@ L201-201 verbatim
def bal_rlp_scalar_rlp_len : Nat := 0x80023f24

-- @@ L202-202 verbatim
def bal_serializer_addr_matches : Nat := 0x80023fa8

-- @@ L203-203 verbatim
def bal_serializer_addr_matches_be : Nat := 0x80023fe8

-- @@ L204-204 verbatim
def bal_serializer_balance_le : Nat := 0xb9106220

-- @@ L205-205 verbatim
def bal_serializer_balance_to_le : Nat := 0x800242e4

-- @@ L206-206 verbatim
def bal_serializer_emit_account : Nat := 0x80024f34

-- @@ L207-207 verbatim
def bal_serializer_emit_balance : Nat := 0x80024b44

-- @@ L208-208 verbatim
def bal_serializer_emit_code : Nat := 0x80024e00

-- @@ L209-209 verbatim
def bal_serializer_emit_nonce : Nat := 0x80024c88

-- @@ L210-210 verbatim
def bal_serializer_emit_outer : Nat := 0x800250f0

-- @@ L211-211 verbatim
def bal_serializer_emit_reads : Nat := 0x80024a78

-- @@ L212-212 verbatim
def bal_serializer_emit_storage : Nat := 0x80024898

-- @@ L213-213 verbatim
def bal_serializer_hdr_scratch : Nat := 0xb9106488

-- @@ L214-214 verbatim
def bal_serializer_len_table : Nat := 0xb91061a0

-- @@ L215-215 verbatim
def bal_serializer_measure_account : Nat := 0x800247b4

-- @@ L216-216 verbatim
def bal_serializer_measure_balance : Nat := 0x80024500

-- @@ L217-217 verbatim
def bal_serializer_measure_code : Nat := 0x800246c4

-- @@ L218-218 verbatim
def bal_serializer_measure_nonce : Nat := 0x800245dc

-- @@ L219-219 verbatim
def bal_serializer_measure_outer : Nat := 0x80025060

-- @@ L220-220 verbatim
def bal_serializer_measure_reads : Nat := 0x800241d8

-- @@ L221-221 verbatim
def bal_serializer_measure_slot : Nat := 0x80024314

-- @@ L222-222 verbatim
def bal_serializer_measure_storage : Nat := 0x80024420

-- @@ L223-223 verbatim
def bal_serializer_outer_payload : Nat := 0xb91061d0

-- @@ L224-224 verbatim
def bal_serializer_rebuild_hash : Nat := 0x80025198

-- @@ L225-225 verbatim
def bal_serializer_rebuilt_ctx : Nat := 0xb9106248

-- @@ L226-226 verbatim
def bal_serializer_rebuilt_hash : Nat := 0xb9106448

-- @@ L227-227 verbatim
def bal_serializer_slot_eq : Nat := 0x80024020

-- @@ L228-228 verbatim
def bal_serializer_slot_le : Nat := 0xb9106200

-- @@ L229-229 verbatim
def bal_serializer_slot_seen_before : Nat := 0x8002411c

-- @@ L230-230 verbatim
def bal_serializer_slot_to_le : Nat := 0x800242b4

-- @@ L231-231 verbatim
def bal_serializer_slot_written : Nat := 0x80024060

-- @@ L232-232 verbatim
def bal_serializer_sort_status : Nat := 0xb9106240

-- @@ L233-233 verbatim
def bal_serializer_supplied_hash : Nat := 0xb9106468

-- @@ L234-234 verbatim
def bal_serializer_surviving_read_count : Nat := 0xb91061d8

-- @@ L235-235 verbatim
def bal_serializer_throwaway_ctx : Nat := 0xb9106498

-- @@ L236-236 verbatim
def bal_serializer_u64_field : Nat := 0xb91061e0

-- @@ L237-237 verbatim
def bal_serializer_u64_to_field : Nat := 0x800241c0

-- @@ L238-238 verbatim
def bal_serializer_verify : Nat := 0x80025394

-- @@ L239-239 verbatim
def bal_sort_ranges : Nat := 0xb9dedae8

-- @@ L240-240 verbatim
def bal_state_root : Nat := 0xba5a1e20

-- @@ L241-241 verbatim
def bal_storage_change_values : Nat := 0x80020358

-- @@ L242-242 verbatim
def balance_live_else_header_state_root : Nat := 0x80030878

-- @@ L243-243 verbatim
def bald_bal_bit_set : Nat := 0xa5edbdd8

-- @@ L244-244 verbatim
def bald_bal_builder_count : Nat := 0xa5edbde8

-- @@ L245-245 verbatim
def bald_bal_cmp_attempts : Nat := 0xa5edbdf0

-- @@ L246-246 verbatim
def bald_bal_differs : Nat := 0xa5edbde0

-- @@ L247-247 verbatim
def bald_bal_eq_addr_a : Nat := 0xa5edbe58

-- @@ L248-248 verbatim
def bald_bal_eq_addr_b : Nat := 0xa5edbe60

-- @@ L249-249 verbatim
def bald_bal_eq_bai_mask : Nat := 0xa5edbe18

-- @@ L250-250 verbatim
def bald_bal_eq_val_hi : Nat := 0xa5edbe30

-- @@ L251-251 verbatim
def bald_bal_eq_val_lo : Nat := 0xa5edbe28

-- @@ L252-252 verbatim
def bald_bal_ne_bai_mask : Nat := 0xa5edbe20

-- @@ L253-253 verbatim
def bald_non_bit_set : Nat := 0xa5edbdf8

-- @@ L254-254 verbatim
def bald_non_builder_count : Nat := 0xa5edbe08

-- @@ L255-255 verbatim
def bald_non_cmp_attempts : Nat := 0xa5edbe10

-- @@ L256-256 verbatim
def bald_non_differs : Nat := 0xa5edbe00

-- @@ L257-257 verbatim
def bald_non_eq_bai_mask : Nat := 0xa5edbe38

-- @@ L258-258 verbatim
def bald_non_eq_val_post : Nat := 0xa5edbe50

-- @@ L259-259 verbatim
def bald_non_eq_val_pre : Nat := 0xa5edbe48

-- @@ L260-260 verbatim
def bald_non_ne_bai_mask : Nat := 0xa5edbe40

-- @@ L261-261 verbatim
def bame_value : Nat := 0xb9dedac0

-- @@ L262-262 verbatim
def bara_acct : Nat := 0xb83c6e68

-- @@ L263-263 verbatim
def bara_acct_len : Nat := 0xb83c6e10

-- @@ L264-264 verbatim
def bara_bal_end : Nat := 0xb83c6e18

-- @@ L265-265 verbatim
def bara_empty_account : Nat := 0xa0b00ca0

-- @@ L266-266 verbatim
def bara_item_len : Nat := 0xb83c6e08

-- @@ L267-267 verbatim
def bara_next_item : Nat := 0xb83c6e20

-- @@ L268-268 verbatim
def bara_path : Nat := 0xb83c6e28

-- @@ L269-269 verbatim
def basr_records : Nat := 0xab708ec0

-- @@ L270-270 verbatim
def bav_hash : Nat := 0xa9e8655c

-- @@ L271-271 verbatim
def besc_addr_be : Nat := 0xb8dd1be0

-- @@ L272-272 verbatim
def besc_base_le : Nat := 0xb8dd1c20

-- @@ L273-273 verbatim
def besc_slot_be : Nat := 0xb8dd1c00

-- @@ L274-274 verbatim
def bfa_index : Nat := 0xb85cf160

-- @@ L275-275 verbatim
def bgv_u32le : Nat := 0x8001ae14

-- @@ L276-276 verbatim
def bgv_u64le : Nat := 0x8001ae44

-- @@ L277-277 verbatim
def bgvh_count_scratch : Nat := 0xab706b48

-- @@ L278-278 verbatim
def bhfwh_number_buf : Nat := 0xb85ced50

-- @@ L279-279 verbatim
def bhr_empty_ommers : Nat := 0xa0b00a80

-- @@ L280-280 verbatim
def bhr_flen : Nat := 0xa438a888

-- @@ L281-281 verbatim
def bhr_payload : Nat := 0xa438a8c8

-- @@ L282-282 verbatim
def bhr_prefix_len : Nat := 0xa438a890

-- @@ L283-283 verbatim
def bhr_rev_le_be : Nat := 0x8000c248

-- @@ L284-284 verbatim
def bhr_uint_be : Nat := 0xa438a8a0

-- @@ L285-285 verbatim
def bhr_zero8 : Nat := 0xa438a880

-- @@ L286-286 verbatim
def blbr_count : Nat := 0xa9c45460

-- @@ L287-287 verbatim
def blbr_length : Nat := 0xa9c45470

-- @@ L288-288 verbatim
def blbr_next_length : Nat := 0xa9c45480

-- @@ L289-289 verbatim
def blbr_next_offset : Nat := 0xa9c45478

-- @@ L290-290 verbatim
def blbr_offset : Nat := 0xa9c45468

-- @@ L291-291 verbatim
def blbr_scratch_bloom : Nat := 0xa9c45488

-- @@ L292-292 verbatim
def blk2_ld_le64 : Nat := 0x80036c90

-- @@ L293-293 verbatim
def blk2_st_le64 : Nat := 0x80036cbc

-- @@ L294-294 verbatim
def blm_fp2_pow : Nat := 0x80039ba4

-- @@ L295-295 verbatim
def blm_fp_pow : Nat := 0x80039b00

-- @@ L296-296 verbatim
def block_access_list_hash : Nat := 0x8000caec

-- @@ L297-297 verbatim
def block_access_list_hash_core : Nat := 0x8000cad4

-- @@ L298-298 verbatim
def block_hash_from_header : Nat := 0x8000cb68

-- @@ L299-299 verbatim
def block_header_ssz_to_rlp : Nat := 0x8000c274

-- @@ L300-300 verbatim
def block_logs_bloom_from_receipts_list : Nat := 0x80015904

-- @@ L301-301 verbatim
def block_rlp_rebuilt_size : Nat := 0x8000c888

-- @@ L302-302 verbatim
def block_validate_logs_bloom : Nat := 0x80015740

-- @@ L303-303 verbatim
def block_validate_receipts_root_indexed : Nat := 0x800151cc

-- @@ L304-304 verbatim
def block_validate_withdrawals_root_indexed : Nat := 0x8000aef8

-- @@ L305-305 verbatim
def block_verdict_chain_id_gate : Nat := 0x8002c754

-- @@ L306-306 verbatim
def block_verdict_eip8037_tx_state_gas_net_array : Nat := 0x80026bc8

-- @@ L307-307 verbatim
def block_verdict_gas_result_arena_prepare : Nat := 0x8002a838

-- @@ L308-308 verbatim
def block_verdict_tx_gas_limits : Nat := 0x800290f8

-- @@ L309-309 verbatim
def block_verdict_tx_state_gas_inline_finalize : Nat := 0x8002a748

-- @@ L310-310 verbatim
def block_verdict_tx_state_gas_inline_prepare : Nat := 0x8002a410

-- @@ L311-311 verbatim
def blockhash_from_witness_headers : Nat := 0x8002645c

-- @@ L312-312 verbatim
def bloom_add_value : Nat := 0x80014d58

-- @@ L313-313 verbatim
def bloom_eq : Nat := 0x80015d48

-- @@ L314-314 verbatim
def bloom_or_into : Nat := 0x800158cc

-- @@ L315-315 verbatim
def blq_acc : Nat := 0xb9e04050

-- @@ L316-316 verbatim
def blq_arith_params : Nat := 0xb9e04028

-- @@ L317-317 verbatim
def blq_copy : Nat := 0x80038c00

-- @@ L318-318 verbatim
def blq_eq : Nat := 0x80038c64

-- @@ L319-319 verbatim
def blq_is_zero : Nat := 0x80038c98

-- @@ L320-320 verbatim
def blq_le_2 : Nat := 0xa0b01610

-- @@ L321-321 verbatim
def blq_le_pm2 : Nat := 0xa0b016d0

-- @@ L322-322 verbatim
def blq_mul : Nat := 0x8003897c

-- @@ L323-323 verbatim
def blq_pow : Nat := 0x80038cc0

-- @@ L324-324 verbatim
def blq_powt : Nat := 0xb9e044a0

-- @@ L325-325 verbatim
def blq_pt_copy : Nat := 0x80038d80

-- @@ L326-326 verbatim
def blq_set_one : Nat := 0x80038c38

-- @@ L327-327 verbatim
def blq_smul : Nat := 0x80038bb0

-- @@ L328-328 verbatim
def blq_zero : Nat := 0x80038c20

-- @@ L329-329 verbatim
def blsf_add_params : Nat := 0xa0b01028

-- @@ L330-330 verbatim
def blsf_copy_quads : Nat := 0x80033c34

-- @@ L331-331 verbatim
def blsf_cplx_params : Nat := 0xa0b01060

-- @@ L332-332 verbatim
def blsf_curve_params : Nat := 0xa0b01050

-- @@ L333-333 verbatim
def blsf_le_a : Nat := 0xb9e03340

-- @@ L334-334 verbatim
def blsf_le_b : Nat := 0xb9e03370

-- @@ L335-335 verbatim
def blsf_le_d : Nat := 0xb9e033a0

-- @@ L336-336 verbatim
def blsf_le_one : Nat := 0xa0b00fd0

-- @@ L337-337 verbatim
def blsf_le_p : Nat := 0xa0b00fa0

-- @@ L338-338 verbatim
def blsf_le_zero : Nat := 0xb9e03310

-- @@ L339-339 verbatim
def blsf_mul_params : Nat := 0xa0b01000

-- @@ L340-340 verbatim
def blsf_p1 : Nat := 0xb9e033d0

-- @@ L341-341 verbatim
def blsf_p2 : Nat := 0xb9e03430

-- @@ L342-342 verbatim
def blsg2_b_le : Nat := 0xa0b01150

-- @@ L343-343 verbatim
def blsg2_chord_tail : Nat := 0x8003820c

-- @@ L344-344 verbatim
def blsg2_copy192 : Nat := 0x8003819c

-- @@ L345-345 verbatim
def blsg2_decode_g2 : Nat := 0x80038568

-- @@ L346-346 verbatim
def blsg2_den : Nat := 0xb9e03ae8

-- @@ L347-347 verbatim
def blsg2_encode : Nat := 0x800387c0

-- @@ L348-348 verbatim
def blsg2_eq_n : Nat := 0x800381d0

-- @@ L349-349 verbatim
def blsg2_facc : Nat := 0xb9e03968

-- @@ L350-350 verbatim
def blsg2_fp2_add : Nat := 0x80038080

-- @@ L351-351 verbatim
def blsg2_fp2_inv : Nat := 0x800380d4

-- @@ L352-352 verbatim
def blsg2_fp2_mul : Nat := 0x800380b8

-- @@ L353-353 verbatim
def blsg2_fp2_sub : Nat := 0x8003809c

-- @@ L354-354 verbatim
def blsg2_fp_add : Nat := 0x80037f68

-- @@ L355-355 verbatim
def blsg2_fp_inv : Nat := 0x80037fa0

-- @@ L356-356 verbatim
def blsg2_fp_mul : Nat := 0x80037f30

-- @@ L357-357 verbatim
def blsg2_fp_params : Nat := 0xb9e038e0

-- @@ L358-358 verbatim
def blsg2_ft : Nat := 0xb9e03998

-- @@ L359-359 verbatim
def blsg2_inv_out : Nat := 0xb9e03b48

-- @@ L360-360 verbatim
def blsg2_lam : Nat := 0xb9e039c8

-- @@ L361-361 verbatim
def blsg2_n : Nat := 0xb9e03908

-- @@ L362-362 verbatim
def blsg2_ninv : Nat := 0xb9e03938

-- @@ L363-363 verbatim
def blsg2_oc_t : Nat := 0xb9e03ba8

-- @@ L364-364 verbatim
def blsg2_oc_y2 : Nat := 0xb9e03c08

-- @@ L365-365 verbatim
def blsg2_p_minus_2_be : Nat := 0xa0b010f0

-- @@ L366-366 verbatim
def blsg2_pm1_le : Nat := 0xa0b01120

-- @@ L367-367 verbatim
def blsg2_point_add : Nat := 0x80038414

-- @@ L368-368 verbatim
def blsg2_point_dbl : Nat := 0x80038304

-- @@ L369-369 verbatim
def blsg2_scalar_mul : Nat := 0x800386a0

-- @@ L370-370 verbatim
def blsg2_sub_out : Nat := 0xb9e03f68

-- @@ L371-371 verbatim
def blsg2_subgroup_g2 : Nat := 0x80038790

-- @@ L372-372 verbatim
def blsg2_t1 : Nat := 0xb9e03a28

-- @@ L373-373 verbatim
def blsg2_t2 : Nat := 0xb9e03a88

-- @@ L374-374 verbatim
def blsg2_zero192 : Nat := 0x800381b8

-- @@ L375-375 verbatim
def blsg_add_mod_p : Nat := 0x80033e40

-- @@ L376-376 verbatim
def blsg_b_be : Nat := 0xa0b010a0

-- @@ L377-377 verbatim
def blsg_be_to_le : Nat := 0x80033c54

-- @@ L378-378 verbatim
def blsg_copy96 : Nat := 0x80033da0

-- @@ L379-379 verbatim
def blsg_decode_g1 : Nat := 0x800342b4

-- @@ L380-380 verbatim
def blsg_eq48 : Nat := 0x80033d20

-- @@ L381-381 verbatim
def blsg_is_zero_n : Nat := 0x80033cf0

-- @@ L382-382 verbatim
def blsg_le_acc : Nat := 0xb9e03880

-- @@ L383-383 verbatim
def blsg_le_add : Nat := 0x80034114

-- @@ L384-384 verbatim
def blsg_le_base : Nat := 0xb9e03820

-- @@ L385-385 verbatim
def blsg_le_dbl : Nat := 0x80034090

-- @@ L386-386 verbatim
def blsg_le_to_be : Nat := 0x80033ca4

-- @@ L387-387 verbatim
def blsg_lt_p : Nat := 0x80033d5c

-- @@ L388-388 verbatim
def blsg_mul_mod_p : Nat := 0x80033dd8

-- @@ L389-389 verbatim
def blsg_n_be : Nat := 0xa0b010d0

-- @@ L390-390 verbatim
def blsg_on_curve : Nat := 0x80034228

-- @@ L391-391 verbatim
def blsg_p_be : Nat := 0xa0b01070

-- @@ L392-392 verbatim
def blsg_point_add : Nat := 0x80033f4c

-- @@ L393-393 verbatim
def blsg_point_dbl : Nat := 0x80033ea8

-- @@ L394-394 verbatim
def blsg_rhs : Nat := 0xb9e03580

-- @@ L395-395 verbatim
def blsg_scalar_mul : Nat := 0x80034390

-- @@ L396-396 verbatim
def blsg_sub_out : Nat := 0xb9e037c0

-- @@ L397-397 verbatim
def blsg_subgroup_g1 : Nat := 0x80034500

-- @@ L398-398 verbatim
def blsg_t : Nat := 0xb9e03550

-- @@ L399-399 verbatim
def blsg_y2 : Nat := 0xb9e035b0

-- @@ L400-400 verbatim
def blsg_zero96 : Nat := 0x80033dc0

-- @@ L401-401 verbatim
def blsk_decompress_g1 : Nat := 0x80036fb0

-- @@ L402-402 verbatim
def blsk_fp_pow_q14 : Nat := 0x80036e90

-- @@ L403-403 verbatim
def blsk_g1_wire : Nat := 0x80037228

-- @@ L404-404 verbatim
def blsk_g2_wire : Nat := 0x80037284

-- @@ L405-405 verbatim
def blsk_lt_be : Nat := 0x80036f70

-- @@ L406-406 verbatim
def blsk_neg_scalar : Nat := 0x80037178

-- @@ L407-407 verbatim
def blsk_negn_params : Nat := 0xa0b03148

-- @@ L408-408 verbatim
def blsk_phalf_be : Nat := 0xa0b02dd8

-- @@ L409-409 verbatim
def blsk_powacc : Nat := 0xb9e09570

-- @@ L410-410 verbatim
def blsk_qp1d4_be : Nat := 0xa0b02da8

-- @@ L411-411 verbatim
def blsk_rhs_le : Nat := 0xb9e094e0

-- @@ L412-412 verbatim
def blsk_scal_be : Nat := 0xb9e095a0

-- @@ L413-413 verbatim
def blsk_scal_le : Nat := 0xb9e095d0

-- @@ L414-414 verbatim
def blsk_t_le : Nat := 0xb9e09540

-- @@ L415-415 verbatim
def blsk_x_le : Nat := 0xb9e094b0

-- @@ L416-416 verbatim
def blsk_y_le : Nat := 0xb9e09510

-- @@ L417-417 verbatim
def bmvmx_sender_addr : Nat := 0xb86d3e20

-- @@ L418-418 verbatim
def bn254_call_allotment : Nat := 0x80034dcc

-- @@ L419-419 verbatim
def bnc_add_params : Nat := 0xa0b00f90

-- @@ L420-420 verbatim
def bnc_copy64 : Nat := 0x800348b4

-- @@ L421-421 verbatim
def bnc_is_inf64 : Nat := 0x800348f4

-- @@ L422-422 verbatim
def bnc_le_p1 : Nat := 0xb9e031e8

-- @@ L423-423 verbatim
def bnc_le_p2 : Nat := 0xb9e03228

-- @@ L424-424 verbatim
def bnc_on_curve : Nat := 0x80034afc

-- @@ L425-425 verbatim
def bnc_point_add : Nat := 0x800349c4

-- @@ L426-426 verbatim
def bnc_point_dbl : Nat := 0x80034924

-- @@ L427-427 verbatim
def bnc_point_tmp : Nat := 0xb9e03268

-- @@ L428-428 verbatim
def bnc_rhs : Nat := 0xb9e032c8

-- @@ L429-429 verbatim
def bnc_scalar_mul : Nat := 0x80034be8

-- @@ L430-430 verbatim
def bnc_t : Nat := 0xb9e032a8

-- @@ L431-431 verbatim
def bnc_validate_g1 : Nat := 0x80034b88

-- @@ L432-432 verbatim
def bnc_y2 : Nat := 0xb9e032e8

-- @@ L433-433 verbatim
def bnc_zero64 : Nat := 0x800348d8

-- @@ L434-434 verbatim
def bnf_add_mod_p : Nat := 0x8003484c

-- @@ L435-435 verbatim
def bnf_add_params : Nat := 0xa0b00f68

-- @@ L436-436 verbatim
def bnf_b_be : Nat := 0xa0b00e60

-- @@ L437-437 verbatim
def bnf_be_to_le : Nat := 0x80034698

-- @@ L438-438 verbatim
def bnf_eq32 : Nat := 0x80034764

-- @@ L439-439 verbatim
def bnf_is_zero32 : Nat := 0x80034734

-- @@ L440-440 verbatim
def bnf_le_a : Nat := 0xa0b00e80

-- @@ L441-441 verbatim
def bnf_le_b : Nat := 0xa0b00ea0

-- @@ L442-442 verbatim
def bnf_le_d : Nat := 0xa0b00ec0

-- @@ L443-443 verbatim
def bnf_le_one : Nat := 0xa0b00f00

-- @@ L444-444 verbatim
def bnf_le_p : Nat := 0xa0b00f20

-- @@ L445-445 verbatim
def bnf_le_to_be : Nat := 0x800346e8

-- @@ L446-446 verbatim
def bnf_le_zero : Nat := 0xa0b00ee0

-- @@ L447-447 verbatim
def bnf_lt_p : Nat := 0x800347a0

-- @@ L448-448 verbatim
def bnf_mul_mod_p : Nat := 0x800347e4

-- @@ L449-449 verbatim
def bnf_mul_params : Nat := 0xa0b00f40

-- @@ L450-450 verbatim
def bnf_p_be : Nat := 0xa0b00e40

-- @@ L451-451 verbatim
def bnp_arith_params : Nat := 0xb9e09f90

-- @@ L452-452 verbatim
def bnp_cplx_params : Nat := 0xb9e09f80

-- @@ L453-453 verbatim
def bnp_fp2_add : Nat := 0x80034e00

-- @@ L454-454 verbatim
def bnp_fp2_copy : Nat := 0x80034e48

-- @@ L455-455 verbatim
def bnp_fp2_eq : Nat := 0x80034eb0

-- @@ L456-456 verbatim
def bnp_fp2_is_zero : Nat := 0x80034ee4

-- @@ L457-457 verbatim
def bnp_fp2_mul : Nat := 0x80034e30

-- @@ L458-458 verbatim
def bnp_fp2_sub : Nat := 0x80034e18

-- @@ L459-459 verbatim
def bnp_fp2_zero : Nat := 0x80034e8c

-- @@ L460-460 verbatim
def bnp_fp_add : Nat := 0x80034f40

-- @@ L461-461 verbatim
def bnp_fp_mul : Nat := 0x80034f0c

-- @@ L462-462 verbatim
def bnp_fp_pow : Nat := 0x80034f74

-- @@ L463-463 verbatim
def bnp_p_minus_1_le : Nat := 0xa0b03428

-- @@ L464-464 verbatim
def bnp_p_minus_2_le : Nat := 0xa0b03408

-- @@ L465-465 verbatim
def bnp_t0 : Nat := 0xb9e09fb8

-- @@ L466-466 verbatim
def bnp_t1 : Nat := 0xb9e09fd8

-- @@ L467-467 verbatim
def bnp_t2 : Nat := 0xb9e09ff8

-- @@ L468-468 verbatim
def bnq_acc : Nat := 0xb9e0a058

-- @@ L469-469 verbatim
def bnq_copy : Nat := 0x80035244

-- @@ L470-470 verbatim
def bnq_eq : Nat := 0x800352a8

-- @@ L471-471 verbatim
def bnq_is_zero : Nat := 0x800352dc

-- @@ L472-472 verbatim
def bnq_le_18 : Nat := 0xa0b03768

-- @@ L473-473 verbatim
def bnq_le_pm82 : Nat := 0xa0b03788

-- @@ L474-474 verbatim
def bnq_mul : Nat := 0x80035018

-- @@ L475-475 verbatim
def bnq_pow : Nat := 0x80035304

-- @@ L476-476 verbatim
def bnq_powt : Nat := 0xb9e0a338

-- @@ L477-477 verbatim
def bnq_pt_copy : Nat := 0x800363fc

-- @@ L478-478 verbatim
def bnq_set_one : Nat := 0x8003527c

-- @@ L479-479 verbatim
def bnq_smul : Nat := 0x800351fc

-- @@ L480-480 verbatim
def bnq_zero : Nat := 0x80035264

-- @@ L481-481 verbatim
def brl_item_end : Nat := 0xaa8453c8

-- @@ L482-482 verbatim
def brl_item_start : Nat := 0xaa8453c0

-- @@ L483-483 verbatim
def brl_wd_buf : Nat := 0xaa8453d8

-- @@ L484-484 verbatim
def brl_wd_len : Nat := 0xaa8453d0

-- @@ L485-485 verbatim
def bscv_vptr : Nat := 0xaa6bca60

-- @@ L486-486 verbatim
def bsg_access_addrs : Nat := 0xab706ac0

-- @@ L487-487 verbatim
def bsg_access_field : Nat := 0xab706a68

-- @@ L488-488 verbatim
def bsg_access_len : Nat := 0xab706ab8

-- @@ L489-489 verbatim
def bsg_access_off : Nat := 0xab706ab0

-- @@ L490-490 verbatim
def bsg_access_slots : Nat := 0xab706ac8

-- @@ L491-491 verbatim
def bsg_auth_count : Nat := 0xab706ae0

-- @@ L492-492 verbatim
def bsg_auth_field : Nat := 0xab706a70

-- @@ L493-493 verbatim
def bsg_auth_len : Nat := 0xab706ad8

-- @@ L494-494 verbatim
def bsg_auth_off : Nat := 0xab706ad0

-- @@ L495-495 verbatim
def bsg_blob_count : Nat := 0xab706b38

-- @@ L496-496 verbatim
def bsg_blob_gas_accum : Nat := 0xab706b40

-- @@ L497-497 verbatim
def bsg_blob_lt_out : Nat := 0xab706c88

-- @@ L498-498 verbatim
def bsg_blob_price_be : Nat := 0xab706c68

-- @@ L499-499 verbatim
def bsg_data_field : Nat := 0xab706a60

-- @@ L500-500 verbatim
def bsg_data_len : Nat := 0xab706a98

-- @@ L501-501 verbatim
def bsg_data_off : Nat := 0xab706a90

-- @@ L502-502 verbatim
def bsg_data_ptr : Nat := 0xab706a88

-- @@ L503-503 verbatim
def bsg_exact_state_ok : Nat := 0xab706b30

-- @@ L504-504 verbatim
def bsg_floor_gas : Nat := 0xab706a80

-- @@ L505-505 verbatim
def bsg_gas_field : Nat := 0xab706a48

-- @@ L506-506 verbatim
def bsg_intrinsic_gas : Nat := 0xab706a78

-- @@ L507-507 verbatim
def bsg_min_block_gas : Nat := 0xab706ae8

-- @@ L508-508 verbatim
def bsg_prior_state : Nat := 0xab706b20

-- @@ L509-509 verbatim
def bsg_sender_addr : Nat := 0xab706c90

-- @@ L510-510 verbatim
def bsg_state_gas : Nat := 0xab706b28

-- @@ L511-511 verbatim
def bsg_to_field : Nat := 0xab706a50

-- @@ L512-512 verbatim
def bsg_to_len : Nat := 0xab706aa8

-- @@ L513-513 verbatim
def bsg_to_off : Nat := 0xab706aa0

-- @@ L514-514 verbatim
def bsg_tx_gas : Nat := 0xab706a40

-- @@ L515-515 verbatim
def bsg_tx_inner : Nat := 0xab706a38

-- @@ L516-516 verbatim
def bsg_tx_type : Nat := 0xab706a30

-- @@ L517-517 verbatim
def bsg_value_field : Nat := 0xab706a58

-- @@ L518-518 verbatim
def bsg_value_len : Nat := 0xab706a28

-- @@ L519-519 verbatim
def bsg_value_off : Nat := 0xab706a20

-- @@ L520-520 verbatim
def bsg_worst_state : Nat := 0xab706b18

-- @@ L521-521 verbatim
def bsr_addr_2935 : Nat := 0xa0b00b20

-- @@ L522-522 verbatim
def bsr_addr_4788 : Nat := 0xa0b00b40

-- @@ L523-523 verbatim
def bsw_amount : Nat := 0xaa845050

-- @@ L524-524 verbatim
def bsw_wei : Nat := 0xaa845070

-- @@ L525-525 verbatim
def bti_conflict : Nat := 0xb85cf210

-- @@ L526-526 verbatim
def bti_err : Nat := 0xb85cf218

-- @@ L527-527 verbatim
def bti_first_tx : Nat := 0xb85cf200

-- @@ L528-528 verbatim
def bti_has_write : Nat := 0xb85cf208

-- @@ L529-529 verbatim
def builder_deposit_contract_addr : Nat := 0xa0b00db8

-- @@ L530-530 verbatim
def builder_exit_contract_addr : Nat := 0xa0b00dd0

-- @@ L531-531 verbatim
def bv_bal_shadow_emit_balance_changes : Nat := 0xa5edbdc0

-- @@ L532-532 verbatim
def bv_bal_shadow_emit_code_changes : Nat := 0xa5edbdd0

-- @@ L533-533 verbatim
def bv_bal_shadow_emit_nonce_changes : Nat := 0xa5edbdc8

-- @@ L534-534 verbatim
def bv_bal_shadow_emit_storage_changes : Nat := 0xa5edbdb0

-- @@ L535-535 verbatim
def bv_bal_shadow_emit_storage_reads : Nat := 0xa5edbdb8

-- @@ L536-536 verbatim
def bv_chain_id : Nat := 0xa3a4bf40

-- @@ L537-537 verbatim
def bv_exec_p : Nat := 0xa5edbd68

-- @@ L538-538 verbatim
def bv_mtx_calldata : Nat := 0xb8692770

-- @@ L539-539 verbatim
def bv_mtx_ctx : Nat := 0xb86b3040

-- @@ L540-540 verbatim
def bv_public_keys_len : Nat := 0xa5edbec8

-- @@ L541-541 verbatim
def bv_public_keys_ptr : Nat := 0xa5edbec0

-- @@ L542-542 verbatim
def bv_runtime_calldata_floor : Nat := 0xaa6bca38

-- @@ L543-543 verbatim
def bv_sum_withdrawals_to_address : Nat := 0x80027af8

-- @@ L544-544 verbatim
def bv_tx_count : Nat := 0xa5edbea8

-- @@ L545-545 verbatim
def bv_tx_item_start : Nat := 0xa5edbeb8

-- @@ L546-546 verbatim
def bv_tx_list_len : Nat := 0xa5edbea0

-- @@ L547-547 verbatim
def bv_tx_list_ptr : Nat := 0xa5edbe98

-- @@ L548-548 verbatim
def bv_tx_status_arr : Nat := 0xa5edbf68

-- @@ L549-549 verbatim
def bv_witness_state_len : Nat := 0xb86d3cc0

-- @@ L550-550 verbatim
def bv_witness_state_ptr : Nat := 0xb86d3cb8

-- @@ L551-551 verbatim
def bvgr_applied_refund : Nat := 0xaa822c80

-- @@ L552-552 verbatim
def bvgr_arena_fail_index : Nat := 0xaa6bcb48

-- @@ L553-553 verbatim
def bvgr_arena_runtime_count : Nat := 0xaa6bcb40

-- @@ L554-554 verbatim
def bvgr_arena_status : Nat := 0xaa6bcb30

-- @@ L555-555 verbatim
def bvgr_arena_substatus : Nat := 0xaa6bcb50

-- @@ L556-556 verbatim
def bvgr_arena_tx_count : Nat := 0xaa6bcb38

-- @@ L557-557 verbatim
def bvgr_before_refund : Nat := 0xaa8023b0

-- @@ L558-558 verbatim
def bvgr_block_gas_increments : Nat := 0xaa73ee98

-- @@ L559-559 verbatim
def bvgr_calldata_floor : Nat := 0xaa71e5c8

-- @@ L560-560 verbatim
def bvgr_count : Nat := 0xaa6bcb00

-- @@ L561-561 verbatim
def bvgr_fail_index : Nat := 0xaa6bcb08

-- @@ L562-562 verbatim
def bvgr_gas : Nat := 0xaa6bcb28

-- @@ L563-563 verbatim
def bvgr_gas_left : Nat := 0xaa6dd428

-- @@ L564-564 verbatim
def bvgr_nonce : Nat := 0xaa6bcb20

-- @@ L565-565 verbatim
def bvgr_receipt_gas_increments : Nat := 0xaa7e1ae0

-- @@ L566-566 verbatim
def bvgr_refund_counter : Nat := 0xaa6fdcf8

-- @@ L567-567 verbatim
def bvgr_runtime_count : Nat := 0xaa092220

-- @@ L568-568 verbatim
def bvgr_status : Nat := 0xaa6bcaf8

-- @@ L569-569 verbatim
def bvgr_tx_exec_state_gas : Nat := 0xaa780038

-- @@ L570-570 verbatim
def bvgr_tx_exec_state_gas_derived : Nat := 0xbbb6af00

-- @@ L571-571 verbatim
def bvgr_tx_exec_state_gas_diff : Nat := 0xbbb8b7d0

-- @@ L572-572 verbatim
def bvgr_tx_exec_state_gas_nonderivable : Nat := 0xbbbac0a0

-- @@ L573-573 verbatim
def bvgr_tx_gas_limits : Nat := 0xaa6bcb58

-- @@ L574-574 verbatim
def bvgr_tx_inner : Nat := 0xaa6bcb18

-- @@ L575-575 verbatim
def bvgr_tx_state_gas : Nat := 0xaa75f768

-- @@ L576-576 verbatim
def bvgr_tx_total_state_gas : Nat := 0xaa7a0908

-- @@ L577-577 verbatim
def bvgr_tx_type : Nat := 0xaa6bcb10

-- @@ L578-578 verbatim
def bvlb_computed_bloom : Nat := 0xa9c45688

-- @@ L579-579 verbatim
def bvlb_header_bloom : Nat := 0xa9c45588

-- @@ L580-580 verbatim
def bvrri_computed_root : Nat := 0xaa050e40

-- @@ L581-581 verbatim
def bvrri_expected_root : Nat := 0xaa050e20

-- @@ L582-582 verbatim
def bvwri_computed_root : Nat := 0xa9f8aca0

-- @@ L583-583 verbatim
def bvwri_expected_root : Nat := 0xa9f8ac80

-- @@ L584-584 verbatim
def bytes_to_nibbles : Nat := 0x80005714

-- @@ L585-585 verbatim
def c1_staging : Nat := 0xaa845498

-- @@ L586-586 verbatim
def cahsr_acct_struct : Nat := 0xb85cc780

-- @@ L587-587 verbatim
def cahsr_code_length : Nat := 0xb85cc7f0

-- @@ L588-588 verbatim
def cahsr_code_offset : Nat := 0xb85cc7e8

-- @@ L589-589 verbatim
def cahsr_state_root : Nat := 0xb85cc760

-- @@ L590-590 verbatim
def call_frame_arena : Nat := 0xabf6dc00

-- @@ L591-591 verbatim
def call_frame_enter : Nat := 0x8003c76c

-- @@ L592-592 verbatim
def call_frame_forward_gas : Nat := 0x8003c93c

-- @@ L593-593 verbatim
def call_frame_set_calldata : Nat := 0x8003c92c

-- @@ L594-594 verbatim
def chahsr_acct_struct : Nat := 0xab7046c0

-- @@ L595-595 verbatim
def chahsr_empty_code_hash : Nat := 0xa0b00c40

-- @@ L596-596 verbatim
def chahsr_state_root : Nat := 0xab7046a0

-- @@ L597-597 verbatim
def chain_config_valid : Nat := 0x80013e68

-- @@ L598-598 verbatim
def check_gas_limit : Nat := 0x8000b020

-- @@ L599-599 verbatim
def cig_inner_off : Nat := 0xa3a4c0c8

-- @@ L600-600 verbatim
def cig_len : Nat := 0xa3a4c0d8

-- @@ L601-601 verbatim
def cig_off : Nat := 0xa3a4c0d0

-- @@ L602-602 verbatim
def cig_type : Nat := 0xa3a4c0c0

-- @@ L603-603 verbatim
def code_at_header_state_root : Nat := 0x8001ccec

-- @@ L604-604 verbatim
def code_hash_at_header_state_root : Nat := 0x8001b2d4

-- @@ L605-605 verbatim
def code_read_fetch : Nat := 0x80025fc0

-- @@ L606-606 verbatim
def code_read_record : Nat := 0x80025e60

-- @@ L607-607 verbatim
def code_reads_count : Nat := 0xb9dfdb90

-- @@ L608-608 verbatim
def code_reads_overflow : Nat := 0xb9dfdb98

-- @@ L609-609 verbatim
def consolidation_request_predeploy_addr : Nat := 0xa0b00da0

-- @@ L610-610 verbatim
def create_address_be : Nat := 0xba5a2660

-- @@ L611-611 verbatim
def create_child_code : Nat := 0xba5e2800

-- @@ L612-612 verbatim
def create_child_code_len : Nat := 0xba5a2700

-- @@ L613-613 verbatim
def create_child_creator_be : Nat := 0xba5a2720

-- @@ L614-614 verbatim
def create_child_init_len : Nat := 0xba5a26f0

-- @@ L615-615 verbatim
def create_child_initcode : Nat := 0xba5a2800

-- @@ L616-616 verbatim
def create_child_kind : Nat := 0xba5a26e8

-- @@ L617-617 verbatim
def create_child_return_len : Nat := 0xba5a26f8

-- @@ L618-618 verbatim
def create_child_returndata : Nat := 0xba5c2800

-- @@ L619-619 verbatim
def create_child_stack : Nat := 0xba5a2780

-- @@ L620-620 verbatim
def create_child_status : Nat := 0xba5a26e0

-- @@ L621-621 verbatim
def create_child_target_be : Nat := 0xba5a2740

-- @@ L622-622 verbatim
def create_child_value_be : Nat := 0xba5a2760

-- @@ L623-623 verbatim
def create_execute_initcode_frame : Nat := 0x8003132c

-- @@ L624-624 verbatim
def create_init_offset : Nat := 0xba5a2610

-- @@ L625-625 verbatim
def create_init_size : Nat := 0xba5a2618

-- @@ L626-626 verbatim
def create_nonce : Nat := 0xba5a2608

-- @@ L627-627 verbatim
def create_salt_be : Nat := 0xba5a2640

-- @@ L628-628 verbatim
def create_sender_be : Nat := 0xba5a2620

-- @@ L629-629 verbatim
def create_stage_initcode_frame : Nat := 0x80031214

-- @@ L630-630 verbatim
def current_block_access_index : Nat := 0xa0b038c8

-- @@ L631-631 verbatim
def cvbgm_field : Nat := 0xa3a0b908

-- @@ L632-632 verbatim
def cvbgm_iter_i : Nat := 0xa3a0b918

-- @@ L633-633 verbatim
def cvbgm_iter_ptr : Nat := 0xa3a0b910

-- @@ L634-634 verbatim
def cvbgum_field : Nat := 0xa3a0b920

-- @@ L635-635 verbatim
def cvbgum_iter_i : Nat := 0xa3a0b930

-- @@ L636-636 verbatim
def cvbgum_iter_ptr : Nat := 0xa3a0b928

-- @@ L637-637 verbatim
def cvcn_iter_child : Nat := 0xa3a0b960

-- @@ L638-638 verbatim
def cvcn_iter_i : Nat := 0xa3a0b968

-- @@ L639-639 verbatim
def cvcn_iter_prev : Nat := 0xa3a0b970

-- @@ L640-640 verbatim
def cvcn_num : Nat := 0xa3a0b958

-- @@ L641-641 verbatim
def cvedl_iter_i : Nat := 0xa3a0b8e0

-- @@ L642-642 verbatim
def cvedl_iter_ptr : Nat := 0xa3a0b8d8

-- @@ L643-643 verbatim
def cvedl_length : Nat := 0xa3a0b8d0

-- @@ L644-644 verbatim
def cvedl_offset : Nat := 0xa3a0b8c8

-- @@ L645-645 verbatim
def cvgul_gas_limit : Nat := 0xa3a0b8f0

-- @@ L646-646 verbatim
def cvgul_gas_used : Nat := 0xa3a0b8e8

-- @@ L647-647 verbatim
def cvgul_iter_i : Nat := 0xa3a0b900

-- @@ L648-648 verbatim
def cvgul_iter_ptr : Nat := 0xa3a0b8f8

-- @@ L649-649 verbatim
def cvit_iter_child : Nat := 0xa3a0b940

-- @@ L650-650 verbatim
def cvit_iter_i : Nat := 0xa3a0b948

-- @@ L651-651 verbatim
def cvit_iter_prev : Nat := 0xa3a0b950

-- @@ L652-652 verbatim
def cvit_ts : Nat := 0xa3a0b938

-- @@ L653-653 verbatim
def cvpmf_empty_hash : Nat := 0xa0b00440

-- @@ L654-654 verbatim
def cvpmf_field : Nat := 0xa3a0b8a0

-- @@ L655-655 verbatim
def cvpmf_iter_i : Nat := 0xa3a0b8c0

-- @@ L656-656 verbatim
def cvpmf_iter_ptr : Nat := 0xa3a0b8b8

-- @@ L657-657 verbatim
def cvpmf_length : Nat := 0xa3a0b8b0

-- @@ L658-658 verbatim
def cvpmf_offset : Nat := 0xa3a0b8a8

-- @@ L659-659 verbatim
def dbsr_cbody : Nat := 0xb9dfe4e0

-- @@ L660-660 verbatim
def dbsr_ccode : Nat := 0xb9dfdca0

-- @@ L661-661 verbatim
def dbsr_clen : Nat := 0xb9dfdcc8

-- @@ L662-662 verbatim
def dbsr_exec : Nat := 0xb9dfdcb0

-- @@ L663-663 verbatim
def dbsr_in_clen : Nat := 0xb9dfdca8

-- @@ L664-664 verbatim
def dbsr_saved_ra : Nat := 0xb9dfdc98

-- @@ L665-665 verbatim
def dbsr_staging : Nat := 0xb9dfdcb8

-- @@ L666-666 verbatim
def dbsr_wbody : Nat := 0xb9dfdce0

-- @@ L667-667 verbatim
def dbsr_wlen : Nat := 0xb9dfdcc0

-- @@ L668-668 verbatim
def derive_builder_deposit_requests : Nat := 0x8005369c

-- @@ L669-669 verbatim
def derive_builder_exit_requests : Nat := 0x800536b8

-- @@ L670-670 verbatim
def derive_consolidation_requests : Nat := 0x80053680

-- @@ L671-671 verbatim
def derive_withdrawal_requests : Nat := 0x80053664

-- @@ L672-672 verbatim
def dispatch_loop : Nat := 0x8003067c

-- @@ L673-673 verbatim
def dispatch_loop_body : Nat := 0x800307d8

-- @@ L674-674 verbatim
def dispatch_resume : Nat := 0x80030818

-- @@ L675-675 verbatim
def dispatcher_capture_exec_state_gas : Nat := 0x8002b17c

-- @@ L676-676 verbatim
def dispatcher_capture_exec_state_gas_differential : Nat := 0x8002b1a0

-- @@ L677-677 verbatim
def dispatcher_tx_gas_settle : Nat := 0x80032e7c

-- @@ L678-678 verbatim
def e77w_authority : Nat := 0xaa8438b8

-- @@ L679-679 verbatim
def e77w_chain : Nat := 0xaa8438a8

-- @@ L680-680 verbatim
def e77w_count : Nat := 0xaa843890

-- @@ L681-681 verbatim
def e77w_nonce : Nat := 0xaa8438b0

-- @@ L682-682 verbatim
def e77w_scratch : Nat := 0xaa8438d0

-- @@ L683-683 verbatim
def e77w_tlen : Nat := 0xaa8438a0

-- @@ L684-684 verbatim
def e77w_toff : Nat := 0xaa843898

-- @@ L685-685 verbatim
def eahsr_acct_struct : Nat := 0xba5a2420

-- @@ L686-686 verbatim
def eahsr_empty_code_hash : Nat := 0xa0b03a80

-- @@ L687-687 verbatim
def eahsr_state_root : Nat := 0xba5a23e0

-- @@ L688-688 verbatim
def ecc_acct_struct : Nat := 0xba5a24e0

-- @@ L689-689 verbatim
def ecc_empty_code_hash : Nat := 0xa0b03aa0

-- @@ L690-690 verbatim
def ecc_match_len : Nat := 0xba5a2560

-- @@ L691-691 verbatim
def ecc_match_offset : Nat := 0xba5a2558

-- @@ L692-692 verbatim
def ecc_state_root : Nat := 0xba5a24c0

-- @@ L693-693 verbatim
def eccp_codes_len : Nat := 0xba5a2550

-- @@ L694-694 verbatim
def eccp_codes_ptr : Nat := 0xba5a2548

-- @@ L695-695 verbatim
def ecsahsr_acct_struct : Nat := 0xab7048e0

-- @@ L696-696 verbatim
def ecsahsr_code_len : Nat := 0xab704748

-- @@ L697-697 verbatim
def ecsahsr_dummy_offset : Nat := 0xab704740

-- @@ L698-698 verbatim
def ecsahsr_empty_code_hash : Nat := 0xa0b00c60

-- @@ L699-699 verbatim
def ecsahsr_state_root : Nat := 0xab704860

-- @@ L700-700 verbatim
def edd_be32_eq : Nat := 0x80054054

-- @@ L701-701 verbatim
def edd_memcpy : Nat := 0x800540b0

-- @@ L702-702 verbatim
def eip1559_calc_base_fee_per_gas : Nat := 0x8000b73c

-- @@ L703-703 verbatim
def eip7702_auth_code_next : Nat := 0xb8d23980

-- @@ L704-704 verbatim
def eip7702_auth_code_slots : Nat := 0xb8d23988

-- @@ L705-705 verbatim
def eip7702_auth_state_prepare : Nat := 0x80029c1c

-- @@ L706-706 verbatim
def eip7702_authority_asof : Nat := 0x80029818

-- @@ L707-707 verbatim
def eip7702_authorization_extract_signature : Nat := 0x80029378

-- @@ L708-708 verbatim
def eip7702_authorization_recover_address : Nat := 0x800294f4

-- @@ L709-709 verbatim
def eip7702_authorization_signing_hash : Nat := 0x800294d0

-- @@ L710-710 verbatim
def eip7702_warm_recovered_authorities : Nat := 0x80029688

-- @@ L711-711 verbatim
def eip7778_remaining_block_gas_check : Nat := 0x80028f30

-- @@ L712-712 verbatim
def eip7778_remaining_block_gas_from_results : Nat := 0x80028fd0

-- @@ L713-713 verbatim
def eip8037_block_gas_used : Nat := 0x80026c48

-- @@ L714-714 verbatim
def eip8037_prior_state_used_exact : Nat := 0x80027ea4

-- @@ L715-715 verbatim
def eip8037_tx_gas_gate : Nat := 0x80027f50

-- @@ L716-716 verbatim
def eip8037_tx_state_gas : Nat := 0x80026ae0

-- @@ L717-717 verbatim
def empty_ommers_hash : Nat := 0xa0b00a60

-- @@ L718-718 verbatim
def enrg_u32le : Nat := 0x8002b150

-- @@ L719-719 verbatim
def eph_len : Nat := 0xa438b980

-- @@ L720-720 verbatim
def eph_off : Nat := 0xa438b978

-- @@ L721-721 verbatim
def eph_u32le : Nat := 0x8000cff4

-- @@ L722-722 verbatim
def erh_blob : Nat := 0xa53e9420

-- @@ L723-723 verbatim
def erh_digests : Nat := 0xa53e9360

-- @@ L724-724 verbatim
def erh_hash_one : Nat := 0x8000cd9c

-- @@ L725-725 verbatim
def evm_access_account_count : Nat := 0xbb4156a8

-- @@ L726-726 verbatim
def evm_access_account_table : Nat := 0xbb4156c0

-- @@ L727-727 verbatim
def evm_call_depth : Nat := 0xbb4054c8

-- @@ L728-728 verbatim
def evm_cur_stack_top : Nat := 0xa0b03b00

-- @@ L729-729 verbatim
def evm_env : Nat := 0xb9e975b0

-- @@ L730-730 verbatim
def evm_halt_flag : Nat := 0xbb4054d0

-- @@ L731-731 verbatim
def evm_memory_pool : Nat := 0xb2386c00

-- @@ L732-732 verbatim
def evm_oldest_ancestor_offset : Nat := 0xa5edbef8

-- @@ L733-733 verbatim
def evm_refund_acc : Nat := 0xb9e030f0

-- @@ L734-734 verbatim
def evm_sparse_memory_epoch_by_depth : Nat := 0xb9e5d5a8

-- @@ L735-735 verbatim
def evm_sparse_memory_next_epoch : Nat := 0xa0b038d0

-- @@ L736-736 verbatim
def evm_state_gas_left : Nat := 0xb9e0d4f8

-- @@ L737-737 verbatim
def evm_state_gas_spilled : Nat := 0xb9e0d508

-- @@ L738-738 verbatim
def evm_state_gas_used : Nat := 0xb9e0d500

-- @@ L739-739 verbatim
def exec_code_effect_count : Nat := 0xba602800

-- @@ L740-740 verbatim
def exec_code_effect_log : Nat := 0xba602818

-- @@ L741-741 verbatim
def exec_code_effect_next : Nat := 0xba602808

-- @@ L742-742 verbatim
def exec_code_effect_overflow : Nat := 0xba602810

-- @@ L743-743 verbatim
def exec_log_addr_to_bal_canonical : Nat := 0x80020700

-- @@ L744-744 verbatim
def exec_nonstorage_effect_count : Nat := 0xba7b0f00

-- @@ L745-745 verbatim
def exec_nonstorage_effect_log : Nat := 0xba7b0f20

-- @@ L746-746 verbatim
def exec_nonstorage_effect_overflow : Nat := 0xba7b0f08

-- @@ L747-747 verbatim
def execution_requests_hash : Nat := 0x8000cb80

-- @@ L748-748 verbatim
def exit_outofgas : Nat := 0x80052ee0

-- @@ L749-749 verbatim
def extcodecopy_at_header_state_root : Nat := 0x80030e1c

-- @@ L750-750 verbatim
def extcodehash_at_header_state_root : Nat := 0x80030cbc

-- @@ L751-751 verbatim
def extcodesize_at_header_state_root : Nat := 0x80006994

-- @@ L752-752 verbatim
def extract_deposit_data : Nat := 0x80053f24

-- @@ L753-753 verbatim
def extract_parent_header_and_state_root : Nat := 0x8000d024

-- @@ L754-754 verbatim
def extract_payload_and_withdrawals : Nat := 0x8000d140

-- @@ L755-755 verbatim
def extract_witness_state_section : Nat := 0x8000d25c

-- @@ L756-756 verbatim
def find_code_effect_by_address : Nat := 0x80031868

-- @@ L757-757 verbatim
def find_code_effect_by_hash : Nat := 0x800318c8

-- @@ L758-758 verbatim
def frame_base : Nat := 0x8003c6ec

-- @@ L759-759 verbatim
def frame_depth_pop : Nat := 0x8003c71c

-- @@ L760-760 verbatim
def frame_depth_push : Nat := 0x8003c704

-- @@ L761-761 verbatim
def frame_load_regs : Nat := 0x8003c750

-- @@ L762-762 verbatim
def frame_parent_bases : Nat := 0xbb411520

-- @@ L763-763 verbatim
def frame_save_area : Nat := 0xbb4054e0

-- @@ L764-764 verbatim
def frame_save_regs : Nat := 0x8003c734

-- @@ L765-765 verbatim
def h_ADD : Nat := 0x80040a74

-- @@ L766-766 verbatim
def h_ADDMOD : Nat := 0x80051b24

-- @@ L767-767 verbatim
def h_ADDRESS : Nat := 0x800421d0

-- @@ L768-768 verbatim
def h_AND : Nat := 0x8004112c

-- @@ L769-769 verbatim
def h_BALANCE : Nat := 0x800442d0

-- @@ L770-770 verbatim
def h_BASEFEE : Nat := 0x80042590

-- @@ L771-771 verbatim
def h_BLOBBASEFEE : Nat := 0x80042630

-- @@ L772-772 verbatim
def h_BLOBHASH : Nat := 0x80042680

-- @@ L773-773 verbatim
def h_BLOCKHASH : Nat := 0x80042718

-- @@ L774-774 verbatim
def h_BYTE : Nat := 0x800412e8

-- @@ L775-775 verbatim
def h_CALL : Nat := 0x80049b50

-- @@ L776-776 verbatim
def h_CALLCODE : Nat := 0x8004bdfc

-- @@ L777-777 verbatim
def h_CALLDATACOPY : Nat := 0x80042a64

-- @@ L778-778 verbatim
def h_CALLDATALOAD : Nat := 0x80042848

-- @@ L779-779 verbatim
def h_CALLDATASIZE : Nat := 0x80042804

-- @@ L780-780 verbatim
def h_CALLER : Nat := 0x80042270

-- @@ L781-781 verbatim
def h_CALLVALUE : Nat := 0x800422c0

-- @@ L782-782 verbatim
def h_CHAINID : Nat := 0x800424f0

-- @@ L783-783 verbatim
def h_CLZ : Nat := 0x800418c8

-- @@ L784-784 verbatim
def h_CODECOPY : Nat := 0x80042c78

-- @@ L785-785 verbatim
def h_CODESIZE : Nat := 0x80042c34

-- @@ L786-786 verbatim
def h_COINBASE : Nat := 0x80042360

-- @@ L787-787 verbatim
def h_CREATE : Nat := 0x80048d88

-- @@ L788-788 verbatim
def h_CREATE2 : Nat := 0x8004dbd8

-- @@ L789-789 verbatim
def h_DELEGATECALL : Nat := 0x8004cf74

-- @@ L790-790 verbatim
def h_DIV : Nat := 0x8004fefc

-- @@ L791-791 verbatim
def h_DUP1 : Nat := 0x8003f9a0

-- @@ L792-792 verbatim
def h_DUP10 : Nat := 0x8003fdd8

-- @@ L793-793 verbatim
def h_DUP11 : Nat := 0x8003fe50

-- @@ L794-794 verbatim
def h_DUP12 : Nat := 0x8003fec8

-- @@ L795-795 verbatim
def h_DUP13 : Nat := 0x8003ff40

-- @@ L796-796 verbatim
def h_DUP14 : Nat := 0x8003ffb8

-- @@ L797-797 verbatim
def h_DUP15 : Nat := 0x80040030

-- @@ L798-798 verbatim
def h_DUP16 : Nat := 0x800400a8

-- @@ L799-799 verbatim
def h_DUP2 : Nat := 0x8003fa18

-- @@ L800-800 verbatim
def h_DUP3 : Nat := 0x8003fa90

-- @@ L801-801 verbatim
def h_DUP4 : Nat := 0x8003fb08

-- @@ L802-802 verbatim
def h_DUP5 : Nat := 0x8003fb80

-- @@ L803-803 verbatim
def h_DUP6 : Nat := 0x8003fbf8

-- @@ L804-804 verbatim
def h_DUP7 : Nat := 0x8003fc70

-- @@ L805-805 verbatim
def h_DUP8 : Nat := 0x8003fce8

-- @@ L806-806 verbatim
def h_DUP9 : Nat := 0x8003fd60

-- @@ L807-807 verbatim
def h_DUPN : Nat := 0x80040820

-- @@ L808-808 verbatim
def h_EQ : Nat := 0x80041048

-- @@ L809-809 verbatim
def h_EXCHANGE : Nat := 0x8004098c

-- @@ L810-810 verbatim
def h_EXP : Nat := 0x80052454

-- @@ L811-811 verbatim
def h_EXTCODECOPY : Nat := 0x80044eec

-- @@ L812-812 verbatim
def h_EXTCODEHASH : Nat := 0x80044880

-- @@ L813-813 verbatim
def h_EXTCODESIZE : Nat := 0x80044578

-- @@ L814-814 verbatim
def h_GAS : Nat := 0x8004218c

-- @@ L815-815 verbatim
def h_GASLIMIT : Nat := 0x800424a0

-- @@ L816-816 verbatim
def h_GASPRICE : Nat := 0x80042310

-- @@ L817-817 verbatim
def h_GT : Nat := 0x80040e88

-- @@ L818-818 verbatim
def h_INVALID : Nat := 0x80047658

-- @@ L819-819 verbatim
def h_ISZERO : Nat := 0x800410cc

-- @@ L820-820 verbatim
def h_JUMP : Nat := 0x80042e4c

-- @@ L821-821 verbatim
def h_JUMPDEST : Nat := 0x80042e44

-- @@ L822-822 verbatim
def h_JUMPI : Nat := 0x80042f0c

-- @@ L823-823 verbatim
def h_KECCAK256 : Nat := 0x80043044

-- @@ L824-824 verbatim
def h_LOG0 : Nat := 0x800432cc

-- @@ L825-825 verbatim
def h_LOG1 : Nat := 0x800435c0

-- @@ L826-826 verbatim
def h_LOG2 : Nat := 0x800438d4

-- @@ L827-827 verbatim
def h_LOG3 : Nat := 0x80043c08

-- @@ L828-828 verbatim
def h_LOG4 : Nat := 0x80043f5c

-- @@ L829-829 verbatim
def h_LT : Nat := 0x80040df0

-- @@ L830-830 verbatim
def h_MCOPY : Nat := 0x8004645c

-- @@ L831-831 verbatim
def h_MLOAD : Nat := 0x800419fc

-- @@ L832-832 verbatim
def h_MOD : Nat := 0x800507f0

-- @@ L833-833 verbatim
def h_MSIZE : Nat := 0x80042148

-- @@ L834-834 verbatim
def h_MSTORE : Nat := 0x80041d48

-- @@ L835-835 verbatim
def h_MSTORE8 : Nat := 0x80042028

-- @@ L836-836 verbatim
def h_MUL : Nat := 0x80040b1c

-- @@ L837-837 verbatim
def h_MULMOD : Nat := 0x8004f644

-- @@ L838-838 verbatim
def h_NOT : Nat := 0x80041288

-- @@ L839-839 verbatim
def h_NUMBER : Nat := 0x80042400

-- @@ L840-840 verbatim
def h_OR : Nat := 0x800411a0

-- @@ L841-841 verbatim
def h_ORIGIN : Nat := 0x80042220

-- @@ L842-842 verbatim
def h_PC : Nat := 0x80043000

-- @@ L843-843 verbatim
def h_POP : Nat := 0x800419c8

-- @@ L844-844 verbatim
def h_PREVRANDAO : Nat := 0x80042450

-- @@ L845-845 verbatim
def h_PUSH0 : Nat := 0x8003e0e0

-- @@ L846-846 verbatim
def h_PUSH1 : Nat := 0x8003e120

-- @@ L847-847 verbatim
def h_PUSH10 : Nat := 0x8003e4c8

-- @@ L848-848 verbatim
def h_PUSH11 : Nat := 0x8003e558

-- @@ L849-849 verbatim
def h_PUSH12 : Nat := 0x8003e5f0

-- @@ L850-850 verbatim
def h_PUSH13 : Nat := 0x8003e690

-- @@ L851-851 verbatim
def h_PUSH14 : Nat := 0x8003e738

-- @@ L852-852 verbatim
def h_PUSH15 : Nat := 0x8003e7e8

-- @@ L853-853 verbatim
def h_PUSH16 : Nat := 0x8003e8a0

-- @@ L854-854 verbatim
def h_PUSH17 : Nat := 0x8003e960

-- @@ L855-855 verbatim
def h_PUSH18 : Nat := 0x8003ea28

-- @@ L856-856 verbatim
def h_PUSH19 : Nat := 0x8003eaf8

-- @@ L857-857 verbatim
def h_PUSH2 : Nat := 0x8003e168

-- @@ L858-858 verbatim
def h_PUSH20 : Nat := 0x8003ebd0

-- @@ L859-859 verbatim
def h_PUSH21 : Nat := 0x8003ecb0

-- @@ L860-860 verbatim
def h_PUSH22 : Nat := 0x8003ed98

-- @@ L861-861 verbatim
def h_PUSH23 : Nat := 0x8003ee88

-- @@ L862-862 verbatim
def h_PUSH24 : Nat := 0x8003ef80

-- @@ L863-863 verbatim
def h_PUSH25 : Nat := 0x8003f080

-- @@ L864-864 verbatim
def h_PUSH26 : Nat := 0x8003f188

-- @@ L865-865 verbatim
def h_PUSH27 : Nat := 0x8003f298

-- @@ L866-866 verbatim
def h_PUSH28 : Nat := 0x8003f3b0

-- @@ L867-867 verbatim
def h_PUSH29 : Nat := 0x8003f4d0

-- @@ L868-868 verbatim
def h_PUSH3 : Nat := 0x8003e1b8

-- @@ L869-869 verbatim
def h_PUSH30 : Nat := 0x8003f5f8

-- @@ L870-870 verbatim
def h_PUSH31 : Nat := 0x8003f728

-- @@ L871-871 verbatim
def h_PUSH32 : Nat := 0x8003f860

-- @@ L872-872 verbatim
def h_PUSH4 : Nat := 0x8003e210

-- @@ L873-873 verbatim
def h_PUSH5 : Nat := 0x8003e270

-- @@ L874-874 verbatim
def h_PUSH6 : Nat := 0x8003e2d8

-- @@ L875-875 verbatim
def h_PUSH7 : Nat := 0x8003e348

-- @@ L876-876 verbatim
def h_PUSH8 : Nat := 0x8003e3c0

-- @@ L877-877 verbatim
def h_PUSH9 : Nat := 0x8003e440

-- @@ L878-878 verbatim
def h_RETURN : Nat := 0x800466dc

-- @@ L879-879 verbatim
def h_RETURNDATACOPY : Nat := 0x80048be4

-- @@ L880-880 verbatim
def h_RETURNDATASIZE : Nat := 0x80048b98

-- @@ L881-881 verbatim
def h_REVERT : Nat := 0x80047074

-- @@ L882-882 verbatim
def h_SAR : Nat := 0x80041714

-- @@ L883-883 verbatim
def h_SDIV : Nat := 0x80050d8c

-- @@ L884-884 verbatim
def h_SDIV_done : Nat := 0x80051438

-- @@ L885-885 verbatim
def h_SELFBALANCE : Nat := 0x80042540

-- @@ L886-886 verbatim
def h_SELFDESTRUCT : Nat := 0x80047674

-- @@ L887-887 verbatim
def h_SGT : Nat := 0x80040fb4

-- @@ L888-888 verbatim
def h_SHL : Nat := 0x800413d4

-- @@ L889-889 verbatim
def h_SHR : Nat := 0x80041574

-- @@ L890-890 verbatim
def h_SIGNEXTEND : Nat := 0x80040cf8

-- @@ L891-891 verbatim
def h_SLOAD : Nat := 0x80045494

-- @@ L892-892 verbatim
def h_SLOTNUM : Nat := 0x800425e0

-- @@ L893-893 verbatim
def h_SLT : Nat := 0x80040f20

-- @@ L894-894 verbatim
def h_SMOD : Nat := 0x80051458

-- @@ L895-895 verbatim
def h_SMOD_done : Nat := 0x80051b04

-- @@ L896-896 verbatim
def h_SSTORE : Nat := 0x80045a14

-- @@ L897-897 verbatim
def h_STATICCALL : Nat := 0x8004e9e0

-- @@ L898-898 verbatim
def h_STOP : Nat := 0x800527a0

-- @@ L899-899 verbatim
def h_SUB : Nat := 0x80040c50

-- @@ L900-900 verbatim
def h_SWAP1 : Nat := 0x80040120

-- @@ L901-901 verbatim
def h_SWAP10 : Nat := 0x80040510

-- @@ L902-902 verbatim
def h_SWAP11 : Nat := 0x80040580

-- @@ L903-903 verbatim
def h_SWAP12 : Nat := 0x800405f0

-- @@ L904-904 verbatim
def h_SWAP13 : Nat := 0x80040660

-- @@ L905-905 verbatim
def h_SWAP14 : Nat := 0x800406d0

-- @@ L906-906 verbatim
def h_SWAP15 : Nat := 0x80040740

-- @@ L907-907 verbatim
def h_SWAP16 : Nat := 0x800407b0

-- @@ L908-908 verbatim
def h_SWAP2 : Nat := 0x80040190

-- @@ L909-909 verbatim
def h_SWAP3 : Nat := 0x80040200

-- @@ L910-910 verbatim
def h_SWAP4 : Nat := 0x80040270

-- @@ L911-911 verbatim
def h_SWAP5 : Nat := 0x800402e0

-- @@ L912-912 verbatim
def h_SWAP6 : Nat := 0x80040350

-- @@ L913-913 verbatim
def h_SWAP7 : Nat := 0x800403c0

-- @@ L914-914 verbatim
def h_SWAP8 : Nat := 0x80040430

-- @@ L915-915 verbatim
def h_SWAP9 : Nat := 0x800404a0

-- @@ L916-916 verbatim
def h_SWAPN : Nat := 0x800408d8

-- @@ L917-917 verbatim
def h_TIMESTAMP : Nat := 0x800423b0

-- @@ L918-918 verbatim
def h_TLOAD : Nat := 0x800462a0

-- @@ L919-919 verbatim
def h_TSTORE : Nat := 0x8004638c

-- @@ L920-920 verbatim
def h_XOR : Nat := 0x80041214

-- @@ L921-921 verbatim
def h_invalid : Nat := 0x80052910

-- @@ L922-922 verbatim
def has_code_or_nonce_at_header_state_root : Nat := 0x800310bc

-- @@ L923-923 verbatim
def hcon_acct_struct : Nat := 0xbb405458

-- @@ L924-924 verbatim
def hcon_empty_code_hash : Nat := 0xa0b03ae0

-- @@ L925-925 verbatim
def hcon_empty_trie_root : Nat := 0xa0b03ac0

-- @@ L926-926 verbatim
def hcon_predicate : Nat := 0xbb4054c0

-- @@ L927-927 verbatim
def hcon_state_root : Nat := 0xbb405438

-- @@ L928-928 verbatim
def header_extended_decode : Nat := 0x8000bbc0

-- @@ L929-929 verbatim
def header_extended_decode_arity_check : Nat := 0x8000be78

-- @@ L930-930 verbatim
def header_extract_logs_bloom : Nat := 0x80015c90

-- @@ L931-931 verbatim
def header_extract_number : Nat := 0x80026590

-- @@ L932-932 verbatim
def header_extract_receipts_root : Nat := 0x80015094

-- @@ L933-933 verbatim
def header_extract_state_root : Nat := 0x8000cee4

-- @@ L934-934 verbatim
def header_extract_withdrawals_root : Nat := 0x8000ace4

-- @@ L935-935 verbatim
def header_validate_base_fee : Nat := 0x8000b874

-- @@ L936-936 verbatim
def header_validate_excess_blob_gas : Nat := 0x8000b8d8

-- @@ L937-937 verbatim
def header_validate_extra_data_length : Nat := 0x8000b2f4

-- @@ L938-938 verbatim
def header_validate_parent_hash : Nat := 0x8000c0d4

-- @@ L939-939 verbatim
def header_validate_post_merge : Nat := 0x8000b05c

-- @@ L940-940 verbatim
def headers_keccak_array : Nat := 0x8001ae78

-- @@ L941-941 verbatim
def headers_parent_hash : Nat := 0x8000c04c

-- @@ L942-942 verbatim
def headers_validate_chain : Nat := 0x8001af24

-- @@ L943-943 verbatim
def helb_length : Nat := 0xaa050e18

-- @@ L944-944 verbatim
def helb_offset : Nat := 0xaa050e10

-- @@ L945-945 verbatim
def herr_length : Nat := 0xaa050e08

-- @@ L946-946 verbatim
def herr_offset : Nat := 0xaa050e00

-- @@ L947-947 verbatim
def hesr_length : Nat := 0xa438b970

-- @@ L948-948 verbatim
def hesr_offset : Nat := 0xa438b968

-- @@ L949-949 verbatim
def hewr_length : Nat := 0xa9f8ac60

-- @@ L950-950 verbatim
def hewr_offset : Nat := 0xa9f8ac58

-- @@ L951-951 verbatim
def hp_decode_nibbles : Nat := 0x800046fc

-- @@ L952-952 verbatim
def hp_encode_nibbles : Nat := 0x800047c8

-- @@ L953-953 verbatim
def hvbf_expected : Nat := 0xa438a6a0

-- @@ L954-954 verbatim
def hvebg_threshold : Nat := 0xa438a6c0

-- @@ L955-955 verbatim
def hved_len : Nat := 0xa438a6f8

-- @@ L956-956 verbatim
def hved_off : Nat := 0xa438a6f0

-- @@ L957-957 verbatim
def hvph_claimed : Nat := 0xa438a720

-- @@ L958-958 verbatim
def hvph_computed : Nat := 0xa438a740

-- @@ L959-959 verbatim
def ins_empty_branch : Nat := 0xa0b00d50

-- @@ L960-960 verbatim
def ins_k : Nat := 0xb83c7830

-- @@ L961-961 verbatim
def ins_kcount : Nat := 0xb83c6fc0

-- @@ L962-962 verbatim
def ins_lv_len : Nat := 0xb83c6fd0

-- @@ L963-963 verbatim
def ins_lv_ptr : Nat := 0xb83c6fc8

-- @@ L964-964 verbatim
def ins_m : Nat := 0xb83c6fd8

-- @@ L965-965 verbatim
def ins_meta : Nat := 0xb83c7000

-- @@ L966-966 verbatim
def ins_niba : Nat := 0xb83c6fe0

-- @@ L967-967 verbatim
def ins_nibb : Nat := 0xb83c6fe8

-- @@ L968-968 verbatim
def ins_node : Nat := 0xb83c80b0

-- @@ L969-969 verbatim
def ins_node2 : Nat := 0xb84c80b0

-- @@ L970-970 verbatim
def ins_node2_len : Nat := 0xb83c6ff0

-- @@ L971-971 verbatim
def ins_node_len : Nat := 0xb83c6fa0

-- @@ L972-972 verbatim
def ins_ref : Nat := 0xb83c8030

-- @@ L973-973 verbatim
def ins_ref2 : Nat := 0xb83c8070

-- @@ L974-974 verbatim
def ins_ref2_len : Nat := 0xb83c6ff8

-- @@ L975-975 verbatim
def ins_ref_len : Nat := 0xb83c6fa8

-- @@ L976-976 verbatim
def ins_stack : Nat := 0xb83c7030

-- @@ L977-977 verbatim
def ins_wl : Nat := 0xb83c6f98

-- @@ L978-978 verbatim
def intrinsic_gas_amsterdam_counts : Nat := 0x80027d7c

-- @@ L979-979 verbatim
def itr_changes : Nat := 0xa9fab598

-- @@ L980-980 verbatim
def itr_empty_witness : Nat := 0xa9f8acc0

-- @@ L981-981 verbatim
def itr_paths : Nat := 0xa9f8acc8

-- @@ L982-982 verbatim
def iw_empty_trie_root : Nat := 0xa0b00d30

-- @@ L983-983 verbatim
def iwd_hash : Nat := 0xb83c6f78

-- @@ L984-984 verbatim
def iwd_len : Nat := 0xb83c6f70

-- @@ L985-985 verbatim
def iwd_ptr : Nat := 0xb83c6f68

-- @@ L986-986 verbatim
def keccak_absorb : Nat := 0x80023aa0

-- @@ L987-987 verbatim
def keccak_final : Nat := 0x80023b14

-- @@ L988-988 verbatim
def keccak_init : Nat := 0x80023a84

-- @@ L989-989 verbatim
def lba_length : Nat := 0xa9e86584

-- @@ L990-990 verbatim
def lba_offset : Nat := 0xa9e8657c

-- @@ L991-991 verbatim
def lba_topic_count : Nat := 0xa9e8659c

-- @@ L992-992 verbatim
def lba_topics_length : Nat := 0xa9e86594

-- @@ L993-993 verbatim
def lba_topics_offset : Nat := 0xa9e8658c

-- @@ L994-994 verbatim
def llba_count : Nat := 0xa9e865b4

-- @@ L995-995 verbatim
def llba_length : Nat := 0xa9e865ac

-- @@ L996-996 verbatim
def llba_offset : Nat := 0xa9e865a4

-- @@ L997-997 verbatim
def log_bloom_add : Nat := 0x80014e0c

-- @@ L998-998 verbatim
def log_records_encode_rlp : Nat := 0x80014948

-- @@ L999-999 verbatim
def logs_list_bloom_add : Nat := 0x80014fb8

-- @@ L1000-1000 verbatim
def lrr_addr_be : Nat := 0xa9c86968

-- @@ L1001-1001 verbatim
def lrr_dhdr : Nat := 0xa9c869a0

-- @@ L1002-1002 verbatim
def lrr_inner : Nat := 0xa9c86a38

-- @@ L1003-1003 verbatim
def lrr_len : Nat := 0xa9c86960

-- @@ L1004-1004 verbatim
def lrr_payload : Nat := 0xa9c86b38

-- @@ L1005-1005 verbatim
def lrr_topic_be : Nat := 0xa9c86980

-- @@ L1006-1006 verbatim
def lrr_topics : Nat := 0xa9c869b0

-- @@ L1007-1007 verbatim
def m28_blob_stage_count : Nat := 0xb85ceb10

-- @@ L1008-1008 verbatim
def m28_blob_stage_table : Nat := 0xb85ceb18

-- @@ L1009-1009 verbatim
def m29_hash_tmp : Nat := 0xb85ced20

-- @@ L1010-1010 verbatim
def m29_len_tmp : Nat := 0xb85ced48

-- @@ L1011-1011 verbatim
def m29_off_tmp : Nat := 0xb85ced40

-- @@ L1012-1012 verbatim
def m29_stage_count : Nat := 0xb85ccb08

-- @@ L1013-1013 verbatim
def m29_stage_cur : Nat := 0xb85ccb00

-- @@ L1014-1014 verbatim
def m29_stage_table : Nat := 0xb85ccb10

-- @@ L1015-1015 verbatim
def map_account_apply_post_fields : Nat := 0x8000e5f0

-- @@ L1016-1016 verbatim
def map_account_change_value : Nat := 0x8000f90c

-- @@ L1017-1017 verbatim
def mbc_length : Nat := 0xa3a4c210

-- @@ L1018-1018 verbatim
def mbc_offset : Nat := 0xa3a4c208

-- @@ L1019-1019 verbatim
def mdacc_child_len : Nat := 0xab706dd8

-- @@ L1020-1020 verbatim
def mdacc_child_ptr : Nat := 0xab706dd0

-- @@ L1021-1021 verbatim
def mdacc_collapsed_path : Nat := 0xab707e48

-- @@ L1022-1022 verbatim
def mdacc_ext_path_len : Nat := 0xab706de8

-- @@ L1023-1023 verbatim
def mdacc_leaf_path : Nat := 0xab707648

-- @@ L1024-1024 verbatim
def mdacc_leaf_path_len : Nat := 0xab706de0

-- @@ L1025-1025 verbatim
def mdacc_leaf_value_len : Nat := 0xab706df8

-- @@ L1026-1026 verbatim
def mdacc_leaf_value_ptr : Nat := 0xab706df0

-- @@ L1027-1027 verbatim
def mdacc_survivor_nibble : Nat := 0xab706dc8

-- @@ L1028-1028 verbatim
def mdacc_witness_len : Nat := 0xab706dc0

-- @@ L1029-1029 verbatim
def mee_path_len : Nat := 0xab706e08

-- @@ L1030-1030 verbatim
def mee_path_off : Nat := 0xab706e00

-- @@ L1031-1031 verbatim
def message_value_transfer_recipient_post : Nat := 0xb8d23960

-- @@ L1032-1032 verbatim
def message_value_transfer_sender_post : Nat := 0xb8d23940

-- @@ L1033-1033 verbatim
def mle_path_len : Nat := 0xb83c6fb8

-- @@ L1034-1034 verbatim
def mle_path_off : Nat := 0xb83c6fb0

-- @@ L1035-1035 verbatim
def mlk_keccak_buf : Nat := 0xab704880

-- @@ L1036-1036 verbatim
def mlk_nibble_buf : Nat := 0xab7048a0

-- @@ L1037-1037 verbatim
def mlnen_cursor : Nat := 0xa3a4cad0

-- @@ L1038-1038 verbatim
def mlnen_field_len : Nat := 0xa3a4cac0

-- @@ L1039-1039 verbatim
def mlnen_hp_buf : Nat := 0xa3a4cae0

-- @@ L1040-1040 verbatim
def mlnen_hp_len : Nat := 0xa3a4cac8

-- @@ L1041-1041 verbatim
def mlnen_payload_buf : Nat := 0xa3a4cee0

-- @@ L1042-1042 verbatim
def mlnen_total_payload : Nat := 0xa3a4cad8

-- @@ L1043-1043 verbatim
def mnk_item_count : Nat := 0xa3a4c200

-- @@ L1044-1044 verbatim
def mnk_path_length : Nat := 0xa3a4c1f8

-- @@ L1045-1045 verbatim
def mnk_path_offset : Nat := 0xa3a4c1f0

-- @@ L1046-1046 verbatim
def modexp_iszero : Nat := 0x800321bc

-- @@ L1047-1047 verbatim
def mpt_branch_child : Nat := 0x800045c8

-- @@ L1048-1048 verbatim
def mpt_delete_acc : Nat := 0x80007580

-- @@ L1049-1049 verbatim
def mpt_delete_walk_db : Nat := 0x800073fc

-- @@ L1050-1050 verbatim
def mpt_extension_extract : Nat := 0x80007400

-- @@ L1051-1051 verbatim
def mpt_extension_node_encode : Nat := 0x800083f8

-- @@ L1052-1052 verbatim
def mpt_indexed_large_leaf_hash : Nat := 0x80009bcc

-- @@ L1053-1053 verbatim
def mpt_indexed_stream_leaf_hash : Nat := 0x8000a28c

-- @@ L1054-1054 verbatim
def mpt_indexed_trie_root_bounded_from_values : Nat := 0x8000ab74

-- @@ L1055-1055 verbatim
def mpt_indexed_trie_root_large : Nat := 0x80009da0

-- @@ L1056-1056 verbatim
def mpt_indexed_trie_root_one_leaf : Nat := 0x8000999c

-- @@ L1057-1057 verbatim
def mpt_indexed_trie_root_small : Nat := 0x8000a094

-- @@ L1058-1058 verbatim
def mpt_insert_acc : Nat := 0x80008af4

-- @@ L1059-1059 verbatim
def mpt_insert_walk_db : Nat := 0x800085e4

-- @@ L1060-1060 verbatim
def mpt_leaf_extract : Nat := 0x80008274

-- @@ L1061-1061 verbatim
def mpt_leaf_node_encode_from_nibbles : Nat := 0x80005490

-- @@ L1062-1062 verbatim
def mpt_lookup_by_key : Nat := 0x80006548

-- @@ L1063-1063 verbatim
def mpt_node_kind : Nat := 0x800044f4

-- @@ L1064-1064 verbatim
def mpt_node_resolve : Nat := 0x80006c50

-- @@ L1065-1065 verbatim
def mpt_node_slot_encode : Nat := 0x80005684

-- @@ L1066-1066 verbatim
def mpt_one_leaf_root_indexed : Nat := 0x8000976c

-- @@ L1067-1067 verbatim
def mpt_resolve_cache_reset : Nat := 0x80006c2c

-- @@ L1068-1068 verbatim
def mpt_set_acc : Nat := 0x80007218

-- @@ L1069-1069 verbatim
def mpt_set_record_walk_db : Nat := 0x80006e10

-- @@ L1070-1070 verbatim
def mpt_splice_slot : Nat := 0x80005c64

-- @@ L1071-1071 verbatim
def mpt_state_root : Nat := 0x80008158

-- @@ L1072-1072 verbatim
def mpt_state_root_ins : Nat := 0x800095b8

-- @@ L1073-1073 verbatim
def mpt_walk : Nat := 0x80006054

-- @@ L1074-1074 verbatim
def mset_cursor : Nat := 0xa3b4cf20

-- @@ L1075-1075 verbatim
def mset_db_count : Nat := 0xa3b4df98

-- @@ L1076-1076 verbatim
def mset_db_data : Nat := 0xa3b86020

-- @@ L1077-1077 verbatim
def mset_db_hash : Nat := 0xa3b4dfe0

-- @@ L1078-1078 verbatim
def mset_db_top : Nat := 0xa3b4dfa0

-- @@ L1079-1079 verbatim
def mset_dr_root : Nat := 0xa4386020

-- @@ L1080-1080 verbatim
def mset_head_len : Nat := 0xa3b4cef8

-- @@ L1081-1081 verbatim
def mset_memcpy : Nat := 0x80005c44

-- @@ L1082-1082 verbatim
def mset_meta : Nat := 0xa3b4cf38

-- @@ L1083-1083 verbatim
def mset_new_payload_len : Nat := 0xa3b4cf10

-- @@ L1084-1084 verbatim
def mset_node : Nat := 0xa3b4d798

-- @@ L1085-1085 verbatim
def mset_node_len : Nat := 0xa3b4cf28

-- @@ L1086-1086 verbatim
def mset_payload_start : Nat := 0xa3b4cef0

-- @@ L1087-1087 verbatim
def mset_prefix_len : Nat := 0xa3b4cf18

-- @@ L1088-1088 verbatim
def mset_ref : Nat := 0xa3b4d758

-- @@ L1089-1089 verbatim
def mset_ref_len : Nat := 0xa3b4cf30

-- @@ L1090-1090 verbatim
def mset_res_cache_data : Nat := 0xa3b56000

-- @@ L1091-1091 verbatim
def mset_res_cache_valid : Nat := 0xa3b4e000

-- @@ L1092-1092 verbatim
def mset_res_len : Nat := 0xa3b4dfb0

-- @@ L1093-1093 verbatim
def mset_res_off : Nat := 0xa3b4dfa8

-- @@ L1094-1094 verbatim
def mset_rw_len : Nat := 0xa3b4dfc0

-- @@ L1095-1095 verbatim
def mset_rw_ptr : Nat := 0xa3b4dfb8

-- @@ L1096-1096 verbatim
def mset_span_size : Nat := 0xa3b4cee8

-- @@ L1097-1097 verbatim
def mset_span_start : Nat := 0xa3b4cee0

-- @@ L1098-1098 verbatim
def mset_stack : Nat := 0xa3b4cf58

-- @@ L1099-1099 verbatim
def mset_tail_len : Nat := 0xa3b4cf08

-- @@ L1100-1100 verbatim
def mset_tail_start : Nat := 0xa3b4cf00

-- @@ L1101-1101 verbatim
def mtoli_leaf_buf : Nat := 0xa55b32a8

-- @@ L1102-1102 verbatim
def mtoli_leaf_len : Nat := 0xa55b32a0

-- @@ L1103-1103 verbatim
def mtoli_nibbles : Nat := 0xa55b3298

-- @@ L1104-1104 verbatim
def multi_tx_nth_context : Nat := 0x800268b0

-- @@ L1105-1105 verbatim
def multi_tx_running_sender_balance_step : Nat := 0x80028878

-- @@ L1106-1106 verbatim
def mw_child_length : Nat := 0xa3a4c298

-- @@ L1107-1107 verbatim
def mw_child_offset : Nat := 0xa3a4c290

-- @@ L1108-1108 verbatim
def mw_is_leaf : Nat := 0xa3a4c2b8

-- @@ L1109-1109 verbatim
def mw_lookup_hash : Nat := 0xa3a4c220

-- @@ L1110-1110 verbatim
def mw_lookup_length : Nat := 0xa3a4c248

-- @@ L1111-1111 verbatim
def mw_lookup_offset : Nat := 0xa3a4c240

-- @@ L1112-1112 verbatim
def mw_nibble_buf : Nat := 0xa3a4c2c0

-- @@ L1113-1113 verbatim
def mw_nibble_count : Nat := 0xa3a4c2b0

-- @@ L1114-1114 verbatim
def mw_path_length : Nat := 0xa3a4c288

-- @@ L1115-1115 verbatim
def mw_path_offset : Nat := 0xa3a4c280

-- @@ L1116-1116 verbatim
def mw_value_length : Nat := 0xa3a4c2a8

-- @@ L1117-1117 verbatim
def mw_value_offset : Nat := 0xa3a4c2a0

-- @@ L1118-1118 verbatim
def mxne_cursor : Nat := 0xb85c80c0

-- @@ L1119-1119 verbatim
def mxne_field_len : Nat := 0xb85c80b0

-- @@ L1120-1120 verbatim
def mxne_hp_buf : Nat := 0xb85c80d0

-- @@ L1121-1121 verbatim
def mxne_hp_len : Nat := 0xb85c80b8

-- @@ L1122-1122 verbatim
def mxne_payload_buf : Nat := 0xb85c84d0

-- @@ L1123-1123 verbatim
def mxne_total_payload : Nat := 0xb85c80c8

-- @@ L1124-1124 verbatim
def node_db_append : Nat := 0x80006ae8

-- @@ L1125-1125 verbatim
def node_db_lookup : Nat := 0x80006ba8

-- @@ L1126-1126 verbatim
def nonce_acct_struct : Nat := 0xba5a25a0

-- @@ L1127-1127 verbatim
def nonce_at_header_state_root : Nat := 0x800309d0

-- @@ L1128-1128 verbatim
def nonce_state_root : Nat := 0xba5a2580

-- @@ L1129-1129 verbatim
def nonstorage_effect_latest_balance : Nat := 0x8003d408

-- @@ L1130-1130 verbatim
def nonstorage_effect_latest_nonce : Nat := 0x8003d498

-- @@ L1131-1131 verbatim
def nse_zero_bal : Nat := 0xbb4053c0

-- @@ L1132-1132 verbatim
def opcode_gas_costs : Nat := 0xa0b04310

-- @@ L1133-1133 verbatim
def opcode_handlers : Nat := 0xa0b04b10

-- @@ L1134-1134 verbatim
def p256_a_be : Nat := 0xa0b03208

-- @@ L1135-1135 verbatim
def p256_acc : Nat := 0xb9e09e20

-- @@ L1136-1136 verbatim
def p256_be_to_le : Nat := 0x80037594

-- @@ L1137-1137 verbatim
def p256_chord_tail : Nat := 0x80037794

-- @@ L1138-1138 verbatim
def p256_copy_n : Nat := 0x800374c8

-- @@ L1139-1139 verbatim
def p256_den : Nat := 0xb9e09de0

-- @@ L1140-1140 verbatim
def p256_eq32 : Nat := 0x80037518

-- @@ L1141-1141 verbatim
def p256_inv_out : Nat := 0xb9e09e00

-- @@ L1142-1142 verbatim
def p256_is_zero_n : Nat := 0x800374e8

-- @@ L1143-1143 verbatim
def p256_lam : Nat := 0xb9e09d80

-- @@ L1144-1144 verbatim
def p256_le_a : Nat := 0xb9e09d00

-- @@ L1145-1145 verbatim
def p256_le_b : Nat := 0xb9e09d20

-- @@ L1146-1146 verbatim
def p256_le_d : Nat := 0xb9e09d40

-- @@ L1147-1147 verbatim
def p256_le_to_be : Nat := 0x800375e4

-- @@ L1148-1148 verbatim
def p256_lt_be : Nat := 0x80037554

-- @@ L1149-1149 verbatim
def p256_one_be : Nat := 0xa0b03248

-- @@ L1150-1150 verbatim
def p256_op_with : Nat := 0x80037630

-- @@ L1151-1151 verbatim
def p256_pb_add_p : Nat := 0xa0b03390

-- @@ L1152-1152 verbatim
def p256_pb_mul_p : Nat := 0xa0b03368

-- @@ L1153-1153 verbatim
def p256_pb_sub_p : Nat := 0xa0b033b8

-- @@ L1154-1154 verbatim
def p256_pm2_be : Nat := 0xa0b03268

-- @@ L1155-1155 verbatim
def p256_point_add : Nat := 0x80037a34

-- @@ L1156-1156 verbatim
def p256_point_dbl : Nat := 0x800378bc

-- @@ L1157-1157 verbatim
def p256_pow : Nat := 0x8003769c

-- @@ L1158-1158 verbatim
def p256_ptmp : Nat := 0xb9e09f40

-- @@ L1159-1159 verbatim
def p256_scalar_mul : Nat := 0x80037b50

-- @@ L1160-1160 verbatim
def p256_t1 : Nat := 0xb9e09da0

-- @@ L1161-1161 verbatim
def p256_t2 : Nat := 0xb9e09dc0

-- @@ L1162-1162 verbatim
def parse_deposit_requests : Nat := 0x80053e24

-- @@ L1163-1163 verbatim
def pbsst_code_len : Nat := 0xb9dfdc90

-- @@ L1164-1164 verbatim
def pbsst_code_ptr : Nat := 0xb9dfdc88

-- @@ L1165-1165 verbatim
def pbsst_saved_ra : Nat := 0xb9dfdc80

-- @@ L1166-1166 verbatim
def pdr_deposit_addr : Nat := 0xa0b00de8

-- @@ L1167-1167 verbatim
def pdr_deposit_sig : Nat := 0xa0b00e00

-- @@ L1168-1168 verbatim
def priority_fee_per_gas_eip1559 : Nat := 0x80027140

-- @@ L1169-1169 verbatim
def process_block_start_system_transactions : Nat := 0x80053a24

-- @@ L1170-1170 verbatim
def public_keys_valid : Nat := 0x80014038

-- @@ L1171-1171 verbatim
def rdg_halt_kind : Nat := 0xb9e030f8

-- @@ L1172-1172 verbatim
def re_cursor : Nat := 0xa9a45340

-- @@ L1173-1173 verbatim
def re_field_len : Nat := 0xa9a45338

-- @@ L1174-1174 verbatim
def re_payload_buf : Nat := 0xa9a45450

-- @@ L1175-1175 verbatim
def re_total_payload : Nat := 0xa9a45348

-- @@ L1176-1176 verbatim
def read_sets_discard_tx : Nat := 0x800262b8

-- @@ L1177-1177 verbatim
def read_sets_incorporate_tx : Nat := 0x800261c0

-- @@ L1178-1178 verbatim
def read_sets_merge_one : Nat := 0x8002609c

-- @@ L1179-1179 verbatim
def receipt_encode : Nat := 0x80015374

-- @@ L1180-1180 verbatim
def receipt_extract_logs_bloom : Nat := 0x80015814

-- @@ L1181-1181 verbatim
def record_message_value_transfer : Nat := 0x80033b18

-- @@ L1182-1182 verbatim
def record_nonstorage_effect : Nat := 0x8003d218

-- @@ L1183-1183 verbatim
def record_nonstorage_effect_nonce_only_after_account_state : Nat := 0x8003d224

-- @@ L1184-1184 verbatim
def relb_length : Nat := 0xa9c45458

-- @@ L1185-1185 verbatim
def relb_offset : Nat := 0xa9c45450

-- @@ L1186-1186 verbatim
def requests_hash_verify : Nat := 0x8005434c

-- @@ L1187-1187 verbatim
def rfu_length : Nat := 0xa4386848

-- @@ L1188-1188 verbatim
def rfu_offset : Nat := 0xa4386840

-- @@ L1189-1189 verbatim
def rhv_hash : Nat := 0xb9e02d08

-- @@ L1190-1190 verbatim
def rlp_bytes_encoded_size : Nat := 0x8000c804

-- @@ L1191-1191 verbatim
def rlp_content_to_u256_be : Nat := 0x80005368

-- @@ L1192-1192 verbatim
def rlp_content_to_u256_be_strict : Nat := 0x80005428

-- @@ L1193-1193 verbatim
def rlp_content_to_u64 : Nat := 0x80005320

-- @@ L1194-1194 verbatim
def rlp_content_to_u64_strict : Nat := 0x800053d0

-- @@ L1195-1195 verbatim
def rlp_encode_bytes : Nat := 0x80004834

-- @@ L1196-1196 verbatim
def rlp_encode_list_prefix : Nat := 0x800049f0

-- @@ L1197-1197 verbatim
def rlp_encode_u64 : Nat := 0x800152a8

-- @@ L1198-1198 verbatim
def rlp_encode_uint_be : Nat := 0x80004964

-- @@ L1199-1199 verbatim
def rlp_field_to_u64 : Nat := 0x8000328c

-- @@ L1200-1200 verbatim
def rlp_field_to_u64_strict : Nat := 0x80019e24

-- @@ L1201-1201 verbatim
def rlp_item_size : Nat := 0x80004aa8

-- @@ L1202-1202 verbatim
def rlp_item_span : Nat := 0x80004b34

-- @@ L1203-1203 verbatim
def rlp_list_count_items : Nat := 0x80019b3c

-- @@ L1204-1204 verbatim
def rlp_list_encoded_size : Nat := 0x8000c854

-- @@ L1205-1205 verbatim
def rlp_list_nth_item : Nat := 0x80002f84

-- @@ L1206-1206 verbatim
def rlp_list_truncate_to_n_fields : Nat := 0x8002b28c

-- @@ L1207-1207 verbatim
def rlp_prefix_to_buffer : Nat := 0x80009b60

-- @@ L1208-1208 verbatim
def rlp_recursive_decode : Nat := 0x80004fe0

-- @@ L1209-1209 verbatim
def rlp_recursive_decode_frame : Nat := 0xbf5e2000

-- @@ L1210-1210 verbatim
def rlp_recursive_decode_items : Nat := 0x80005188

-- @@ L1211-1211 verbatim
def rlp_recursive_decode_read_be : Nat := 0x800052fc

-- @@ L1212-1212 verbatim
def rlp_validate_payload : Nat := 0x80004df0

-- @@ L1213-1213 verbatim
def rlp_walk_init : Nat := 0x80004c18

-- @@ L1214-1214 verbatim
def rlp_walk_next : Nat := 0x80004cec

-- @@ L1215-1215 verbatim
def rlp_walk_next_core : Nat := 0x80004e44

-- @@ L1216-1216 verbatim
def rlp_walk_next_leaf : Nat := 0x8000bb84

-- @@ L1217-1217 verbatim
def rlp_walk_next_shared : Nat := 0x80004d20

-- @@ L1218-1218 verbatim
def rltn_length_hi : Nat := 0xa3a2bef0

-- @@ L1219-1219 verbatim
def rltn_offset_hi : Nat := 0xa3a2bee8

-- @@ L1220-1220 verbatim
def rltn_prefix_len : Nat := 0xa3a2bef8

-- @@ L1221-1221 verbatim
def rsbd_code_len : Nat := 0xb9e02df0

-- @@ L1222-1222 verbatim
def rsbd_code_ptr : Nat := 0xb9e02de8

-- @@ L1223-1223 verbatim
def runtime_access_account_seed : Nat := 0x80032f6c

-- @@ L1224-1224 verbatim
def runtime_dispatcher_call : Nat := 0x8002fac0

-- @@ L1225-1225 verbatim
def runtime_dispatcher_input_ptr : Nat := 0xb9e02d38

-- @@ L1226-1226 verbatim
def runtime_same_block_delegation_code : Nat := 0x80031000

-- @@ L1227-1227 verbatim
def runtime_tx_access_list_address_count : Nat := 0xb9e030e0

-- @@ L1228-1228 verbatim
def runtime_tx_access_list_storage_key_count : Nat := 0xb9e030e8

-- @@ L1229-1229 verbatim
def runtime_tx_account_read_suppress : Nat := 0xb9e02d88

-- @@ L1230-1230 verbatim
def runtime_tx_auth_code_effect_count_checkpoint : Nat := 0xb86b3108

-- @@ L1231-1231 verbatim
def runtime_tx_auth_code_effect_next_checkpoint : Nat := 0xb86b3110

-- @@ L1232-1232 verbatim
def runtime_tx_auth_code_effect_overflow_checkpoint : Nat := 0xb86b3120

-- @@ L1233-1233 verbatim
def runtime_tx_auth_effect_count_checkpoint : Nat := 0xb86b3100

-- @@ L1234-1234 verbatim
def runtime_tx_auth_effect_overflow_checkpoint : Nat := 0xb86b3118

-- @@ L1235-1235 verbatim
def runtime_tx_auth_exec_fn : Nat := 0xb9e02d78

-- @@ L1236-1236 verbatim
def runtime_tx_auth_phase_halted : Nat := 0xb9e02d80

-- @@ L1237-1237 verbatim
def runtime_tx_auth_prepared : Nat := 0xb9e030b8

-- @@ L1238-1238 verbatim
def runtime_tx_auth_regular_refund : Nat := 0xb9e02dd8

-- @@ L1239-1239 verbatim
def runtime_tx_auth_state_charge : Nat := 0xb9e02dc0

-- @@ L1240-1240 verbatim
def runtime_tx_auth_state_charged : Nat := 0xb9e02dd0

-- @@ L1241-1241 verbatim
def runtime_tx_auth_state_refund : Nat := 0xb9e02db8

-- @@ L1242-1242 verbatim
def runtime_tx_auth_state_used : Nat := 0xb9e02dc8

-- @@ L1243-1243 verbatim
def runtime_tx_calldata_floor : Nat := 0xb9e03068

-- @@ L1244-1244 verbatim
def runtime_tx_intrinsic_regular : Nat := 0xb9e030a0

-- @@ L1245-1245 verbatim
def runtime_tx_settle_regular_gas_left : Nat := 0xb9e03080

-- @@ L1246-1246 verbatim
def runtime_tx_settle_state_gas_left : Nat := 0xb9e03088

-- @@ L1247-1247 verbatim
def runtime_tx_settle_state_gas_used : Nat := 0xb9e03090

-- @@ L1248-1248 verbatim
def runtime_tx_state_gas_entry_valid : Nat := 0xbbbcc970

-- @@ L1249-1249 verbatim
def runtime_tx_state_gas_message_left : Nat := 0xb9e0d520

-- @@ L1250-1250 verbatim
def runtime_tx_state_gas_message_spilled : Nat := 0xb9e0d528

-- @@ L1251-1251 verbatim
def runtime_tx_state_gas_ptr : Nat := 0xb9e02d90

-- @@ L1252-1252 verbatim
def runtime_tx_state_reservoir_initial : Nat := 0xb9e03098

-- @@ L1253-1253 verbatim
def runtime_tx_top_frame_regular_gas : Nat := 0xb9e030a8

-- @@ L1254-1254 verbatim
def sahsr_acct_struct : Nat := 0xb85cc600

-- @@ L1255-1255 verbatim
def sahsr_state_root : Nat := 0xb85cc5e0

-- @@ L1256-1256 verbatim
def sahsr_u256 : Nat := 0xb85cc680

-- @@ L1257-1257 verbatim
def scc_ctx : Nat := 0xb9dfdba0

-- @@ L1258-1258 verbatim
def scc_system_addr : Nat := 0xa0b00d70

-- @@ L1259-1259 verbatim
def sdbt_delta32 : Nat := 0xba5a23c0

-- @@ L1260-1260 verbatim
def sdfg_gascost : Nat := 0xb8b22d40

-- @@ L1261-1261 verbatim
def secc_add_params : Nat := 0xa0b009d0

-- @@ L1262-1262 verbatim
def secc_le_p1 : Nat := 0xa0b00950

-- @@ L1263-1263 verbatim
def secc_le_p2 : Nat := 0xa0b00990

-- @@ L1264-1264 verbatim
def secc_point_tmp : Nat := 0xa0b00910

-- @@ L1265-1265 verbatim
def secf_add_mod_p : Nat := 0x8001f848

-- @@ L1266-1266 verbatim
def secf_arith_params_n : Nat := 0xa0b00868

-- @@ L1267-1267 verbatim
def secf_arith_params_p : Nat := 0xa0b00840

-- @@ L1268-1268 verbatim
def secf_be_to_le : Nat := 0x8001f69c

-- @@ L1269-1269 verbatim
def secf_cmp : Nat := 0xa3a0bc50

-- @@ L1270-1270 verbatim
def secf_copy32 : Nat := 0x8001f664

-- @@ L1271-1271 verbatim
def secf_eq32 : Nat := 0x8001f78c

-- @@ L1272-1272 verbatim
def secf_get_bit_lsb : Nat := 0x8001f738

-- @@ L1273-1273 verbatim
def secf_inv_mod_n : Nat := 0x8001fcec

-- @@ L1274-1274 verbatim
def secf_is_zero32 : Nat := 0x8001f75c

-- @@ L1275-1275 verbatim
def secf_le_a : Nat := 0xa0b00780

-- @@ L1276-1276 verbatim
def secf_le_b : Nat := 0xa0b007a0

-- @@ L1277-1277 verbatim
def secf_le_d : Nat := 0xa0b007c0

-- @@ L1278-1278 verbatim
def secf_le_to_be : Nat := 0x8001f6ec

-- @@ L1279-1279 verbatim
def secf_mul_mod_n : Nat := 0x8001fbb4

-- @@ L1280-1280 verbatim
def secf_mul_mod_p : Nat := 0x8001f8d4

-- @@ L1281-1281 verbatim
def secf_n_be : Nat := 0xa0b00720

-- @@ L1282-1282 verbatim
def secf_n_c_be : Nat := 0xa0b00740

-- @@ L1283-1283 verbatim
def secf_n_minus_2_be : Nat := 0xa0b00760

-- @@ L1284-1284 verbatim
def secf_pow_base : Nat := 0xa3a0bc78

-- @@ L1285-1285 verbatim
def secf_pow_mod_n : Nat := 0x8001fc24

-- @@ L1286-1286 verbatim
def secf_pow_mod_p : Nat := 0x8001f944

-- @@ L1287-1287 verbatim
def secf_pow_result : Nat := 0xa3a0bc58

-- @@ L1288-1288 verbatim
def secf_pow_verify : Nat := 0xa3a0bc98

-- @@ L1289-1289 verbatim
def secf_recover_cmp : Nat := 0xa3a0bcb8

-- @@ L1290-1290 verbatim
def secf_recover_rhs : Nat := 0xa3a0bce0

-- @@ L1291-1291 verbatim
def secf_recover_t : Nat := 0xa3a0bcc0

-- @@ L1292-1292 verbatim
def secf_reduce_once : Nat := 0x8001f7c8

-- @@ L1293-1293 verbatim
def secf_reduce_once_n : Nat := 0x8001fb34

-- @@ L1294-1294 verbatim
def secf_sqrt_mod_p : Nat := 0x8001fa0c

-- @@ L1295-1295 verbatim
def secf_square_mod_n : Nat := 0x8001fc1c

-- @@ L1296-1296 verbatim
def secf_square_mod_p : Nat := 0x8001f93c

-- @@ L1297-1297 verbatim
def secf_tmp0 : Nat := 0xa3a0bc30

-- @@ L1298-1298 verbatim
def secf_zero32 : Nat := 0x8001f688

-- @@ L1299-1299 verbatim
def secp256k1_b_be : Nat := 0xa0b00a00

-- @@ L1300-1300 verbatim
def secp256k1_c_be : Nat := 0xa0b006a0

-- @@ L1301-1301 verbatim
def secp256k1_generator : Nat := 0xa0b00890

-- @@ L1302-1302 verbatim
def secp256k1_n_be : Nat := 0xa0b009e0

-- @@ L1303-1303 verbatim
def secp256k1_one_be : Nat := 0xa0b006c0

-- @@ L1304-1304 verbatim
def secp256k1_p_be : Nat := 0xa0b00680

-- @@ L1305-1305 verbatim
def secp256k1_p_minus_2_be : Nat := 0xa0b006e0

-- @@ L1306-1306 verbatim
def secp256k1_point_add : Nat := 0x8001fdfc

-- @@ L1307-1307 verbatim
def secp256k1_point_copy64 : Nat := 0x8001ff50

-- @@ L1308-1308 verbatim
def secp256k1_point_double : Nat := 0x8001fd54

-- @@ L1309-1309 verbatim
def secp256k1_point_zero64 : Nat := 0x8001ff74

-- @@ L1310-1310 verbatim
def secp256k1_recover_pubkey_staged : Nat := 0x800201c4

-- @@ L1311-1311 verbatim
def secp256k1_recover_r : Nat := 0x8002009c

-- @@ L1312-1312 verbatim
def secp256k1_scalar_mul : Nat := 0x8001ff90

-- @@ L1313-1313 verbatim
def selfdestruct_balance_transfer : Nat := 0x80033374

-- @@ L1314-1314 verbatim
def sender_debit_from_gas : Nat := 0x800289b0

-- @@ L1315-1315 verbatim
def sg_load_u32le : Nat := 0x800020c0

-- @@ L1316-1316 verbatim
def sg_memcpy : Nat := 0x800020f0

-- @@ L1317-1317 verbatim
def sg_validate_fixed_list : Nat := 0x80002110

-- @@ L1318-1318 verbatim
def sha256_w_input : Nat := 0xa3a0a938

-- @@ L1319-1319 verbatim
def sha256_w_iv : Nat := 0xa0b00000

-- @@ L1320-1320 verbatim
def sha256_w_params : Nat := 0xa0b00020

-- @@ L1321-1321 verbatim
def sha256_w_state : Nat := 0xa3a0a918

-- @@ L1322-1322 verbatim
def si_value_len : Nat := 0xb85cc4d0

-- @@ L1323-1323 verbatim
def si_value_scratch : Nat := 0xb85cc4e0

-- @@ L1324-1324 verbatim
def simple_transfer_intrinsic_gas : Nat := 0x80015d8c

-- @@ L1325-1325 verbatim
def single_leaf_trie_root : Nat := 0x8000d64c

-- @@ L1326-1326 verbatim
def slot_at_header_state_root : Nat := 0x8001cbec

-- @@ L1327-1327 verbatim
def slot_at_index : Nat := 0x8001cb54

-- @@ L1328-1328 verbatim
def slot_decode_u256 : Nat := 0x8001cad4

-- @@ L1329-1329 verbatim
def sltr_cursor : Nat := 0xa55aa688

-- @@ L1330-1330 verbatim
def sltr_field_len : Nat := 0xa55aa670

-- @@ L1331-1331 verbatim
def sltr_hp_buf : Nat := 0xa55aae98

-- @@ L1332-1332 verbatim
def sltr_hp_len : Nat := 0xa55aa680

-- @@ L1333-1333 verbatim
def sltr_nibble_count : Nat := 0xa55aa678

-- @@ L1334-1334 verbatim
def sltr_nibbles : Nat := 0xa55aa698

-- @@ L1335-1335 verbatim
def sltr_node_buf : Nat := 0xa55af298

-- @@ L1336-1336 verbatim
def sltr_payload_buf : Nat := 0xa55ab298

-- @@ L1337-1337 verbatim
def sltr_total_payload : Nat := 0xa55aa690

-- @@ L1338-1338 verbatim
def spw_u32le : Nat := 0x8000d110

-- @@ L1339-1339 verbatim
def sri_cur_mode : Nat := 0xab706ce0

-- @@ L1340-1340 verbatim
def sri_fail_index : Nat := 0xab706ce8

-- @@ L1341-1341 verbatim
def sri_fail_mode : Nat := 0xab706cf0

-- @@ L1342-1342 verbatim
def sri_fail_status : Nat := 0xab706cf8

-- @@ L1343-1343 verbatim
def srpc_env_base : Nat := 0xb85ccaf8

-- @@ L1344-1344 verbatim
def srss_key : Nat := 0xa55b72c0

-- @@ L1345-1345 verbatim
def srss_rlpval : Nat := 0xa55b72e0

-- @@ L1346-1346 verbatim
def srss_rlpval_len : Nat := 0xa55b7308

-- @@ L1347-1347 verbatim
def ssc_calldata_len : Nat := 0xb9dfdc78

-- @@ L1348-1348 verbatim
def ssc_calldata_ptr : Nat := 0xb9dfdc70

-- @@ L1349-1349 verbatim
def ssc_saved_ra : Nat := 0xb9dfdc60

-- @@ L1350-1350 verbatim
def ssc_saved_s0 : Nat := 0xb9dfdc68

-- @@ L1351-1351 verbatim
def ssz_ew_field_roots : Nat := 0xa3a0aa80

-- @@ L1352-1352 verbatim
def ssz_hash_tree_root_bytes : Nat := 0x80001d84

-- @@ L1353-1353 verbatim
def ssz_hash_tree_root_list_bytelist : Nat := 0x80001e5c

-- @@ L1354-1354 verbatim
def ssz_hb_chunks : Nat := 0xbfd80000

-- @@ L1355-1355 verbatim
def ssz_hb_mix : Nat := 0xa3a0a9e0

-- @@ L1356-1356 verbatim
def ssz_hb_partial : Nat := 0xa3a0a9c0

-- @@ L1357-1357 verbatim
def ssz_ltb_child_roots : Nat := 0xbff80000

-- @@ L1358-1358 verbatim
def ssz_ltb_mix : Nat := 0xa3a0aa40

-- @@ L1359-1359 verbatim
def ssz_ltb_partial : Nat := 0xa3a0aa20

-- @@ L1360-1360 verbatim
def ssz_merkleize : Nat := 0x80001be4

-- @@ L1361-1361 verbatim
def ssz_merkleize_padded : Nat := 0xbfb80000

-- @@ L1362-1362 verbatim
def ssz_merkleize_partial : Nat := 0xa3a0a980

-- @@ L1363-1363 verbatim
def ssz_merkleize_pow2 : Nat := 0x80001afc

-- @@ L1364-1364 verbatim
def ssz_merkleize_scratch : Nat := 0xbf980000

-- @@ L1365-1365 verbatim
def ssz_pack_bytes : Nat := 0x80001aa4

-- @@ L1366-1366 verbatim
def ssz_tx_list_versioned_hashes_match : Nat := 0x8001a3fc

-- @@ L1367-1367 verbatim
def ssz_withdrawal_to_rlp : Nat := 0x8000d2f4

-- @@ L1368-1368 verbatim
def ssz_zero_hashes : Nat := 0xa0b00040

-- @@ L1369-1369 verbatim
def stage_blockhash_m29 : Nat := 0x800262e0

-- @@ L1370-1370 verbatim
def stage_runtime_payload_code : Nat := 0x8001cf64

-- @@ L1371-1371 verbatim
def stage_runtime_payload_witness_context : Nat := 0x8001d444

-- @@ L1372-1372 verbatim
def stage_system_call : Nat := 0x800536d4

-- @@ L1373-1373 verbatim
def stage_system_call_payload : Nat := 0x800537f0

-- @@ L1374-1374 verbatim
def stateless_verdict_from_ssz : Nat := 0x8000d45c

-- @@ L1375-1375 verbatim
def step2_verdict : Nat := 0x8000cdf8

-- @@ L1376-1376 verbatim
def storage_read_record : Nat := 0x80020730

-- @@ L1377-1377 verbatim
def storage_read_record_block : Nat := 0x800208c0

-- @@ L1378-1378 verbatim
def storage_reads_count : Nat := 0xb9dfdb70

-- @@ L1379-1379 verbatim
def storage_reads_overflow : Nat := 0xb9dfdb78

-- @@ L1380-1380 verbatim
def storage_root_single_slot : Nat := 0x8000d808

-- @@ L1381-1381 verbatim
def storage_write_record : Nat := 0x80020a3c

-- @@ L1382-1382 verbatim
def storage_writes_block_latest_value : Nat := 0x800205b8

-- @@ L1383-1383 verbatim
def storage_writes_block_upsert : Nat := 0x80020e10

-- @@ L1384-1384 verbatim
def storage_writes_count : Nat := 0xb9deba68

-- @@ L1385-1385 verbatim
def storage_writes_overflow : Nat := 0xb9deba70

-- @@ L1386-1386 verbatim
def storage_writes_undo_count : Nat := 0xb9deba88

-- @@ L1387-1387 verbatim
def storage_writes_undo_push : Nat := 0x8002109c

-- @@ L1388-1388 verbatim
def sttc_base_fee_be : Nat := 0xaa843b60

-- @@ L1389-1389 verbatim
def sttc_nonce : Nat := 0xaa843aa8

-- @@ L1390-1390 verbatim
def sv_params : Nat := 0xa438b100

-- @@ L1391-1391 verbatim
def sv_pre_rlp_len : Nat := 0xb86d3cb0

-- @@ L1392-1392 verbatim
def sv_pre_rlp_ptr : Nat := 0xb86d3ca8

-- @@ L1393-1393 verbatim
def sv_recomputed : Nat := 0xa438b0e0

-- @@ L1394-1394 verbatim
def sv_this_rlp : Nat := 0xa438b568

-- @@ L1395-1395 verbatim
def sv_this_rlp_len : Nat := 0xa438b0c8

-- @@ L1396-1396 verbatim
def svf_codes_len : Nat := 0xaa845438

-- @@ L1397-1397 verbatim
def svf_codes_ptr : Nat := 0xaa845430

-- @@ L1398-1398 verbatim
def svf_descriptors : Nat := 0xa438baa0

-- @@ L1399-1399 verbatim
def svf_parent_rlp : Nat := 0xa438ba48

-- @@ L1400-1400 verbatim
def svf_parent_rlp_len : Nat := 0xa438ba50

-- @@ L1401-1401 verbatim
def svf_parent_sr : Nat := 0xa438ba60

-- @@ L1402-1402 verbatim
def svf_payload : Nat := 0xa438ba20

-- @@ L1403-1403 verbatim
def svf_rlp_arena : Nat := 0xa438bba0

-- @@ L1404-1404 verbatim
def svf_wd_len : Nat := 0xa438ba58

-- @@ L1405-1405 verbatim
def svf_wds_count : Nat := 0xa438ba30

-- @@ L1406-1406 verbatim
def svf_wds_ptr : Nat := 0xa438ba28

-- @@ L1407-1407 verbatim
def svf_witness : Nat := 0xa438ba38

-- @@ L1408-1408 verbatim
def svf_witness_len : Nat := 0xa438ba40

-- @@ L1409-1409 verbatim
def svf_zero32 : Nat := 0xa438ba80

-- @@ L1410-1410 verbatim
def swr_be : Nat := 0xa438b998

-- @@ L1411-1411 verbatim
def swr_flen : Nat := 0xa438b988

-- @@ L1412-1412 verbatim
def swr_payload : Nat := 0xa438b9a0

-- @@ L1413-1413 verbatim
def swr_prefix_len : Nat := 0xa438b990

-- @@ L1414-1414 verbatim
def swr_rev_le_be : Nat := 0x8000d2c8

-- @@ L1415-1415 verbatim
def sws_u32le : Nat := 0x8000d22c

-- @@ L1416-1416 verbatim
def system_call_mode : Nat := 0xb9e99a40

-- @@ L1417-1417 verbatim
def system_call_returndata : Nat := 0xb9e99a50

-- @@ L1418-1418 verbatim
def system_call_returndata_len : Nat := 0xb9e99a48

-- @@ L1419-1419 verbatim
def t155_buf : Nat := 0xa3a2bf00

-- @@ L1420-1420 verbatim
def t155_chain_be : Nat := 0xa3a4bf20

-- @@ L1421-1421 verbatim
def t155_chain_enc : Nat := 0xa3a4bf28

-- @@ L1422-1422 verbatim
def t155_length_hi : Nat := 0xa3a4bf18

-- @@ L1423-1423 verbatim
def t155_offset_hi : Nat := 0xa3a4bf10

-- @@ L1424-1424 verbatim
def t155_prefix_len : Nat := 0xa3a4bf38

-- @@ L1425-1425 verbatim
def t48_length : Nat := 0xaa843b58

-- @@ L1426-1426 verbatim
def t48_offset : Nat := 0xaa843b50

-- @@ L1427-1427 verbatim
def tcbg_blob_fee_be : Nat := 0xab706c48

-- @@ L1428-1428 verbatim
def tcbg_struct : Nat := 0xab706b50

-- @@ L1429-1429 verbatim
def tea_inner_off : Nat := 0xaa843ab8

-- @@ L1430-1430 verbatim
def tea_type : Nat := 0xaa843ab0

-- @@ L1431-1431 verbatim
def teds_inner_off : Nat := 0xaa843b38

-- @@ L1432-1432 verbatim
def teds_type : Nat := 0xaa843b30

-- @@ L1433-1433 verbatim
def teer_auth_count : Nat := 0xaa843570

-- @@ L1434-1434 verbatim
def teer_pre_acct : Nat := 0xaa843828

-- @@ L1435-1435 verbatim
def teer_records_ptr : Nat := 0xaa843590

-- @@ L1436-1436 verbatim
def teer_success_count : Nat := 0xb8b23240

-- @@ L1437-1437 verbatim
def teer_success_table : Nat := 0xb8b23268

-- @@ L1438-1438 verbatim
def tefgp_max_fee : Nat := 0xaa843ba0

-- @@ L1439-1439 verbatim
def tefgp_max_priority : Nat := 0xaa843b80

-- @@ L1440-1440 verbatim
def tefgp_tmp : Nat := 0xaa843bc0

-- @@ L1441-1441 verbatim
def tegp_inner_off : Nat := 0xaa843aa0

-- @@ L1442-1442 verbatim
def tegp_type : Nat := 0xaa843a98

-- @@ L1443-1443 verbatim
def teng_inner_off : Nat := 0xaa843a90

-- @@ L1444-1444 verbatim
def teng_type : Nat := 0xaa843a88

-- @@ L1445-1445 verbatim
def tev_inner_off : Nat := 0xaa843b28

-- @@ L1446-1446 verbatim
def tev_type : Nat := 0xaa843b20

-- @@ L1447-1447 verbatim
def tgsbl_addr_len : Nat := 0xaa843a80

-- @@ L1448-1448 verbatim
def tgsbl_addr_off : Nat := 0xaa843a78

-- @@ L1449-1449 verbatim
def tgsbl_count : Nat := 0xaa843a60

-- @@ L1450-1450 verbatim
def tgsbl_row_len : Nat := 0xaa843a70

-- @@ L1451-1451 verbatim
def tgsbl_row_off : Nat := 0xaa843a68

-- @@ L1452-1452 verbatim
def tgsbl_tmp_len : Nat := 0xaa843a58

-- @@ L1453-1453 verbatim
def tgsbl_tmp_off : Nat := 0xaa843a50

-- @@ L1454-1454 verbatim
def tis_inner_off : Nat := 0xaa843b00

-- @@ L1455-1455 verbatim
def tis_is_creation : Nat := 0xaa843af0

-- @@ L1456-1456 verbatim
def tis_to_buf : Nat := 0xaa843ad0

-- @@ L1457-1457 verbatim
def tis_type : Nat := 0xaa843af8

-- @@ L1458-1458 verbatim
def tpr_R : Nat := 0xa3a0bd00

-- @@ L1459-1459 verbatim
def tpr_e : Nat := 0xa3a0bd40

-- @@ L1460-1460 verbatim
def tpr_nege : Nat := 0xa3a0bd60

-- @@ L1461-1461 verbatim
def tpr_p1 : Nat := 0xa3a0bde0

-- @@ L1462-1462 verbatim
def tpr_p2 : Nat := 0xa3a0be20

-- @@ L1463-1463 verbatim
def tpr_rinv : Nat := 0xa3a0bd80

-- @@ L1464-1464 verbatim
def tpr_u1 : Nat := 0xa3a0bda0

-- @@ L1465-1465 verbatim
def tpr_u2 : Nat := 0xa3a0bdc0

-- @@ L1466-1466 verbatim
def tps_cmp : Nat := 0xa3a0be78

-- @@ L1467-1467 verbatim
def tps_inner_off : Nat := 0xa3a0be68

-- @@ L1468-1468 verbatim
def tps_secp256k1_half_n : Nat := 0xa0b00a40

-- @@ L1469-1469 verbatim
def tps_secp256k1_n : Nat := 0xa0b00a20

-- @@ L1470-1470 verbatim
def tps_type : Nat := 0xa3a0be60

-- @@ L1471-1471 verbatim
def tps_v : Nat := 0xa3a0be70

-- @@ L1472-1472 verbatim
def tsh_buf : Nat := 0xa3a0bed0

-- @@ L1473-1473 verbatim
def tvhm_blob_count : Nat := 0xaa845270

-- @@ L1474-1474 verbatim
def tvhm_blob_index : Nat := 0xaa845278

-- @@ L1475-1475 verbatim
def tvhm_hash_len : Nat := 0xaa845288

-- @@ L1476-1476 verbatim
def tvhm_hash_off : Nat := 0xaa845280

-- @@ L1477-1477 verbatim
def tvhm_inner_off : Nat := 0xaa845268

-- @@ L1478-1478 verbatim
def tvhm_struct : Nat := 0xaa845290

-- @@ L1479-1479 verbatim
def tvhm_tx_type : Nat := 0xaa845260

-- @@ L1480-1480 verbatim
def tx_access_list_span : Nat := 0x8001e848

-- @@ L1481-1481 verbatim
def tx_account_reads_count : Nat := 0xb9dfdb50

-- @@ L1482-1482 verbatim
def tx_account_reads_overflow : Nat := 0xb9dfdb58

-- @@ L1483-1483 verbatim
def tx_account_writes_count : Nat := 0xb9dedaa8

-- @@ L1484-1484 verbatim
def tx_account_writes_overflow : Nat := 0xb9dedab0

-- @@ L1485-1485 verbatim
def tx_code_reads_count : Nat := 0xb9dfdb60

-- @@ L1486-1486 verbatim
def tx_code_reads_overflow : Nat := 0xb9dfdb68

-- @@ L1487-1487 verbatim
def tx_effective_gas_pricing : Nat := 0x800271b4

-- @@ L1488-1488 verbatim
def tx_eip1559_decode : Nat := 0x8001ec28

-- @@ L1489-1489 verbatim
def tx_eip1559_extract_signature : Nat := 0x8002b730

-- @@ L1490-1490 verbatim
def tx_eip2930_decode : Nat := 0x8001e9e8

-- @@ L1491-1491 verbatim
def tx_eip2930_extract_signature : Nat := 0x8002b574

-- @@ L1492-1492 verbatim
def tx_eip4844_decode : Nat := 0x80019f78

-- @@ L1493-1493 verbatim
def tx_eip4844_extract_signature : Nat := 0x8002b900

-- @@ L1494-1494 verbatim
def tx_eip4844_validate_blob_hashes : Nat := 0x8001a294

-- @@ L1495-1495 verbatim
def tx_eip7702_decode : Nat := 0x8001ee90

-- @@ L1496-1496 verbatim
def tx_eip7702_extract_signature : Nat := 0x8002baf8

-- @@ L1497-1497 verbatim
def tx_extract_data_section : Nat := 0x8001ab80

-- @@ L1498-1498 verbatim
def tx_extract_gas_pricing : Nat := 0x80026eec

-- @@ L1499-1499 verbatim
def tx_extract_nonce_and_gas : Nat := 0x80026cd4

-- @@ L1500-1500 verbatim
def tx_extract_to_address : Nat := 0x8001a6b0

-- @@ L1501-1501 verbatim
def tx_extract_value : Nat := 0x8001a908

-- @@ L1502-1502 verbatim
def tx_gas_result_increments : Nat := 0x80028810

-- @@ L1503-1503 verbatim
def tx_gas_sender_bal_lookup : Nat := 0x8001b814

-- @@ L1504-1504 verbatim
def tx_intrinsic_state_gas : Nat := 0x80026af0

-- @@ L1505-1505 verbatim
def tx_legacy_extract_signature : Nat := 0x8002b3dc

-- @@ L1506-1506 verbatim
def tx_pubkey_ecrecover_stage_material : Nat := 0x8002c404

-- @@ L1507-1507 verbatim
def tx_pubkey_public_key_matches : Nat := 0x8002c560

-- @@ L1508-1508 verbatim
def tx_pubkey_recover_raw : Nat := 0x8002c4b4

-- @@ L1509-1509 verbatim
def tx_pubkey_signature_material : Nat := 0x8002c030

-- @@ L1510-1510 verbatim
def tx_signing_hash : Nat := 0x8002bcdc

-- @@ L1511-1511 verbatim
def tx_signing_hash_legacy_eip155 : Nat := 0x8002be50

-- @@ L1512-1512 verbatim
def tx_storage_reads_count : Nat := 0xb9deba58

-- @@ L1513-1513 verbatim
def tx_storage_reads_overflow : Nat := 0xb9deba60

-- @@ L1514-1514 verbatim
def tx_storage_writes_count : Nat := 0xb9deba78

-- @@ L1515-1515 verbatim
def tx_storage_writes_overflow : Nat := 0xb9deba80

-- @@ L1516-1516 verbatim
def tx_type_dispatch : Nat := 0x80019eb8

-- @@ L1517-1517 verbatim
def tx_upfront_precharge : Nat := 0x80027340

-- @@ L1518-1518 verbatim
def txal_decode : Nat := 0xb9e02ec0

-- @@ L1519-1519 verbatim
def txal_inner_off : Nat := 0xb9e02e78

-- @@ L1520-1520 verbatim
def txal_type : Nat := 0xb9e02e70

-- @@ L1521-1521 verbatim
def txup_effective_gas_price : Nat := 0xaa843c00

-- @@ L1522-1522 verbatim
def txup_gas_limit : Nat := 0xaa843be8

-- @@ L1523-1523 verbatim
def txup_nonce : Nat := 0xaa843be0

-- @@ L1524-1524 verbatim
def txup_priority_fee : Nat := 0xaa843c20

-- @@ L1525-1525 verbatim
def u256_add_be : Nat := 0x800059a4

-- @@ L1526-1526 verbatim
def u256_div_u64_be : Nat := 0x80005904

-- @@ L1527-1527 verbatim
def u256_eq : Nat := 0x80005a2c

-- @@ L1528-1528 verbatim
def u256_from_u64_be : Nat := 0x80005758

-- @@ L1529-1529 verbatim
def u256_is_zero : Nat := 0x80005980

-- @@ L1530-1530 verbatim
def u256_lt_be : Nat := 0x80005a64

-- @@ L1531-1531 verbatim
def u256_min : Nat := 0x800270e0

-- @@ L1532-1532 verbatim
def u256_mul_u64_be : Nat := 0x800057a4

-- @@ L1533-1533 verbatim
def u256_sub_be : Nat := 0x800059e8

-- @@ L1534-1534 verbatim
def u256m_acc : Nat := 0xa4386860

-- @@ L1535-1535 verbatim
def validate_header : Nat := 0x8000ba00

-- @@ L1536-1536 verbatim
def validate_header_basic : Nat := 0x8000afd4

-- @@ L1537-1537 verbatim
def validate_header_rlp_pair : Nat := 0x8000c180

-- @@ L1538-1538 verbatim
def validate_parent_hash_link : Nat := 0x80003320

-- @@ L1539-1539 verbatim
def verify_public_keys_match_senders : Nat := 0x8002c620

-- @@ L1540-1540 verbatim
def vh_extracted_parent_hash : Nat := 0xab706960

-- @@ L1541-1541 verbatim
def vh_keccak_table : Nat := 0xab704960

-- @@ L1542-1542 verbatim
def vhrp_parent_struct : Nat := 0xa438a7f0

-- @@ L1543-1543 verbatim
def vhrp_this_struct : Nat := 0xa438a760

-- @@ L1544-1544 verbatim
def vphl_claimed : Nat := 0xa3a0b860

-- @@ L1545-1545 verbatim
def vphl_computed : Nat := 0xa3a0b880

-- @@ L1546-1546 verbatim
def vphl_length : Nat := 0xa3a0b840

-- @@ L1547-1547 verbatim
def vphl_offset : Nat := 0xa3a0b838

-- @@ L1548-1548 verbatim
def vpks_pubkey_out : Nat := 0xa3a4bf48

-- @@ L1549-1549 verbatim
def vpks_scratch : Nat := 0xa3a4bf88

-- @@ L1550-1550 verbatim
def wcidx_build_count : Nat := 0xa34070b8

-- @@ L1551-1551 verbatim
def wcidx_build_section_len : Nat := 0xa34070b0

-- @@ L1552-1552 verbatim
def wcidx_build_status : Nat := 0xa34070a8

-- @@ L1553-1553 verbatim
def wcidx_cmp32 : Nat := 0x80004048

-- @@ L1554-1554 verbatim
def wcidx_count : Nat := 0xa34070a0

-- @@ L1555-1555 verbatim
def wcidx_enabled : Nat := 0xa3407088

-- @@ L1556-1556 verbatim
def wcidx_record_ptr : Nat := 0x8000402c

-- @@ L1557-1557 verbatim
def wcidx_records : Nat := 0xa3407110

-- @@ L1558-1558 verbatim
def wcidx_section_len : Nat := 0xa3407098

-- @@ L1559-1559 verbatim
def wcidx_section_ptr : Nat := 0xa3407090

-- @@ L1560-1560 verbatim
def wcidx_sift_down : Nat := 0x800040b8

-- @@ L1561-1561 verbatim
def wcidx_swap_records : Nat := 0x80004088

-- @@ L1562-1562 verbatim
def wclh_indexed_calls : Nat := 0xa34070c8

-- @@ L1563-1563 verbatim
def wclh_indexed_hits : Nat := 0xa34070d0

-- @@ L1564-1564 verbatim
def wclh_indexed_misses : Nat := 0xa34070d8

-- @@ L1565-1565 verbatim
def wclh_linear_calls : Nat := 0xa34070e0

-- @@ L1566-1566 verbatim
def wclh_linear_hits : Nat := 0xa34070e8

-- @@ L1567-1567 verbatim
def wclh_linear_iterations : Nat := 0xa34070f8

-- @@ L1568-1568 verbatim
def wclh_linear_last_section_len : Nat := 0xa3407100

-- @@ L1569-1569 verbatim
def wclh_linear_max_section_len : Nat := 0xa3407108

-- @@ L1570-1570 verbatim
def wclh_linear_misses : Nat := 0xa34070f0

-- @@ L1571-1571 verbatim
def wclh_lookup_calls : Nat := 0xa34070c0

-- @@ L1572-1572 verbatim
def wclh_scratch_hash : Nat := 0xaa845440

-- @@ L1573-1573 verbatim
def wd_length : Nat := 0xa4386858

-- @@ L1574-1574 verbatim
def wd_offset : Nat := 0xa4386850

-- @@ L1575-1575 verbatim
def widx_build_count : Nat := 0xa2e07030

-- @@ L1576-1576 verbatim
def widx_build_section_len : Nat := 0xa2e07028

-- @@ L1577-1577 verbatim
def widx_build_status : Nat := 0xa2e07020

-- @@ L1578-1578 verbatim
def widx_cmp32 : Nat := 0x80003914

-- @@ L1579-1579 verbatim
def widx_count : Nat := 0xa2e07018

-- @@ L1580-1580 verbatim
def widx_enabled : Nat := 0xa2e07000

-- @@ L1581-1581 verbatim
def widx_record_ptr : Nat := 0x800038f8

-- @@ L1582-1582 verbatim
def widx_records : Nat := 0xa2e07088

-- @@ L1583-1583 verbatim
def widx_section_len : Nat := 0xa2e07010

-- @@ L1584-1584 verbatim
def widx_section_ptr : Nat := 0xa2e07008

-- @@ L1585-1585 verbatim
def widx_sift_down : Nat := 0x80003984

-- @@ L1586-1586 verbatim
def widx_swap_records : Nat := 0x80003954

-- @@ L1587-1587 verbatim
def withdrawal_decode : Nat := 0x80005ab0

-- @@ L1588-1588 verbatim
def withdrawal_request_predeploy_addr : Nat := 0xa0b00d88

-- @@ L1589-1589 verbatim
def withdrawal_to_path_delta : Nat := 0x80005ba0

-- @@ L1590-1590 verbatim
def withdrawals_state_root : Nat := 0x80009804

-- @@ L1591-1591 verbatim
def witness_codes_index_build : Nat := 0x800041b4

-- @@ L1592-1592 verbatim
def witness_codes_lookup_by_hash : Nat := 0x80003dc0

-- @@ L1593-1593 verbatim
def witness_codes_lookup_by_hash_indexed : Nat := 0x8000442c

-- @@ L1594-1594 verbatim
def witness_index_build : Nat := 0x80003a80

-- @@ L1595-1595 verbatim
def witness_lookup_by_hash : Nat := 0x8000368c

-- @@ L1596-1596 verbatim
def witness_lookup_by_hash_indexed : Nat := 0x80003cf8

-- @@ L1597-1597 verbatim
def wlh_indexed_calls : Nat := 0xa2e07040

-- @@ L1598-1598 verbatim
def wlh_indexed_hits : Nat := 0xa2e07048

-- @@ L1599-1599 verbatim
def wlh_indexed_misses : Nat := 0xa2e07050

-- @@ L1600-1600 verbatim
def wlh_linear_calls : Nat := 0xa2e07058

-- @@ L1601-1601 verbatim
def wlh_linear_hits : Nat := 0xa2e07060

-- @@ L1602-1602 verbatim
def wlh_linear_iterations : Nat := 0xa2e07070

-- @@ L1603-1603 verbatim
def wlh_linear_last_section_len : Nat := 0xa2e07078

-- @@ L1604-1604 verbatim
def wlh_linear_max_section_len : Nat := 0xa2e07080

-- @@ L1605-1605 verbatim
def wlh_linear_misses : Nat := 0xa2e07068

-- @@ L1606-1606 verbatim
def wlh_lookup_calls : Nat := 0xa2e07038

-- @@ L1607-1607 verbatim
def wlh_scratch_hash : Nat := 0xa3a4c1c0

-- @@ L1608-1608 verbatim
def write_sets_discard_tx : Nat := 0x80021074

-- @@ L1609-1609 verbatim
def write_sets_incorporate_tx : Nat := 0x80020fb4

-- @@ L1610-1610 verbatim
def write_sets_restore_frame : Nat := 0x80021198

-- @@ L1611-1611 verbatim
def ws_acct : Nat := 0xa43869a0

-- @@ L1612-1612 verbatim
def ws_acct_len : Nat := 0xa4386960

-- @@ L1613-1613 verbatim
def ws_changes : Nat := 0xa4387ea0

-- @@ L1614-1614 verbatim
def ws_delta : Nat := 0xa4386980

-- @@ L1615-1615 verbatim
def ws_newacct : Nat := 0xa43886a0

-- @@ L1616-1616 verbatim
def ws_newacct_len : Nat := 0xa4386968

-- @@ L1617-1617 verbatim
def ws_path : Nat := 0xa4386ea0

-- @@ L1618-1618 verbatim
def wtpd_hash : Nat := 0xa43868c0

-- @@ L1619-1619 verbatim
def wtpd_struct : Nat := 0xa4386888

-- @@ L1620-1620 verbatim
def zk3_state : Nat := 0xa3a4c0e0

-- @@ L1621-1621 verbatim
def zkvm_keccak256 : Nat := 0x80003460

-- @@ L1622-1622 verbatim
def zkvm_keccak256_segments : Nat := 0x80003574

-- @@ L1623-1623 verbatim
def zkvm_sha256 : Nat := 0x800018c0


-- @@ L1625-1625 verbatim
end EvmAsm.Codegen.GuestAddrs
