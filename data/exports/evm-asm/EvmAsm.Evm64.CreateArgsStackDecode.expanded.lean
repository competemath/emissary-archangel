/-
  EvmAsm.Evm64.CreateArgsStackDecode

  Pure top-of-stack decoders for CREATE and CREATE2 arguments (GH #115).
-/

module

public import EvmAsm.Evm64.CreateArgs


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
namespace EvmAsm.Evm64


-- @@ L15-15 verbatim
namespace CreateArgsStackDecode


-- @@ L17-17 verbatim
open CreateArgs


-- @@ L19-22 verbatim
inductive Decoded where
  | create (args : Create)
  | create2 (args : Create2)
  deriving Repr


-- @@ L24-25 verbatim
def mkCreate (value offset size : EvmWord) : Create :=
  { value := value, initcode := { offset := offset, size := size } }


-- @@ L27-28 verbatim
def mkCreate2 (value offset size salt : EvmWord) : Create2 :=
  { value := value, initcode := { offset := offset, size := size }, salt := salt }


-- @@ L30-32 verbatim
def decodedKind : Decoded → Kind
  | .create _ => .create
  | .create2 _ => .create2


-- @@ L34-36 verbatim
def decodedInitcode : Decoded → InitcodeRange
  | .create args => args.initcode
  | .create2 args => args.initcode


-- @@ L38-40 verbatim
def decodedValue : Decoded → EvmWord
  | .create args => args.value
  | .create2 args => args.value


-- @@ L42-44 verbatim
def decodedSalt? : Decoded → Option EvmWord
  | .create _ => none
  | .create2 args => some args.salt


-- @@ L46-47 verbatim
def decodedUsesSalt (decoded : Decoded) : Bool :=
  usesSalt (decodedKind decoded)


-- @@ L49-50 verbatim
def decodedArgumentCount (decoded : Decoded) : Nat :=
  argumentCount (decodedKind decoded)


-- @@ L52-53 verbatim
def decodedResultCount (decoded : Decoded) : Nat :=
  resultCount (decodedKind decoded)


-- @@ L55-56 verbatim
def decodedInitcodeRangeCount (decoded : Decoded) : Nat :=
  initcodeRangeCount (decodedKind decoded)


-- @@ L58-69 verbatim
/--
Decode CREATE-family stack arguments from the top-of-stack list order:
`value, offset, size` for CREATE and `value, offset, size, salt` for CREATE2.

Distinctive token: CreateArgsStackDecode.decodeCreateStack? #115.
-/
def decodeCreateStack? : Kind → List EvmWord → Option Decoded
  | .create, value :: offset :: size :: _ =>
      some (.create (mkCreate value offset size))
  | .create2, value :: offset :: size :: salt :: _ =>
      some (.create2 (mkCreate2 value offset size salt))
  | _, _ => none


-- @@ L71-74 verbatim
theorem decodeCreateStack?_create
    (value offset size : EvmWord) (rest : List EvmWord) :
    decodeCreateStack? .create (value :: offset :: size :: rest) =
      some (.create (mkCreate value offset size)) := rfl


-- @@ L76-79 verbatim
theorem decodeCreateStack?_create2
    (value offset size salt : EvmWord) (rest : List EvmWord) :
    decodeCreateStack? .create2 (value :: offset :: size :: salt :: rest) =
      some (.create2 (mkCreate2 value offset size salt)) := rfl


-- @@ L81-94 verbatim
theorem decodeCreateStack?_create_eq_some_iff
    (stack : List EvmWord) (decoded : Decoded) :
    decodeCreateStack? .create stack = some decoded ↔
      ∃ value offset size rest,
        stack = value :: offset :: size :: rest ∧
          decoded = .create (mkCreate value offset size) := by
  constructor
  · intro h_decode
    rcases stack with _ | ⟨value, _ | ⟨offset, _ | ⟨size, rest⟩⟩⟩ <;>
      simp [decodeCreateStack?] at h_decode
    cases h_decode
    exact ⟨value, offset, size, rest, rfl, rfl⟩
  · rintro ⟨value, offset, size, rest, rfl, rfl⟩
    rfl


-- @@ L96-109 verbatim
theorem decodeCreateStack?_create2_eq_some_iff
    (stack : List EvmWord) (decoded : Decoded) :
    decodeCreateStack? .create2 stack = some decoded ↔
      ∃ value offset size salt rest,
        stack = value :: offset :: size :: salt :: rest ∧
          decoded = .create2 (mkCreate2 value offset size salt) := by
  constructor
  · intro h_decode
    rcases stack with _ | ⟨value, _ | ⟨offset, _ | ⟨size, _ | ⟨salt, rest⟩⟩⟩⟩ <;>
      simp [decodeCreateStack?] at h_decode
    cases h_decode
    exact ⟨value, offset, size, salt, rest, rfl, rfl⟩
  · rintro ⟨value, offset, size, salt, rest, rfl, rfl⟩
    rfl


-- @@ L111-125 verbatim
theorem decodeCreateStack?_eq_some_iff
    (kind : Kind) (stack : List EvmWord) (decoded : Decoded) :
    decodeCreateStack? kind stack = some decoded ↔
      match kind with
      | .create =>
          ∃ value offset size rest,
            stack = value :: offset :: size :: rest ∧
              decoded = .create (mkCreate value offset size)
      | .create2 =>
          ∃ value offset size salt rest,
            stack = value :: offset :: size :: salt :: rest ∧
              decoded = .create2 (mkCreate2 value offset size salt) := by
  cases kind with
  | create => exact decodeCreateStack?_create_eq_some_iff stack decoded
  | create2 => exact decodeCreateStack?_create2_eq_some_iff stack decoded


-- @@ L127-134 verbatim
theorem decodeCreateStack?_create_kind_of_some
    {stack : List EvmWord} {decoded : Decoded}
    (h_decode : decodeCreateStack? .create stack = some decoded) :
    decodedKind decoded = .create := by
  rw [decodeCreateStack?_create_eq_some_iff] at h_decode
  rcases h_decode with ⟨value, offset, size, rest, h_stack, h_decoded⟩
  subst h_decoded
  rfl


-- @@ L136-143 verbatim
theorem decodeCreateStack?_create2_kind_of_some
    {stack : List EvmWord} {decoded : Decoded}
    (h_decode : decodeCreateStack? .create2 stack = some decoded) :
    decodedKind decoded = .create2 := by
  rw [decodeCreateStack?_create2_eq_some_iff] at h_decode
  rcases h_decode with ⟨value, offset, size, salt, rest, h_stack, h_decoded⟩
  subst h_decoded
  rfl


-- @@ L145-151 verbatim
theorem decodeCreateStack?_kind_of_some
    {kind : Kind} {stack : List EvmWord} {decoded : Decoded}
    (h_decode : decodeCreateStack? kind stack = some decoded) :
    decodedKind decoded = kind := by
  cases kind with
  | create => exact decodeCreateStack?_create_kind_of_some h_decode
  | create2 => exact decodeCreateStack?_create2_kind_of_some h_decode


-- @@ L153-157 verbatim
theorem decodeCreateStack?_usesSalt_of_some
    {kind : Kind} {stack : List EvmWord} {decoded : Decoded}
    (h_decode : decodeCreateStack? kind stack = some decoded) :
    decodedUsesSalt decoded = usesSalt kind := by
  rw [decodedUsesSalt, decodeCreateStack?_kind_of_some h_decode]


-- @@ L159-163 verbatim
theorem decodeCreateStack?_argumentCount_of_some
    {kind : Kind} {stack : List EvmWord} {decoded : Decoded}
    (h_decode : decodeCreateStack? kind stack = some decoded) :
    decodedArgumentCount decoded = argumentCount kind := by
  rw [decodedArgumentCount, decodeCreateStack?_kind_of_some h_decode]


-- @@ L165-169 verbatim
theorem decodeCreateStack?_resultCount_of_some
    {kind : Kind} {stack : List EvmWord} {decoded : Decoded}
    (h_decode : decodeCreateStack? kind stack = some decoded) :
    decodedResultCount decoded = resultCount kind := by
  rw [decodedResultCount, decodeCreateStack?_kind_of_some h_decode]


-- @@ L171-175 verbatim
theorem decodeCreateStack?_initcodeRangeCount_of_some
    {kind : Kind} {stack : List EvmWord} {decoded : Decoded}
    (h_decode : decodeCreateStack? kind stack = some decoded) :
    decodedInitcodeRangeCount decoded = initcodeRangeCount kind := by
  rw [decodedInitcodeRangeCount, decodeCreateStack?_kind_of_some h_decode]


-- @@ L177-192 verbatim
theorem decodeCreateStack?_create_eq_none_iff (stack : List EvmWord) :
    decodeCreateStack? .create stack = none ↔ stack.length < argumentCount .create := by
  constructor
  · intro h_decode
    rcases stack with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩
    · simp [argumentCount]
    · simp [argumentCount]
    · simp [argumentCount]
    · simp [decodeCreateStack?] at h_decode
  · intro h_len
    rcases stack with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩
    · rfl
    · rfl
    · rfl
    · simp [argumentCount] at h_len
      omega


-- @@ L194-211 verbatim
theorem decodeCreateStack?_create2_eq_none_iff (stack : List EvmWord) :
    decodeCreateStack? .create2 stack = none ↔ stack.length < argumentCount .create2 := by
  constructor
  · intro h_decode
    rcases stack with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩
    · simp [argumentCount]
    · simp [argumentCount]
    · simp [argumentCount]
    · simp [argumentCount]
    · simp [decodeCreateStack?] at h_decode
  · intro h_len
    rcases stack with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩
    · rfl
    · rfl
    · rfl
    · rfl
    · simp [argumentCount] at h_len
      omega


-- @@ L213-217 verbatim
theorem decodeCreateStack?_eq_none_iff (kind : Kind) (stack : List EvmWord) :
    decodeCreateStack? kind stack = none ↔ stack.length < argumentCount kind := by
  cases kind with
  | create => exact decodeCreateStack?_create_eq_none_iff stack
  | create2 => exact decodeCreateStack?_create2_eq_none_iff stack


-- @@ L219-220 verbatim
theorem decodeCreateStack?_create_none_of_empty :
    decodeCreateStack? .create [] = none := rfl


-- @@ L222-224 verbatim
theorem decodeCreateStack?_create_none_of_one
    (value : EvmWord) :
    decodeCreateStack? .create [value] = none := rfl


-- @@ L226-228 verbatim
theorem decodeCreateStack?_create_none_of_two
    (value offset : EvmWord) :
    decodeCreateStack? .create [value, offset] = none := rfl


-- @@ L230-231 verbatim
theorem decodeCreateStack?_create2_none_of_empty :
    decodeCreateStack? .create2 [] = none := rfl


-- @@ L233-235 verbatim
theorem decodeCreateStack?_create2_none_of_one
    (value : EvmWord) :
    decodeCreateStack? .create2 [value] = none := rfl


-- @@ L237-239 verbatim
theorem decodeCreateStack?_create2_none_of_two
    (value offset : EvmWord) :
    decodeCreateStack? .create2 [value, offset] = none := rfl


-- @@ L241-243 verbatim
theorem decodeCreateStack?_create2_none_of_three
    (value offset size : EvmWord) :
    decodeCreateStack? .create2 [value, offset, size] = none := rfl


-- @@ L245-246 verbatim
theorem decodedKind_create (value offset size : EvmWord) :
    decodedKind (.create (mkCreate value offset size)) = .create := rfl


-- @@ L248-249 verbatim
theorem decodedKind_create2 (value offset size salt : EvmWord) :
    decodedKind (.create2 (mkCreate2 value offset size salt)) = .create2 := rfl


-- @@ L251-253 verbatim
theorem decodedInitcode_create (value offset size : EvmWord) :
    decodedInitcode (.create (mkCreate value offset size)) =
      { offset := offset, size := size } := rfl


-- @@ L255-257 verbatim
theorem decodedInitcode_create2 (value offset size salt : EvmWord) :
    decodedInitcode (.create2 (mkCreate2 value offset size salt)) =
      { offset := offset, size := size } := rfl


-- @@ L259-260 verbatim
theorem decodedValue_create (value offset size : EvmWord) :
    decodedValue (.create (mkCreate value offset size)) = value := rfl


-- @@ L262-263 verbatim
theorem decodedValue_create2 (value offset size salt : EvmWord) :
    decodedValue (.create2 (mkCreate2 value offset size salt)) = value := rfl


-- @@ L265-266 verbatim
theorem decodedSalt?_create (value offset size : EvmWord) :
    decodedSalt? (.create (mkCreate value offset size)) = none := rfl


-- @@ L268-269 verbatim
theorem decodedSalt?_create2 (value offset size salt : EvmWord) :
    decodedSalt? (.create2 (mkCreate2 value offset size salt)) = some salt := rfl


-- @@ L271-272 verbatim
theorem decodedUsesSalt_create (value offset size : EvmWord) :
    decodedUsesSalt (.create (mkCreate value offset size)) = false := rfl


-- @@ L274-275 verbatim
theorem decodedUsesSalt_create2 (value offset size salt : EvmWord) :
    decodedUsesSalt (.create2 (mkCreate2 value offset size salt)) = true := rfl


-- @@ L277-278 verbatim
theorem decodedArgumentCount_create (value offset size : EvmWord) :
    decodedArgumentCount (.create (mkCreate value offset size)) = 3 := rfl


-- @@ L280-281 verbatim
theorem decodedArgumentCount_create2 (value offset size salt : EvmWord) :
    decodedArgumentCount (.create2 (mkCreate2 value offset size salt)) = 4 := rfl


-- @@ L283-284 verbatim
theorem decodedResultCount_create (value offset size : EvmWord) :
    decodedResultCount (.create (mkCreate value offset size)) = 1 := rfl


-- @@ L286-287 verbatim
theorem decodedResultCount_create2 (value offset size salt : EvmWord) :
    decodedResultCount (.create2 (mkCreate2 value offset size salt)) = 1 := rfl


-- @@ L289-290 verbatim
theorem decodedInitcodeRangeCount_create (value offset size : EvmWord) :
    decodedInitcodeRangeCount (.create (mkCreate value offset size)) = 1 := rfl


-- @@ L292-293 verbatim
theorem decodedInitcodeRangeCount_create2 (value offset size salt : EvmWord) :
    decodedInitcodeRangeCount (.create2 (mkCreate2 value offset size salt)) = 1 := rfl


-- @@ L295-295 verbatim
end CreateArgsStackDecode


-- @@ L297-297 verbatim
end EvmAsm.Evm64
