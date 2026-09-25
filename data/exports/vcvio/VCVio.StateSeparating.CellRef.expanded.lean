/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import ToMathlib.Data.Heap
public import VCVio.EvalDist.Defs.Instances
public import VCVio.OracleComp.ProbComp
public import VCVio.OracleComp.SimSemantics.QueryImpl.Constructions


-- @@ L13-31 verbatim
/-!
# State-separating cell references

`Heap Ident` stores typed cells at stable identifiers. `CellRef Ident` packages
one identifier as a typed reference, so heap programs can say explicitly which
cell they read or write.

The main purpose of this file is frame reasoning. A program that writes only a
known footprint preserves every cell outside that footprint, and the same idea
lifts from deterministic state programs to support-based effectful programs and
to oracle handlers interpreted by `simulateQ`.

The file is organized around four small layers:

* typed references and state operations;
* support-based preservation and write footprints;
* deterministic specializations for `StateT (Heap Ident) Id`;
* handler-level footprints for `QueryImpl`.
-/


-- @@ L33-33 verbatim
@[expose] public section


-- @@ L35-35 verbatim
universe u v uι u₀


-- @@ L37-37 verbatim
namespace VCVio.StateSeparating


-- @@ L39-39 verbatim
variable {Ident : Type u} [CellSpec.{u, max u v} Ident]


-- @@ L41-41 verbatim
/-! ## Cell references -/


-- @@ L43-47 verbatim
/-- A capability naming one typed cell in a `Heap Ident`. The value type of
the reference is dependent: `r.Value = CellSpec.type r.id`. -/
structure CellRef (Ident : Type u) [CellSpec.{u, max u v} Ident] where
  /-- The underlying heap cell identifier. -/
  id : Ident


-- @@ L49-49 verbatim
namespace CellRef


-- @@ L51-52 verbatim
/-- The value type stored at a cell reference. -/
abbrev Value (r : CellRef Ident) : Type (max u v) := CellSpec.type r.id


-- @@ L54-56 verbatim
/-- Read a referenced cell from a heap. -/
@[reducible]
def get (r : CellRef Ident) (h : Heap Ident) : r.Value := h.get r.id


-- @@ L58-60 verbatim
/-- Write a referenced cell in a heap. -/
def set [DecidableEq Ident] (r : CellRef Ident) (h : Heap Ident) (x : r.Value) : Heap Ident :=
  h.update r.id x


-- @@ L62-65 verbatim
@[simp]
theorem get_set_self [DecidableEq Ident] (r : CellRef Ident) (h : Heap Ident) (x : r.Value) :
    r.get (r.set h x) = x :=
  Heap.get_update_self h r.id x


-- @@ L67-71 verbatim
@[simp]
theorem get_set_of_ne [DecidableEq Ident] (r s : CellRef Ident) (h : Heap Ident) (x : r.Value)
    (hne : s.id ≠ r.id) :
    s.get (r.set h x) = s.get h :=
  Heap.get_update_of_ne hne x


-- @@ L73-73 verbatim
/-! ## Deterministic state operations -/


-- @@ L75-77 verbatim
/-- Deterministically read a referenced cell. -/
def read (r : CellRef Ident) : StateT (Heap Ident) Id r.Value :=
  StateT.mk fun h => (r.get h, h)


-- @@ L79-82 verbatim
/-- Deterministically write a referenced cell. -/
def write [DecidableEq Ident] (r : CellRef Ident) (x : r.Value) :
    StateT (Heap Ident) Id PUnit :=
  StateT.mk fun h => (PUnit.unit, r.set h x)


-- @@ L84-87 verbatim
@[simp]
theorem read_run (r : CellRef Ident) (h : Heap Ident) :
    r.read.run h = (r.get h, h) :=
  rfl


-- @@ L89-92 verbatim
@[simp]
theorem write_run [DecidableEq Ident] (r : CellRef Ident) (h : Heap Ident) (x : r.Value) :
    (r.write x).run h = (PUnit.unit, r.set h x) :=
  rfl


-- @@ L94-94 verbatim
/-! ## Effectful state operations -/


-- @@ L96-100 verbatim
/-- Effectfully read a referenced cell. This is the monadic version of
`CellRef.read`: it works in any ambient monad, not just `Id`. -/
def readM (r : CellRef Ident) {m : Type (max u v) → Type*} [Monad m] :
    StateT (Heap Ident) m r.Value :=
  StateT.mk fun h => pure (r.get h, h)


-- @@ L102-108 verbatim
/-- Effectfully write a referenced cell. This is the monadic version of
`CellRef.write`: it updates only the selected heap cell and performs no other
ambient effects. -/
def writeM [DecidableEq Ident] (r : CellRef Ident) (x : r.Value)
    {m : Type (max u v) → Type*} [Monad m] :
    StateT (Heap Ident) m PUnit :=
  StateT.mk fun h => pure (PUnit.unit, r.set h x)


-- @@ L110-114 verbatim
@[simp]
theorem readM_run (r : CellRef Ident) {m : Type (max u v) → Type*} [Monad m]
    (h : Heap Ident) :
    (r.readM : StateT (Heap Ident) m r.Value).run h = pure (r.get h, h) :=
  rfl


-- @@ L116-121 verbatim
@[simp]
theorem writeM_run [DecidableEq Ident] (r : CellRef Ident) (x : r.Value)
    {m : Type (max u v) → Type*} [Monad m] (h : Heap Ident) :
    (r.writeM x : StateT (Heap Ident) m PUnit).run h =
      pure (PUnit.unit, r.set h x) :=
  rfl


-- @@ L123-123 verbatim
/-! ## Support-based frame predicates -/


-- @@ L125-132 verbatim
/-- An effectful heap program preserves a cell reference when every
support-reachable final heap has the same value at that reference as the
initial heap. This is the right generalization of `Preserves` beyond `Id`:
for probabilistic/oracle computations there may be many possible final states. -/
def SupportPreserves {m : Type (max u v) → Type*} [Monad m] [MonadLiftT m SetM]
    [LawfulMonadLiftT m SetM]
    {α : Type (max u v)} (c : StateT (Heap Ident) m α) (r : CellRef Ident) : Prop :=
  ∀ h z, z ∈ support (c.run h) → r.get z.2 = r.get h


-- @@ L134-139 verbatim
/-- An effectful heap program writes only a set of identifiers when every cell
outside the set is support-preserved. -/
def SupportWritesOnly {m : Type (max u v) → Type*} [Monad m] [MonadLiftT m SetM]
    [LawfulMonadLiftT m SetM]
    {α : Type (max u v)} (c : StateT (Heap Ident) m α) (writes : Set Ident) : Prop :=
  ∀ r : CellRef Ident, r.id ∉ writes → SupportPreserves c r


-- @@ L141-146 verbatim
theorem supportWritesOnly_mono {m : Type (max u v) → Type*} [Monad m] [MonadLiftT m SetM]
    [LawfulMonadLiftT m SetM]
    {α : Type (max u v)} {c : StateT (Heap Ident) m α} {writes₁ writes₂ : Set Ident}
    (hc : SupportWritesOnly c writes₁) (hsubset : writes₁ ⊆ writes₂) :
    SupportWritesOnly c writes₂ :=
  fun r hr => hc r (fun hmem => hr (hsubset hmem))


-- @@ L148-154 verbatim
theorem supportPreserves_pure {m : Type (max u v) → Type*} [Monad m] [MonadLiftT m SetM]
    [LawfulMonadLiftT m SetM]
    {α : Type (max u v)} (x : α) (r : CellRef Ident) :
    SupportPreserves (pure x : StateT (Heap Ident) m α) r := by
  intro h z hz
  obtain rfl := (mem_support_pure_iff z (x, h)).1 hz
  simp


-- @@ L156-160 verbatim
theorem supportWritesOnly_pure_empty {m : Type (max u v) → Type*} [Monad m] [MonadLiftT m SetM]
    [LawfulMonadLiftT m SetM]
    {α : Type (max u v)} (x : α) :
    SupportWritesOnly (pure x : StateT (Heap Ident) m α) (∅ : Set Ident) :=
  fun r _ => supportPreserves_pure x r


-- @@ L162-168 verbatim
theorem supportPreserves_readM {m : Type (max u v) → Type*} [Monad m] [MonadLiftT m SetM]
    [LawfulMonadLiftT m SetM]
    (r s : CellRef Ident) :
    SupportPreserves (r.readM : StateT (Heap Ident) m r.Value) s := by
  intro h z hz
  obtain rfl := (mem_support_pure_iff z (r.get h, h)).1 hz
  simp


-- @@ L170-174 verbatim
theorem readM_supportWritesOnly_empty {m : Type (max u v) → Type*} [Monad m] [MonadLiftT m SetM]
    [LawfulMonadLiftT m SetM]
    (r : CellRef Ident) :
    SupportWritesOnly (r.readM : StateT (Heap Ident) m r.Value) (∅ : Set Ident) :=
  fun s _ => supportPreserves_readM r s


-- @@ L176-185 verbatim
theorem supportPreserves_bind {m : Type (max u v) → Type*} [Monad m] [MonadLiftT m SetM]
    [LawfulMonadLiftT m SetM]
    {α β : Type (max u v)} {c : StateT (Heap Ident) m α}
    {k : α → StateT (Heap Ident) m β} {r : CellRef Ident}
    (hc : SupportPreserves c r) (hk : ∀ a, SupportPreserves (k a) r) :
    SupportPreserves (c >>= k) r := by
  intro h z hz
  rw [StateT.run_bind] at hz
  rcases (mem_support_bind_iff _ _ _).1 hz with ⟨us, hus, hzcont⟩
  exact (hk us.1 us.2 z hzcont).trans (hc h us hus)


-- @@ L187-194 verbatim
theorem writeM_supportWritesOnly_single [DecidableEq Ident]
    {m : Type (max u v) → Type*} [Monad m] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    (r : CellRef Ident) (x : r.Value) :
    SupportWritesOnly
      (r.writeM x : StateT (Heap Ident) m PUnit) ({r.id} : Set Ident) := by
  intro s hs h z hz
  obtain rfl := (mem_support_pure_iff z (PUnit.unit, r.set h x)).1 hz
  simpa using get_set_of_ne r s h x hs


-- @@ L196-203 verbatim
theorem supportWritesOnly_bind {m : Type (max u v) → Type*} [Monad m] [MonadLiftT m SetM]
    [LawfulMonadLiftT m SetM]
    {α β : Type (max u v)} {c : StateT (Heap Ident) m α}
    {k : α → StateT (Heap Ident) m β} {writes₁ writes₂ : Set Ident}
    (hc : SupportWritesOnly c writes₁) (hk : ∀ a, SupportWritesOnly (k a) writes₂) :
    SupportWritesOnly (c >>= k) (writes₁ ∪ writes₂) :=
  fun r hr => supportPreserves_bind (hc r (fun hmem => hr (Or.inl hmem)))
    (fun a => hk a r (fun hmem => hr (Or.inr hmem)))


-- @@ L205-215 verbatim
/-- Dependent effectful bind form: the continuation's write set may depend on
the first result. -/
theorem supportWritesOnly_bind_dep {m : Type (max u v) → Type*} [Monad m] [MonadLiftT m SetM]
    [LawfulMonadLiftT m SetM]
    {α β : Type (max u v)} {c : StateT (Heap Ident) m α}
    {k : α → StateT (Heap Ident) m β} {writes₁ : Set Ident}
    {writes₂ : α → Set Ident}
    (hc : SupportWritesOnly c writes₁) (hk : ∀ a, SupportWritesOnly (k a) (writes₂ a)) :
    SupportWritesOnly (c >>= k) (writes₁ ∪ {i | ∃ a, i ∈ writes₂ a}) :=
  fun r hr => supportPreserves_bind (hc r (fun hmem => hr (Or.inl hmem)))
    (fun a => hk a r (fun hmem => hr (Or.inr ⟨a, hmem⟩)))


-- @@ L217-225 verbatim
/-- A support-based write footprint packages a program with the set of cells it
may write and the proof that every other cell is preserved. -/
structure SupportWriteFootprint {m : Type (max u v)
    → Type*} [Monad m] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    {α : Type (max u v)} (c : StateT (Heap Ident) m α) where
  /-- Cells that the effectful program may write. -/
  writes : Set Ident
  /-- Soundness: every cell outside `writes` is support-framed through. -/
  sound : SupportWritesOnly c writes


-- @@ L227-227 verbatim
namespace SupportWriteFootprint


-- @@ L229-229 verbatim
variable {m : Type (max u v) → Type*} [Monad m] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]

-- @@ L230-230 verbatim
variable {α β : Type (max u v)}


-- @@ L232-235 verbatim
theorem preserves {c : StateT (Heap Ident) m α} (footprint : SupportWriteFootprint c)
    (r : CellRef Ident) (hr : r.id ∉ footprint.writes) :
    SupportPreserves c r :=
  footprint.sound r hr


-- @@ L237-239 verbatim
def pure (x : α) : SupportWriteFootprint (pure x : StateT (Heap Ident) m α) where
  writes := ∅
  sound := supportWritesOnly_pure_empty x


-- @@ L241-244 verbatim
def readM (r : CellRef Ident) :
    SupportWriteFootprint (r.readM : StateT (Heap Ident) m r.Value) where
  writes := ∅
  sound := readM_supportWritesOnly_empty r


-- @@ L246-249 verbatim
def writeM [DecidableEq Ident] (r : CellRef Ident) (x : r.Value) :
    SupportWriteFootprint (r.writeM x : StateT (Heap Ident) m PUnit) where
  writes := {r.id}
  sound := writeM_supportWritesOnly_single r x


-- @@ L251-255 verbatim
def bind {c : StateT (Heap Ident) m α} {k : α → StateT (Heap Ident) m β}
    (footprint : SupportWriteFootprint c) (kont : ∀ a, SupportWriteFootprint (k a)) :
    SupportWriteFootprint (c >>= k) where
  writes := footprint.writes ∪ {i | ∃ a, i ∈ (kont a).writes}
  sound := supportWritesOnly_bind_dep footprint.sound (fun a => (kont a).sound)


-- @@ L257-257 verbatim
end SupportWriteFootprint


-- @@ L259-259 verbatim
/-! ## Probability corollaries for cell frames -/


-- @@ L261-261 verbatim
namespace SupportPreserves


-- @@ L263-264 verbatim
variable {m : Type (max u v) → Type*} [Monad m] [MonadLiftT m SPMF]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]

-- @@ L265-265 verbatim
variable {α : Type (max u v)} {c : StateT (Heap Ident) m α} {r : CellRef Ident}


-- @@ L267-272 expanded
/-- A support-level frame implies that the cell-change event has probability
zero. This is the probability-facing corollary most proofs want after a
generic frame theorem has done the support-level work. -/
theorem prob_changed_eq_zero (hc : SupportPreserves c r) (h : Heap Ident) :
    (probEvent (c.run h) fun z => r.get z.2 ≠ r.get h) = 0 :=
  probEvent_eq_zero_iff.2 fun z hz hchange => hchange (hc h z hz)


-- @@ L274-279 expanded
/-- If a cell is support-preserved, then the probability of reading the
initial value at the end is exactly one minus the failure probability. -/
theorem prob_unchanged_eq_sub_probFailure (hc : SupportPreserves c r) (h : Heap Ident) :
    (probEvent (c.run h) fun z => r.get z.2 = r.get h) = 1 - probFailure (c.run h) := by
  rw [probEvent_ext (q := fun _ => True) fun z hz => ⟨fun _ => True.intro, fun _ => hc h z hz⟩,
    probEvent_True_eq_sub]


-- @@ L281-285 expanded
/-- Failure-free specialization of `prob_unchanged_eq_sub_probFailure`. -/
theorem prob_unchanged_eq_one_of_probFailure_eq_zero (hc : SupportPreserves c r) (h : Heap Ident)
    (hnf : probFailure (c.run h) = 0) : (probEvent (c.run h) fun z => r.get z.2 = r.get h) = 1 := by
  simp [prob_unchanged_eq_sub_probFailure hc h, hnf]


-- @@ L287-295 expanded
/-- If the ambient monad has total probability semantics, support preservation
gives probability-one preservation directly. -/
theorem prob_unchanged_eq_one {m : Type (max u v) → Type*} [Monad m] [MonadLiftT m PMF]
    [LawfulMonadLiftT m PMF] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]
    {α : Type (max u v)} {c : StateT (Heap Ident) m α} {r : CellRef Ident}
    (hc : SupportPreserves c r) (h : Heap Ident) :
    (probEvent (c.run h) fun z => r.get z.2 = r.get h) = 1 :=
  prob_unchanged_eq_one_of_probFailure_eq_zero hc h (probFailure_of_liftM_PMF (c.run h))


-- @@ L297-302 expanded
/-- If the initial cell value is not `x`, then a support-preserved cell has
final value `x` with probability zero. -/
theorem prob_final_eq_eq_zero_of_ne (hc : SupportPreserves c r) (h : Heap Ident) {x : r.Value}
    (hne : x ≠ r.get h) : (probEvent (c.run h) fun z => r.get z.2 = x) = 0 :=
  probEvent_eq_zero_iff.2 fun z hz hzval => hne (hzval.symm.trans (hc h z hz))


-- @@ L304-304 verbatim
end SupportPreserves


-- @@ L306-306 verbatim
namespace SupportWritesOnly


-- @@ L308-309 verbatim
variable {m : Type (max u v) → Type*} [Monad m] [MonadLiftT m SPMF]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]

-- @@ L310-310 verbatim
variable {α : Type (max u v)} {c : StateT (Heap Ident) m α} {writes : Set Ident}


-- @@ L312-315 expanded
theorem prob_changed_eq_zero (hc : SupportWritesOnly c writes) (r : CellRef Ident)
    (hr : r.id ∉ writes) (h : Heap Ident) :
    (probEvent (c.run h) fun z => r.get z.2 ≠ r.get h) = 0 :=
  SupportPreserves.prob_changed_eq_zero (hc r hr) h


-- @@ L317-320 expanded
theorem prob_unchanged_eq_sub_probFailure (hc : SupportWritesOnly c writes) (r : CellRef Ident)
    (hr : r.id ∉ writes) (h : Heap Ident) :
    (probEvent (c.run h) fun z => r.get z.2 = r.get h) = 1 - probFailure (c.run h) :=
  SupportPreserves.prob_unchanged_eq_sub_probFailure (hc r hr) h


-- @@ L322-326 expanded
theorem prob_final_eq_eq_zero_of_ne (hc : SupportWritesOnly c writes) (r : CellRef Ident)
    (hr : r.id ∉ writes) (h : Heap Ident) {x : r.Value} (hne : x ≠ r.get h) :
    (probEvent (c.run h) fun z => r.get z.2 = x) = 0 :=
  SupportPreserves.prob_final_eq_eq_zero_of_ne (hc r hr) h hne


-- @@ L328-328 verbatim
end SupportWritesOnly


-- @@ L330-330 verbatim
/-! ## Preservation except an event -/


-- @@ L332-339 verbatim
/-- A computation preserves a cell except on an event when every
support-reachable outcome outside that event has the initial cell value. The
event may depend on the initial heap. -/
def SupportPreservesExcept {m : Type (max u v) → Type*} [Monad m] [MonadLiftT m SetM]
    [LawfulMonadLiftT m SetM]
    {α : Type (max u v)} (c : StateT (Heap Ident) m α) (r : CellRef Ident)
    (event : Heap Ident → α × Heap Ident → Prop) : Prop :=
  ∀ h z, z ∈ support (c.run h) → ¬ event h z → r.get z.2 = r.get h


-- @@ L341-341 verbatim
namespace SupportPreservesExcept


-- @@ L343-343 verbatim
section support


-- @@ L345-345 verbatim
variable {m : Type (max u v) → Type*} [Monad m] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]

-- @@ L346-346 verbatim
variable {α : Type (max u v)} {c : StateT (Heap Ident) m α} {r : CellRef Ident}

-- @@ L347-347 verbatim
variable {event : Heap Ident → α × Heap Ident → Prop}


-- @@ L349-351 verbatim
theorem of_supportPreserves (hc : SupportPreserves c r) :
    SupportPreservesExcept c r event :=
  fun h z hz _ => hc h z hz


-- @@ L353-357 verbatim
theorem mono_event (hc : SupportPreservesExcept c r event)
    {event' : Heap Ident → α × Heap Ident → Prop}
    (hsubset : ∀ h z, event h z → event' h z) :
    SupportPreservesExcept c r event' :=
  fun h z hz hnot => hc h z hz fun hevent => hnot (hsubset h z hevent)


-- @@ L359-362 verbatim
theorem supportPreserves_of_false_event
    (hc : SupportPreservesExcept c r (fun _ _ => False)) :
    SupportPreserves c r :=
  fun h z hz => hc h z hz (by simp)


-- @@ L364-364 verbatim
end support


-- @@ L366-366 verbatim
section probability


-- @@ L368-369 verbatim
variable {m : Type (max u v) → Type*} [Monad m] [MonadLiftT m SPMF]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]

-- @@ L370-370 verbatim
variable {α : Type (max u v)} {c : StateT (Heap Ident) m α} {r : CellRef Ident}

-- @@ L371-371 verbatim
variable {event : Heap Ident → α × Heap Ident → Prop}


-- @@ L373-379 expanded
/-- If a cell can change only when `event` occurs, then the change probability
is bounded by the event probability. -/
theorem prob_changed_le_prob_event (hc : SupportPreservesExcept c r event) (h : Heap Ident) :
    (probEvent (c.run h) fun z => r.get z.2 ≠ r.get h) ≤ probEvent (c.run h) fun z => event h z :=
  probEvent_mono fun z hz hchange => not_not.1 fun hevent => hchange (hc h z hz hevent)


-- @@ L381-385 expanded
theorem prob_changed_eq_zero_of_prob_event_eq_zero (hc : SupportPreservesExcept c r event)
    (h : Heap Ident) (hevent : (probEvent (c.run h) fun z => event h z) = 0) :
    (probEvent (c.run h) fun z => r.get z.2 ≠ r.get h) = 0 :=
  le_zero_iff.1 ((prob_changed_le_prob_event hc h).trans hevent.le)


-- @@ L387-391 expanded
theorem prob_changed_le_of_prob_event_le (hc : SupportPreservesExcept c r event) (h : Heap Ident)
    {ε : ENNReal} (hevent : (probEvent (c.run h) fun z => event h z) ≤ ε) :
    (probEvent (c.run h) fun z => r.get z.2 ≠ r.get h) ≤ ε :=
  (prob_changed_le_prob_event hc h).trans hevent


-- @@ L393-393 verbatim
end probability


-- @@ L395-395 verbatim
end SupportPreservesExcept


-- @@ L397-397 verbatim
/-! ## Relational and measured cell effects -/


-- @@ L399-406 verbatim
/-- A support-level relation between the initial and final value of one cell.
This is the general qualitative layer underneath preservation (`rel := Eq`) and
monotonicity/growth assertions. -/
def SupportCellRel {m : Type (max u v) → Type*} [Monad m] [MonadLiftT m SetM]
    [LawfulMonadLiftT m SetM]
    {α : Type (max u v)} (c : StateT (Heap Ident) m α) (r : CellRef Ident)
    (rel : r.Value → r.Value → Prop) : Prop :=
  ∀ h z, z ∈ support (c.run h) → rel (r.get h) (r.get z.2)


-- @@ L408-408 verbatim
namespace SupportCellRel


-- @@ L410-410 verbatim
section support


-- @@ L412-412 verbatim
variable {m : Type (max u v) → Type*} [Monad m] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]

-- @@ L413-413 verbatim
variable {α β : Type (max u v)} {c : StateT (Heap Ident) m α}

-- @@ L414-414 verbatim
variable {k : α → StateT (Heap Ident) m β} {r : CellRef Ident}

-- @@ L415-415 verbatim
variable {rel : r.Value → r.Value → Prop}


-- @@ L417-419 verbatim
theorem of_supportPreserves (hc : SupportPreserves c r) :
    SupportCellRel c r Eq :=
  fun h z hz => (hc h z hz).symm


-- @@ L421-423 verbatim
theorem supportPreserves_of_eq (hc : SupportCellRel c r Eq) :
    SupportPreserves c r :=
  fun h z hz => (hc h z hz).symm


-- @@ L425-433 verbatim
theorem bind (hc : SupportCellRel c r rel)
    (hk : ∀ a, SupportCellRel (k a) r rel)
    (htrans : ∀ x y z, rel x y → rel y z → rel x z) :
    SupportCellRel (c >>= k) r rel := by
  intro h z hz
  rw [StateT.run_bind] at hz
  rcases (mem_support_bind_iff _ _ _).1 hz with ⟨us, hus, hzcont⟩
  exact htrans (r.get h) (r.get us.2) (r.get z.2)
    (hc h us hus) (hk us.1 us.2 z hzcont)


-- @@ L435-435 verbatim
end support


-- @@ L437-437 verbatim
section probability


-- @@ L439-440 verbatim
variable {m : Type (max u v) → Type*} [Monad m] [MonadLiftT m SPMF]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]

-- @@ L441-441 verbatim
variable {α : Type (max u v)} {c : StateT (Heap Ident) m α} {r : CellRef Ident}

-- @@ L442-442 verbatim
variable {rel : r.Value → r.Value → Prop}


-- @@ L444-448 expanded
/-- A support-level cell relation makes violations of the relation a
probability-zero event. -/
theorem prob_violate_eq_zero (hc : SupportCellRel c r rel) (h : Heap Ident) :
    (probEvent (c.run h) fun z => ¬rel (r.get h) (r.get z.2)) = 0 :=
  probEvent_eq_zero_iff.2 fun z hz hviol => hviol (hc h z hz)


-- @@ L450-450 verbatim
end probability


-- @@ L452-452 verbatim
end SupportCellRel


-- @@ L454-461 verbatim
/-- A measured cell bound says a numeric measure of a cell can increase by at
most `δ` on every support-reachable execution path. Binds compose by adding
their deltas. -/
def SupportMeasureBound {m : Type (max u v) → Type*} [Monad m] [MonadLiftT m SetM]
    [LawfulMonadLiftT m SetM]
    {α : Type (max u v)} (c : StateT (Heap Ident) m α) (r : CellRef Ident)
    (measure : r.Value → Nat) (δ : Nat) : Prop :=
  ∀ h z, z ∈ support (c.run h) → measure (r.get z.2) ≤ measure (r.get h) + δ


-- @@ L463-463 verbatim
namespace SupportMeasureBound


-- @@ L465-465 verbatim
section support


-- @@ L467-467 verbatim
variable {m : Type (max u v) → Type*} [Monad m] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]

-- @@ L468-468 verbatim
variable {α β : Type (max u v)} {c : StateT (Heap Ident) m α}

-- @@ L469-469 verbatim
variable {k : α → StateT (Heap Ident) m β} {r : CellRef Ident}

-- @@ L470-470 verbatim
variable {measure : r.Value → Nat}


-- @@ L472-475 verbatim
theorem of_supportPreserves (hc : SupportPreserves c r) :
    SupportMeasureBound c r measure 0 := by
  intro h z hz
  simp [hc h z hz]


-- @@ L477-480 verbatim
theorem mono_delta {δ₁ δ₂ : Nat} (hc : SupportMeasureBound c r measure δ₁)
    (hle : δ₁ ≤ δ₂) :
    SupportMeasureBound c r measure δ₂ :=
  fun h z hz => (hc h z hz).trans (Nat.add_le_add_left hle (measure (r.get h)))


-- @@ L482-490 verbatim
theorem bind {δ₁ δ₂ : Nat} (hc : SupportMeasureBound c r measure δ₁)
    (hk : ∀ a, SupportMeasureBound (k a) r measure δ₂) :
    SupportMeasureBound (c >>= k) r measure (δ₁ + δ₂) := by
  intro h z hz
  rw [StateT.run_bind] at hz
  rcases (mem_support_bind_iff _ _ _).1 hz with ⟨us, hus, hzcont⟩
  exact (hk us.1 us.2 z hzcont).trans (by
    simpa [Nat.add_assoc] using
      Nat.add_le_add_right (hc h us hus) δ₂)


-- @@ L492-492 verbatim
end support


-- @@ L494-494 verbatim
section probability


-- @@ L496-497 verbatim
variable {m : Type (max u v) → Type*} [Monad m] [MonadLiftT m SPMF]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]

-- @@ L498-498 verbatim
variable {α : Type (max u v)} {c : StateT (Heap Ident) m α} {r : CellRef Ident}

-- @@ L499-499 verbatim
variable {measure : r.Value → Nat} {δ : Nat}


-- @@ L501-505 expanded
/-- A measured support bound gives probability zero to exceeding the bound. -/
theorem prob_exceeds_eq_zero (hc : SupportMeasureBound c r measure δ) (h : Heap Ident) :
    (probEvent (c.run h) fun z => measure (r.get h) + δ < measure (r.get z.2)) = 0 :=
  probEvent_eq_zero_iff.2 fun z hz hgt => Nat.not_lt_of_ge (hc h z hz) hgt


-- @@ L507-507 verbatim
end probability


-- @@ L509-509 verbatim
end SupportMeasureBound


-- @@ L511-511 verbatim
/-! ## Deterministic specialization -/


-- @@ L513-521 verbatim
/-- A deterministic heap program preserves a cell reference when the final
heap has the same value at that reference as the initial heap.

This exact `Id`-specific predicate is equivalent to `SupportPreserves`, whose
support contains exactly the single deterministic output. The exact form keeps
deterministic examples pleasant to use, while the combinator proofs below are
derived from the generic support-based API. -/
def Preserves {α : Type (max u v)} (c : StateT (Heap Ident) Id α) (r : CellRef Ident) : Prop :=
  ∀ h, r.get (c.run h).2 = r.get h


-- @@ L523-526 verbatim
/-- A deterministic heap program writes only a set of identifiers when every
cell outside the set is preserved. -/
def WritesOnly {α : Type (max u v)} (c : StateT (Heap Ident) Id α) (writes : Set Ident) : Prop :=
  ∀ r : CellRef Ident, r.id ∉ writes → Preserves c r


-- @@ L528-534 verbatim
theorem supportPreserves_of_preserves {α : Type (max u v)} {c : StateT (Heap Ident) Id α}
    {r : CellRef Ident} (hc : Preserves c r) :
    SupportPreserves c r := by
  intro h z hz
  obtain rfl : z = (c.run h).run := by simpa [Id.support_eq_singleton] using hz
  change r.get (c.run h).2 = r.get h
  exact hc h


-- @@ L536-539 verbatim
theorem preserves_of_supportPreserves {α : Type (max u v)} {c : StateT (Heap Ident) Id α}
    {r : CellRef Ident} (hc : SupportPreserves c r) :
    Preserves c r :=
  fun h => hc h (c.run h).run (by simp [Id.support_eq_singleton])


-- @@ L541-546 verbatim
/-- For the `Id` monad, support-based cell preservation is exactly the same as
the direct final-state equality predicate. -/
theorem supportPreserves_iff_preserves {α : Type (max u v)} {c : StateT (Heap Ident) Id α}
    {r : CellRef Ident} :
    SupportPreserves c r ↔ Preserves c r :=
  ⟨preserves_of_supportPreserves, supportPreserves_of_preserves⟩


-- @@ L548-551 verbatim
theorem supportWritesOnly_of_writesOnly {α : Type (max u v)} {c : StateT (Heap Ident) Id α}
    {writes : Set Ident} (hc : WritesOnly c writes) :
    SupportWritesOnly c writes :=
  fun r hr => supportPreserves_of_preserves (hc r hr)


-- @@ L553-556 verbatim
theorem writesOnly_of_supportWritesOnly {α : Type (max u v)} {c : StateT (Heap Ident) Id α}
    {writes : Set Ident} (hc : SupportWritesOnly c writes) :
    WritesOnly c writes :=
  fun r hr => preserves_of_supportPreserves (hc r hr)


-- @@ L558-561 verbatim
theorem supportWritesOnly_iff_writesOnly {α : Type (max u v)} {c : StateT (Heap Ident) Id α}
    {writes : Set Ident} :
    SupportWritesOnly c writes ↔ WritesOnly c writes :=
  ⟨writesOnly_of_supportWritesOnly, supportWritesOnly_of_writesOnly⟩


-- @@ L563-568 verbatim
theorem writesOnly_mono {α : Type (max u v)} {c : StateT (Heap Ident) Id α}
    {writes₁ writes₂ : Set Ident} (hc : WritesOnly c writes₁)
    (hsubset : writes₁ ⊆ writes₂) :
    WritesOnly c writes₂ :=
  writesOnly_of_supportWritesOnly
    (supportWritesOnly_mono (supportWritesOnly_of_writesOnly hc) hsubset)


-- @@ L570-572 verbatim
theorem preserves_pure {α : Type (max u v)} (x : α) (r : CellRef Ident) :
    Preserves (pure x : StateT (Heap Ident) Id α) r :=
  preserves_of_supportPreserves (supportPreserves_pure x r)


-- @@ L574-579 verbatim
theorem preserves_read (r s : CellRef Ident) :
    Preserves (r.read) s := by
  refine preserves_of_supportPreserves fun h z hz => ?_
  change z ∈ ({(r.get h, h)} : Set _) at hz
  obtain rfl : z = (r.get h, h) := by simpa using hz
  simp


-- @@ L581-583 verbatim
theorem read_writesOnly_empty (r : CellRef Ident) :
    WritesOnly (r.read) (∅ : Set Ident) :=
  fun s _ => preserves_read r s


-- @@ L585-591 verbatim
theorem preserves_bind {α β : Type (max u v)} {c : StateT (Heap Ident) Id α}
    {k : α → StateT (Heap Ident) Id β} {r : CellRef Ident}
    (hc : Preserves c r) (hk : ∀ a, Preserves (k a) r) :
    Preserves (c >>= k) r :=
  preserves_of_supportPreserves
    (supportPreserves_bind (supportPreserves_of_preserves hc)
      (fun a => supportPreserves_of_preserves (hk a)))


-- @@ L593-599 verbatim
theorem write_writesOnly_single [DecidableEq Ident] (r : CellRef Ident) (x : r.Value) :
    WritesOnly (r.write x) ({r.id} : Set Ident) := by
  refine writesOnly_of_supportWritesOnly ?_
  intro s hs h z hz
  change z ∈ ({(PUnit.unit, r.set h x)} : Set _) at hz
  obtain rfl : z = (PUnit.unit, r.set h x) := by simpa using hz
  simpa using get_set_of_ne r s h x hs


-- @@ L601-607 verbatim
theorem writesOnly_bind {α β : Type (max u v)} {c : StateT (Heap Ident) Id α}
    {k : α → StateT (Heap Ident) Id β} {writes₁ writes₂ : Set Ident}
    (hc : WritesOnly c writes₁) (hk : ∀ a, WritesOnly (k a) writes₂) :
    WritesOnly (c >>= k) (writes₁ ∪ writes₂) :=
  writesOnly_of_supportWritesOnly
    (supportWritesOnly_bind (supportWritesOnly_of_writesOnly hc)
      (fun a => supportWritesOnly_of_writesOnly (hk a)))


-- @@ L609-619 verbatim
/-- Dependent bind form: the continuation's write set may depend on the
first result. The resulting write set is the union of the first write set and
all possible continuation write sets. -/
theorem writesOnly_bind_dep {α β : Type (max u v)} {c : StateT (Heap Ident) Id α}
    {k : α → StateT (Heap Ident) Id β} {writes₁ : Set Ident}
    {writes₂ : α → Set Ident}
    (hc : WritesOnly c writes₁) (hk : ∀ a, WritesOnly (k a) (writes₂ a)) :
    WritesOnly (c >>= k) (writes₁ ∪ {i | ∃ a, i ∈ writes₂ a}) :=
  writesOnly_of_supportWritesOnly
    (supportWritesOnly_bind_dep (supportWritesOnly_of_writesOnly hc)
      (fun a => supportWritesOnly_of_writesOnly (hk a)))


-- @@ L621-621 verbatim
/-! ## Read agreement and result-dependence footprints -/


-- @@ L623-626 verbatim
/-- Two heaps agree on a set of cell identifiers when every reference whose
identifier is in the set reads the same value from both heaps. -/
def SameOn (cells : Set Ident) (h₁ h₂ : Heap Ident) : Prop :=
  ∀ r : CellRef Ident, r.id ∈ cells → r.get h₁ = r.get h₂


-- @@ L628-630 verbatim
theorem sameOn_refl (cells : Set Ident) (h : Heap Ident) :
    SameOn cells h h :=
  fun _ _ => rfl


-- @@ L632-635 verbatim
theorem sameOn_mono {cells₁ cells₂ : Set Ident} {h₁ h₂ : Heap Ident}
    (hsubset : cells₁ ⊆ cells₂) (hsame : SameOn cells₂ h₁ h₂) :
    SameOn cells₁ h₁ h₂ :=
  fun r hr => hsame r (hsubset hr)


-- @@ L637-640 verbatim
theorem sameOn_singleton_read {r : CellRef Ident} {h₁ h₂ : Heap Ident}
    (hsame : SameOn ({r.id} : Set Ident) h₁ h₂) :
    r.get h₁ = r.get h₂ :=
  hsame r rfl


-- @@ L642-647 verbatim
/-- A deterministic heap program's result depends only on a set of cells when
heaps agreeing on those cells produce equal return values. This intentionally
tracks only the returned value, not the final heap. -/
def ResultDependsOnly {α : Type (max u v)} (c : StateT (Heap Ident) Id α)
    (reads : Set Ident) : Prop :=
  ∀ h₁ h₂, SameOn reads h₁ h₂ → (c.run h₁).1 = (c.run h₂).1


-- @@ L649-651 verbatim
theorem resultDependsOnly_pure {α : Type (max u v)} (x : α) :
    ResultDependsOnly (pure x : StateT (Heap Ident) Id α) (∅ : Set Ident) :=
  fun _ _ _ => rfl


-- @@ L653-655 verbatim
theorem resultDependsOnly_read (r : CellRef Ident) :
    ResultDependsOnly r.read ({r.id} : Set Ident) :=
  fun _ _ hsame => sameOn_singleton_read hsame


-- @@ L657-659 verbatim
theorem resultDependsOnly_write [DecidableEq Ident] (r : CellRef Ident) (x : r.Value) :
    ResultDependsOnly (r.write x) (∅ : Set Ident) :=
  fun _ _ _ => rfl


-- @@ L661-661 verbatim
/-! ## Compositional write footprints -/


-- @@ L663-670 verbatim
/-- A compositional write footprint packages a deterministic heap program with
the set of cells it may write and the proof that all other cells are
preserved. -/
structure WriteFootprint {α : Type (max u v)} (c : StateT (Heap Ident) Id α) where
  /-- Cells that the program may write. -/
  writes : Set Ident
  /-- Soundness: every cell outside `writes` is framed through. -/
  sound : WritesOnly c writes


-- @@ L672-672 verbatim
namespace WriteFootprint


-- @@ L674-674 verbatim
variable {α β : Type (max u v)}


-- @@ L676-679 verbatim
theorem preserves {c : StateT (Heap Ident) Id α} (footprint : WriteFootprint c)
    (r : CellRef Ident) (hr : r.id ∉ footprint.writes) :
    Preserves c r :=
  footprint.sound r hr


-- @@ L681-683 verbatim
def pure (x : α) : WriteFootprint (pure x : StateT (Heap Ident) Id α) where
  writes := ∅
  sound := fun r _ => preserves_pure x r


-- @@ L685-687 verbatim
def read (r : CellRef Ident) : WriteFootprint r.read where
  writes := ∅
  sound := read_writesOnly_empty r


-- @@ L689-692 verbatim
def write [DecidableEq Ident] (r : CellRef Ident) (x : r.Value) :
    WriteFootprint (r.write x) where
  writes := {r.id}
  sound := write_writesOnly_single r x


-- @@ L694-698 verbatim
def bind {c : StateT (Heap Ident) Id α} {k : α → StateT (Heap Ident) Id β}
    (footprint : WriteFootprint c) (kont : ∀ a, WriteFootprint (k a)) :
    WriteFootprint (c >>= k) where
  writes := footprint.writes ∪ {i | ∃ a, i ∈ (kont a).writes}
  sound := writesOnly_bind_dep footprint.sound (fun a => (kont a).sound)


-- @@ L700-700 verbatim
end WriteFootprint


-- @@ L702-702 verbatim
end CellRef


-- @@ L704-704 verbatim
/-! ## Query-implementation cell frames -/


-- @@ L706-706 verbatim
noncomputable section


-- @@ L708-708 verbatim
open OracleComp OracleSpec


-- @@ L710-710 verbatim
namespace QueryImpl


-- @@ L712-712 verbatim
variable {ι : Type uι} {spec : OracleSpec.{uι, max u₀ v} ι}

-- @@ L713-713 verbatim
variable {Ident₀ : Type u₀} [CellSpec.{u₀, max u₀ v} Ident₀]

-- @@ L714-714 verbatim
variable {m : Type (max u₀ v) → Type*} [Monad m] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]


-- @@ L716-721 verbatim
/-- A `QueryImpl` preserves a heap cell when each single query step leaves
that cell unchanged on every support-reachable post-state. This is the
support-level analogue of `CellRef.Preserves` for probabilistic handlers. -/
def PreservesCell (impl : QueryImpl spec (StateT (Heap Ident₀) m))
    (r : CellRef Ident₀) : Prop :=
  ∀ t h z, z ∈ support ((impl t).run h) → r.get z.2 = r.get h


-- @@ L723-727 verbatim
/-- A `QueryImpl` writes only the cells named by a per-query footprint when
each query step support-preserves every cell outside its footprint. -/
def WritesOnlyCells (impl : QueryImpl spec (StateT (Heap Ident₀) m))
    (writes : spec.Domain → Set Ident₀) : Prop :=
  ∀ t, CellRef.SupportWritesOnly (impl t) (writes t)


-- @@ L729-733 verbatim
theorem writesOnlyCells_mono {impl : QueryImpl spec (StateT (Heap Ident₀) m)}
    {writes₁ writes₂ : spec.Domain → Set Ident₀} (himpl : WritesOnlyCells impl writes₁)
    (hsubset : ∀ t, writes₁ t ⊆ writes₂ t) :
    WritesOnlyCells impl writes₂ :=
  fun t => CellRef.supportWritesOnly_mono (himpl t) (hsubset t)


-- @@ L735-740 verbatim
theorem preservesCell_of_writesOnlyCells
    {impl : QueryImpl spec (StateT (Heap Ident₀) m)}
    {writes : spec.Domain → Set Ident₀} {r : CellRef Ident₀}
    (himpl : WritesOnlyCells impl writes) (hr : ∀ t, r.id ∉ writes t) :
    PreservesCell impl r :=
  fun t h z hz => himpl t r (hr t) h z hz


-- @@ L742-749 verbatim
/-- A compositional cell-write footprint for a whole query implementation: every
domain element gets a set of cells it may write, plus a support-level proof
that no other cells change. -/
structure CellWriteFootprint (impl : QueryImpl spec (StateT (Heap Ident₀) m)) where
  /-- Per-query cells that may be written by the handler branch. -/
  writes : spec.Domain → Set Ident₀
  /-- Soundness of the footprint. -/
  sound : WritesOnlyCells impl writes


-- @@ L751-751 verbatim
namespace CellWriteFootprint


-- @@ L753-757 verbatim
theorem preservesCell {impl : QueryImpl spec (StateT (Heap Ident₀) m)}
    (footprint : CellWriteFootprint impl) (r : CellRef Ident₀)
    (hr : ∀ t, r.id ∉ footprint.writes t) :
    PreservesCell impl r :=
  preservesCell_of_writesOnlyCells footprint.sound hr


-- @@ L759-759 verbatim
end CellWriteFootprint


-- @@ L761-761 verbatim
end QueryImpl


-- @@ L763-763 verbatim
namespace OracleComp


-- @@ L765-765 verbatim
variable {ι : Type uι} {spec : OracleSpec.{uι, max u₀ v} ι}

-- @@ L766-766 verbatim
variable {α : Type (max u₀ v)}

-- @@ L767-767 verbatim
variable {Ident₀ : Type u₀} [CellSpec.{u₀, max u₀ v} Ident₀]

-- @@ L768-769 verbatim
variable {m : Type (max u₀ v)
    → Type*} [Monad m] [LawfulMonad m] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]


-- @@ L771-794 verbatim
/-- If every handler query preserves a cell, then interpreting any
`OracleComp` through that handler preserves the cell. -/
theorem simulateQ_run_cellPreserved
    (impl : QueryImpl spec (StateT (Heap Ident₀) m))
    (r : CellRef Ident₀) (himpl : QueryImpl.PreservesCell impl r)
    (A : OracleComp spec α) (h : Heap Ident₀) :
    ∀ z ∈ support ((simulateQ impl A).run h), r.get z.2 = r.get h := by
  revert h
  induction A using OracleComp.inductionOn with
  | pure a =>
      intro h z hz
      obtain rfl := (mem_support_pure_iff z (a, h)).1 hz
      simp
  | query_bind t oa ih =>
      intro h z hz
      have hz' :
          z ∈ support
            (((simulateQ impl
                  (OracleSpec.query t : OracleComp spec (spec.Range t))).run h) >>=
              fun us => (simulateQ impl (oa us.1)).run us.2) := by
        simpa [simulateQ_bind, OracleComp.liftM_def] using hz
      rcases (mem_support_bind_iff _ _ _).1 hz' with ⟨us, hus, hzcont⟩
      refine (ih us.1 us.2 z hzcont).trans (himpl t h us ?_)
      simpa [simulateQ_spec_query] using hus


-- @@ L796-796 verbatim
end OracleComp


-- @@ L798-798 verbatim
namespace QueryImpl


-- @@ L800-800 verbatim
section probability


-- @@ L802-802 verbatim
variable {ι : Type uι} {spec : OracleSpec.{uι, max u₀ v} ι}

-- @@ L803-803 verbatim
variable {Ident₀ : Type u₀} [CellSpec.{u₀, max u₀ v} Ident₀]

-- @@ L804-805 verbatim
variable {m : Type (max u₀ v) → Type*} [Monad m] [MonadLiftT m SPMF]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]


-- @@ L807-811 expanded
theorem PreservesCell.prob_changed_eq_zero {impl : QueryImpl spec (StateT (Heap Ident₀) m)}
    {r : CellRef Ident₀} (himpl : PreservesCell impl r) (t : spec.Domain) (h : Heap Ident₀) :
    (probEvent ((impl t).run h) fun z => r.get z.2 ≠ r.get h) = 0 :=
  CellRef.SupportPreserves.prob_changed_eq_zero (himpl t) h


-- @@ L813-818 expanded
theorem PreservesCell.prob_unchanged_eq_sub_probFailure
    {impl : QueryImpl spec (StateT (Heap Ident₀) m)} {r : CellRef Ident₀}
    (himpl : PreservesCell impl r) (t : spec.Domain) (h : Heap Ident₀) :
    (probEvent ((impl t).run h) fun z => r.get z.2 = r.get h) = 1 - probFailure ((impl t).run h) :=
  CellRef.SupportPreserves.prob_unchanged_eq_sub_probFailure (himpl t) h


-- @@ L820-826 expanded
theorem CellWriteFootprint.prob_changed_eq_zero {impl : QueryImpl spec (StateT (Heap Ident₀) m)}
    (footprint : CellWriteFootprint impl) (r : CellRef Ident₀) (hr : ∀ t, r.id ∉ footprint.writes t)
    (t : spec.Domain) (h : Heap Ident₀) :
    (probEvent ((impl t).run h) fun z => r.get z.2 ≠ r.get h) = 0 :=
  (footprint.preservesCell r hr).prob_changed_eq_zero t h


-- @@ L828-835 expanded
theorem CellWriteFootprint.prob_unchanged_eq_sub_probFailure
    {impl : QueryImpl spec (StateT (Heap Ident₀) m)} (footprint : CellWriteFootprint impl)
    (r : CellRef Ident₀) (hr : ∀ t, r.id ∉ footprint.writes t) (t : spec.Domain) (h : Heap Ident₀) :
    (probEvent ((impl t).run h) fun z => r.get z.2 = r.get h) = 1 - probFailure ((impl t).run h) :=
  (footprint.preservesCell r hr).prob_unchanged_eq_sub_probFailure t h


-- @@ L837-837 verbatim
end probability


-- @@ L839-839 verbatim
end QueryImpl


-- @@ L841-841 verbatim
namespace OracleComp


-- @@ L843-843 verbatim
section probability


-- @@ L845-845 verbatim
variable {ι : Type uι} {spec : OracleSpec.{uι, max u₀ v} ι}

-- @@ L846-846 verbatim
variable {α : Type (max u₀ v)}

-- @@ L847-847 verbatim
variable {Ident₀ : Type u₀} [CellSpec.{u₀, max u₀ v} Ident₀]

-- @@ L848-849 verbatim
variable {m : Type (max u₀ v) → Type*} [Monad m] [LawfulMonad m] [MonadLiftT m SPMF]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]


-- @@ L851-857 expanded
theorem simulateQ_run_cellChange_prob_eq_zero (impl : QueryImpl spec (StateT (Heap Ident₀) m))
    (r : CellRef Ident₀) (himpl : QueryImpl.PreservesCell impl r) (A : OracleComp spec α)
    (h : Heap Ident₀) : (probEvent ((simulateQ impl A).run h) fun z => r.get z.2 ≠ r.get h) = 0 :=
  probEvent_eq_zero_iff.2 fun z hz hchange =>
    hchange (simulateQ_run_cellPreserved impl r himpl A h z hz)


-- @@ L859-866 expanded
theorem simulateQ_run_cellUnchanged_prob_eq_sub_probFailure
    (impl : QueryImpl spec (StateT (Heap Ident₀) m)) (r : CellRef Ident₀)
    (himpl : QueryImpl.PreservesCell impl r) (A : OracleComp spec α) (h : Heap Ident₀) :
    (probEvent ((simulateQ impl A).run h) fun z => r.get z.2 = r.get h) =
      1 - probFailure ((simulateQ impl A).run h) :=
  CellRef.SupportPreserves.prob_unchanged_eq_sub_probFailure
    (fun h' z hz => simulateQ_run_cellPreserved impl r himpl A h' z hz) h


-- @@ L868-874 expanded
theorem simulateQ_run_cellUnchanged_prob_eq_one_of_probFailure_eq_zero
    (impl : QueryImpl spec (StateT (Heap Ident₀) m)) (r : CellRef Ident₀)
    (himpl : QueryImpl.PreservesCell impl r) (A : OracleComp spec α) (h : Heap Ident₀)
    (hnf : probFailure ((simulateQ impl A).run h) = 0) :
    (probEvent ((simulateQ impl A).run h) fun z => r.get z.2 = r.get h) = 1 := by
  simp [simulateQ_run_cellUnchanged_prob_eq_sub_probFailure impl r himpl A h, hnf]


-- @@ L876-876 verbatim
end probability


-- @@ L878-878 verbatim
section probability_total


-- @@ L880-880 verbatim
variable {ι : Type uι} {spec : OracleSpec.{uι, max u₀ v} ι}

-- @@ L881-881 verbatim
variable {α : Type (max u₀ v)}

-- @@ L882-882 verbatim
variable {Ident₀ : Type u₀} [CellSpec.{u₀, max u₀ v} Ident₀]

-- @@ L883-884 verbatim
variable {m : Type (max u₀ v) → Type*} [Monad m] [LawfulMonad m] [MonadLiftT m PMF]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]


-- @@ L886-892 expanded
theorem simulateQ_run_cellUnchanged_prob_eq_one (impl : QueryImpl spec (StateT (Heap Ident₀) m))
    (r : CellRef Ident₀) (himpl : QueryImpl.PreservesCell impl r) (A : OracleComp spec α)
    (h : Heap Ident₀) : (probEvent ((simulateQ impl A).run h) fun z => r.get z.2 = r.get h) = 1 :=
  simulateQ_run_cellUnchanged_prob_eq_one_of_probFailure_eq_zero impl r himpl A h
    (probFailure_of_liftM_PMF ((simulateQ impl A).run h))


-- @@ L894-894 verbatim
end probability_total


-- @@ L896-896 verbatim
end OracleComp


-- @@ L898-898 verbatim
namespace QueryImpl


-- @@ L900-900 verbatim
variable {ι : Type uι} {spec : OracleSpec.{uι, max u₀ v} ι}

-- @@ L901-901 verbatim
variable {α : Type (max u₀ v)}

-- @@ L902-902 verbatim
variable {Ident₀ : Type u₀} [CellSpec.{u₀, max u₀ v} Ident₀]

-- @@ L903-904 verbatim
variable {m : Type (max u₀ v)
    → Type*} [Monad m] [LawfulMonad m] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]


-- @@ L906-915 verbatim
/-- A query-implementation cell-write footprint lifts through interpretation: if a
cell is outside every per-query footprint, the interpreted computation
preserves that cell. -/
theorem CellWriteFootprint.simulateQ_run_cellPreserved
    {impl : QueryImpl spec (StateT (Heap Ident₀) m)}
    (footprint : CellWriteFootprint impl) (r : CellRef Ident₀)
    (hr : ∀ t, r.id ∉ footprint.writes t)
    (A : OracleComp spec α) (h : Heap Ident₀) :
    ∀ z ∈ support ((simulateQ impl A).run h), r.get z.2 = r.get h :=
  OracleComp.simulateQ_run_cellPreserved impl r (footprint.preservesCell r hr) A h


-- @@ L917-917 verbatim
section probability


-- @@ L919-919 verbatim
variable {ι : Type uι} {spec : OracleSpec.{uι, max u₀ v} ι}

-- @@ L920-920 verbatim
variable {α : Type (max u₀ v)}

-- @@ L921-921 verbatim
variable {Ident₀ : Type u₀} [CellSpec.{u₀, max u₀ v} Ident₀]

-- @@ L922-923 verbatim
variable {m : Type (max u₀ v) → Type*} [Monad m] [LawfulMonad m] [MonadLiftT m SPMF]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]


-- @@ L925-932 expanded
theorem CellWriteFootprint.simulateQ_run_cellChange_prob_eq_zero
    {impl : QueryImpl spec (StateT (Heap Ident₀) m)} (footprint : CellWriteFootprint impl)
    (r : CellRef Ident₀) (hr : ∀ t, r.id ∉ footprint.writes t) (A : OracleComp spec α)
    (h : Heap Ident₀) : (probEvent ((simulateQ impl A).run h) fun z => r.get z.2 ≠ r.get h) = 0 :=
  OracleComp.simulateQ_run_cellChange_prob_eq_zero impl r (footprint.preservesCell r hr) A h


-- @@ L934-942 expanded
theorem CellWriteFootprint.simulateQ_run_cellUnchanged_prob_eq_sub_probFailure
    {impl : QueryImpl spec (StateT (Heap Ident₀) m)} (footprint : CellWriteFootprint impl)
    (r : CellRef Ident₀) (hr : ∀ t, r.id ∉ footprint.writes t) (A : OracleComp spec α)
    (h : Heap Ident₀) :
    (probEvent ((simulateQ impl A).run h) fun z => r.get z.2 = r.get h) =
      1 - probFailure ((simulateQ impl A).run h) :=
  OracleComp.simulateQ_run_cellUnchanged_prob_eq_sub_probFailure impl r
    (footprint.preservesCell r hr) A h


-- @@ L944-952 expanded
theorem CellWriteFootprint.simulateQ_run_cellUnchanged_prob_eq_one_of_probFailure_eq_zero
    {impl : QueryImpl spec (StateT (Heap Ident₀) m)} (footprint : CellWriteFootprint impl)
    (r : CellRef Ident₀) (hr : ∀ t, r.id ∉ footprint.writes t) (A : OracleComp spec α)
    (h : Heap Ident₀) (hnf : probFailure ((simulateQ impl A).run h) = 0) :
    (probEvent ((simulateQ impl A).run h) fun z => r.get z.2 = r.get h) = 1 :=
  OracleComp.simulateQ_run_cellUnchanged_prob_eq_one_of_probFailure_eq_zero impl r
    (footprint.preservesCell r hr) A h hnf


-- @@ L954-954 verbatim
end probability


-- @@ L956-956 verbatim
section probability_total


-- @@ L958-958 verbatim
variable {ι : Type uι} {spec : OracleSpec.{uι, max u₀ v} ι}

-- @@ L959-959 verbatim
variable {α : Type (max u₀ v)}

-- @@ L960-960 verbatim
variable {Ident₀ : Type u₀} [CellSpec.{u₀, max u₀ v} Ident₀]

-- @@ L961-962 verbatim
variable {m : Type (max u₀ v) → Type*} [Monad m] [LawfulMonad m] [MonadLiftT m PMF]
    [LawfulMonadLiftT m PMF] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]


-- @@ L964-972 expanded
omit [LawfulMonadLiftT m PMF] in
theorem CellWriteFootprint.simulateQ_run_cellUnchanged_prob_eq_one
    {impl : QueryImpl spec (StateT (Heap Ident₀) m)} (footprint : CellWriteFootprint impl)
    (r : CellRef Ident₀) (hr : ∀ t, r.id ∉ footprint.writes t) (A : OracleComp spec α)
    (h : Heap Ident₀) : (probEvent ((simulateQ impl A).run h) fun z => r.get z.2 = r.get h) = 1 :=
  OracleComp.simulateQ_run_cellUnchanged_prob_eq_one impl r (footprint.preservesCell r hr) A h


-- @@ L974-974 verbatim
end probability_total


-- @@ L976-976 verbatim
end QueryImpl


-- @@ L978-978 verbatim
end


-- @@ L980-980 verbatim
/-! ## Examples -/


-- @@ L982-982 verbatim
namespace CellRefExample


-- @@ L984-989 verbatim
/-- Three toy cells: a log counter, a cache counter, and an immutable flag. -/
inductive DemoCell where
  | log
  | cache
  | flag
  deriving DecidableEq


-- @@ L991-999 verbatim
instance : CellSpec DemoCell where
  type
    | .log => Nat
    | .cache => Nat
    | .flag => Bool
  default
    | .log => 0
    | .cache => 0
    | .flag => false


-- @@ L1001-1001 verbatim
@[reducible] def logRef : CellRef DemoCell := ⟨.log⟩

-- @@ L1002-1002 verbatim
@[reducible] def cacheRef : CellRef DemoCell := ⟨.cache⟩

-- @@ L1003-1003 verbatim
@[reducible] def flagRef : CellRef DemoCell := ⟨.flag⟩


-- @@ L1005-1005 verbatim
/-! ### Query-handler write footprints -/


-- @@ L1007-1012 verbatim
/-- A tiny external oracle interface for the support-based footprint demo. -/
inductive DemoQuery where
  | touchLog
  | touchCache
  | readFlag
  deriving DecidableEq


-- @@ L1014-1015 verbatim
/-- Every demo query returns unit; the interesting part is the heap effect. -/
def demoSpec : OracleSpec.{0, 0} DemoQuery := fun _ => PUnit


-- @@ L1017-1024 verbatim
/-- A toy probabilistic handler with heap effects. Two branches write cells,
and one branch reads the flag without modifying it. -/
def demoImpl : QueryImpl demoSpec (StateT (Heap DemoCell) ProbComp)
  | .touchLog => logRef.writeM 1
  | .touchCache => cacheRef.writeM 1
  | .readFlag => do
      let _ ← (flagRef.readM : StateT (Heap DemoCell) ProbComp Bool)
      pure PUnit.unit


-- @@ L1026-1030 verbatim
/-- Per-query write footprint for `demoImpl`. -/
def demoWrites : DemoQuery → Set DemoCell
  | .touchLog => {DemoCell.log}
  | .touchCache => {DemoCell.cache}
  | .readFlag => ∅


-- @@ L1032-1054 verbatim
/-- The handler writes only the cells declared by `demoWrites`. -/
theorem demoImpl_writesOnly :
    QueryImpl.WritesOnlyCells demoImpl demoWrites := by
  intro t
  cases t with
  | touchLog =>
      change CellRef.SupportWritesOnly
        (logRef.writeM 1 : StateT (Heap DemoCell) ProbComp PUnit) {DemoCell.log}
      simpa [demoSpec, demoImpl, demoWrites, logRef] using
        CellRef.writeM_supportWritesOnly_single logRef 1
  | touchCache =>
      change CellRef.SupportWritesOnly
        (cacheRef.writeM 1 : StateT (Heap DemoCell) ProbComp PUnit) {DemoCell.cache}
      simpa [demoSpec, demoImpl, demoWrites, cacheRef] using
        CellRef.writeM_supportWritesOnly_single cacheRef 1
  | readFlag =>
      change CellRef.SupportWritesOnly
        ((do let _ ← (flagRef.readM : StateT (Heap DemoCell) ProbComp Bool)
             pure PUnit.unit) : StateT (Heap DemoCell) ProbComp PUnit) ∅
      simpa [demoSpec, demoImpl, demoWrites] using
        CellRef.supportWritesOnly_bind
          (CellRef.readM_supportWritesOnly_empty (m := ProbComp) flagRef)
          (fun _ => CellRef.supportWritesOnly_pure_empty (m := ProbComp) PUnit.unit)


-- @@ L1056-1060 verbatim
/-- Pack the handler-level footprint once, so later proofs need not unfold
every query branch. -/
def demoFootprint : QueryImpl.CellWriteFootprint demoImpl where
  writes := demoWrites
  sound := demoImpl_writesOnly


-- @@ L1062-1067 verbatim
/-- The flag is outside every branch footprint, so each handler step preserves
it. -/
theorem demoImpl_preserves_flag :
    QueryImpl.PreservesCell demoImpl flagRef :=
  demoFootprint.preservesCell flagRef (by
    intro t; cases t <;> simp [demoFootprint, demoWrites])


-- @@ L1069-1073 verbatim
/-- A tiny client computation that calls several branches of the demo handler. -/
def demoClient : OracleComp demoSpec PUnit := do
  let _ ← liftM (demoSpec.query DemoQuery.touchCache)
  let _ ← liftM (demoSpec.query DemoQuery.touchLog)
  liftM (demoSpec.query DemoQuery.readFlag)


-- @@ L1075-1081 verbatim
/-- The handler footprint automatically lifts through `simulateQ`: the whole
interpreted computation preserves the flag, not just a single query branch. -/
theorem demoClient_preserves_flag (h : Heap DemoCell) :
    ∀ z ∈ support ((simulateQ demoImpl demoClient).run h),
      flagRef.get z.2 = flagRef.get h :=
  demoFootprint.simulateQ_run_cellPreserved flagRef (by
    intro t; cases t <;> simp [demoFootprint, demoWrites]) demoClient h


-- @@ L1083-1086 verbatim
/-- The previous theorem as a reusable support-preservation predicate. -/
theorem demoClient_supportPreserves_flag :
    CellRef.SupportPreserves (simulateQ demoImpl demoClient) flagRef :=
  fun h z hz => demoClient_preserves_flag h z hz


-- @@ L1088-1095 expanded
/-- From the empty heap, the framed flag is never `true`. The cell's
`CellSpec.default` value is `false`, so support preservation collapses the event
to one with no reachable witness. -/
theorem demoClient_prob_flag_true_eq_zero :
    (probEvent ((simulateQ demoImpl demoClient).run (Heap.empty : Heap DemoCell)) fun z =>
        flagRef.get z.2 = true) =
      0 :=
  CellRef.SupportPreserves.prob_final_eq_eq_zero_of_ne demoClient_supportPreserves_flag
    (Heap.empty : Heap DemoCell) (by decide)


-- @@ L1097-1102 expanded
/-- Probability-one preservation for the framed flag: under the uniform-sampling
semantics of `ProbComp`, the handler never changes the flag and never aborts. -/
theorem demoClient_prob_flag_unchanged_eq_one (h : Heap DemoCell) :
    (probEvent ((simulateQ demoImpl demoClient).run h) fun z => flagRef.get z.2 = flagRef.get h) =
      1 :=
  CellRef.SupportPreserves.prob_unchanged_eq_one demoClient_supportPreserves_flag h


-- @@ L1104-1110 verbatim
/-- Increment the cache counter and append one log entry. The program never
writes `flagRef`. -/
def cacheAndLogStep : StateT (Heap DemoCell) Id PUnit := do
  let cache ← cacheRef.read
  let _ ← cacheRef.write (cache + 1)
  let log ← logRef.read
  logRef.write (log + 1)


-- @@ L1112-1128 verbatim
/-- The step writes only `.cache` and `.log`. -/
theorem cacheAndLogStep_writesOnly :
    CellRef.WritesOnly cacheAndLogStep ({DemoCell.cache, DemoCell.log} : Set DemoCell) := by
  classical
  intro r hr h
  rcases r with ⟨id⟩
  cases id with
  | log => exact (hr (by simp)).elim
  | cache => exact (hr (by simp)).elim
  | flag =>
      change
        (((h.update DemoCell.cache (h.get DemoCell.cache + 1)).update
            DemoCell.log
            (((h.update DemoCell.cache (h.get DemoCell.cache + 1)).get
              DemoCell.log) + 1)).get DemoCell.flag =
          h.get DemoCell.flag)
      simp


-- @@ L1130-1154 verbatim
/-- A compositional footprint for `cacheAndLogStep`. Reads contribute no writes,
writes contribute singleton footprints, and binds union the footprints. -/
def cacheAndLogFootprint :
    CellRef.WriteFootprint
      (cacheRef.read >>= fun cache =>
        cacheRef.write (cache + 1) >>= fun _ =>
          logRef.read >>= fun log =>
            logRef.write (log + 1)) where
  writes := {DemoCell.cache, DemoCell.log}
  sound := by
    intro r hr
    apply CellRef.preserves_bind
    · exact CellRef.preserves_read cacheRef r
    · intro cache
      apply CellRef.preserves_bind
      · exact (CellRef.write_writesOnly_single cacheRef (cache + 1)) r (by
          intro hmem
          exact hr (Or.inl hmem))
      · intro _
        apply CellRef.preserves_bind
        · exact CellRef.preserves_read logRef r
        · intro log
          exact (CellRef.write_writesOnly_single logRef (log + 1)) r (by
            intro hmem
            exact hr (Or.inr hmem))


-- @@ L1156-1161 verbatim
/-- The compositional footprint gives flag preservation without unfolding each
state update in the final proof. -/
theorem cacheAndLogStep_preserves_flag_via_footprint :
    CellRef.Preserves cacheAndLogStep flagRef := by
  unfold cacheAndLogStep
  exact cacheAndLogFootprint.preserves flagRef (by simp [cacheAndLogFootprint])


-- @@ L1163-1167 verbatim
/-- A smaller example that uses the generic frame combinators directly: two
writes outside the flag cell preserve the flag. -/
def writeCacheThenLog : StateT (Heap DemoCell) Id PUnit := do
  let _ ← cacheRef.write 1
  logRef.write 1


-- @@ L1169-1175 verbatim
theorem writeCacheThenLog_preserves_flag :
    CellRef.Preserves writeCacheThenLog flagRef := by
  unfold writeCacheThenLog
  apply CellRef.preserves_bind
  · exact (CellRef.write_writesOnly_single cacheRef 1) flagRef (by simp)
  · intro _
    exact (CellRef.write_writesOnly_single logRef 1) flagRef (by simp)


-- @@ L1177-1182 verbatim
/-- A compositional footprint for the two-write program. The write set is
computed by `WriteFootprint.bind`: first `{cache}`, then `{log}`. -/
def writeCacheThenLogFootprint :
    CellRef.WriteFootprint (cacheRef.write 1 >>= fun _ => logRef.write 1) :=
  (CellRef.WriteFootprint.write cacheRef 1).bind fun _ =>
    CellRef.WriteFootprint.write logRef 1


-- @@ L1184-1189 verbatim
/-- Once the footprint says the write set is `{cache, log}`, flag preservation
is a one-line frame application plus a membership proof. -/
theorem writeCacheThenLog_preserves_flag_via_footprint :
    CellRef.Preserves writeCacheThenLog flagRef := by
  unfold writeCacheThenLog
  exact writeCacheThenLogFootprint.preserves flagRef (by rintro (h | ⟨_, h⟩) <;> cases h)


-- @@ L1191-1196 verbatim
/-- Reads have a separate result-dependence footprint: reading `cacheRef`
depends only on the cache cell. -/
example {h₁ h₂ : Heap DemoCell}
    (hsame : CellRef.SameOn ({DemoCell.cache} : Set DemoCell) h₁ h₂) :
    (cacheRef.read.run h₁).1 = (cacheRef.read.run h₂).1 :=
  CellRef.resultDependsOnly_read cacheRef h₁ h₂ hsame


-- @@ L1198-1201 verbatim
/-- As a corollary, `flagRef` is preserved by `cacheAndLogStep`. -/
theorem cacheAndLogStep_preserves_flag :
    CellRef.Preserves cacheAndLogStep flagRef :=
  cacheAndLogStep_writesOnly flagRef (by simp)


-- @@ L1203-1205 verbatim
example (h : Heap DemoCell) :
    flagRef.get (cacheAndLogStep.run h).2 = flagRef.get h :=
  cacheAndLogStep_preserves_flag h


-- @@ L1207-1210 verbatim
example :
    flagRef.get (cacheAndLogStep.run (Heap.empty : Heap DemoCell)).2 = false := by
  rw [cacheAndLogStep_preserves_flag]
  rfl


-- @@ L1212-1212 verbatim
end CellRefExample


-- @@ L1214-1214 verbatim
end VCVio.StateSeparating
