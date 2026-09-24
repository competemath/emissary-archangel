module

public import Mathlib.Tactic.TypeStar
public import Mathlib.Data.Nat.Basic


-- @@ L6-8 verbatim
/-!
# Supplemental notation classes
-/


-- @@ L10-10 verbatim
@[expose] public section


-- @@ L12-12 verbatim
namespace FFL


-- @@ L14-14 verbatim
/-! ## Heterogeneous notation classes -/


-- @@ L16-17 verbatim
class HTilde (α : Type*) (β : outParam Type*) where
  hTilde : α → β


-- @@ L19-19 verbatim
prefix:75 "∼" => HTilde.hTilde

-- @@ L20-20 verbatim
macro_rules | `(∼$x) => `(unop% HTilde.hTilde $x)


-- @@ L22-23 verbatim
class HArrow (α β : Type*) (γ : outParam Type*) where
  hArrow : α → β → γ


-- @@ L25-25 verbatim
infixr:60 " 🡒 " => HArrow.hArrow

-- @@ L26-26 verbatim
macro_rules | `($x 🡒 $y) => `(binop% HArrow.hArrow $x $y)


-- @@ L28-29 verbatim
class HWedge (α β : Type*) (γ : outParam Type*) where
  hWedge : α → β → γ


-- @@ L31-31 verbatim
infixr:69 " ⋏ " => HWedge.hWedge

-- @@ L32-32 verbatim
macro_rules | `($x ⋏ $y) => `(binop% HWedge.hWedge $x $y)


-- @@ L34-35 verbatim
class HVee (α β : Type*) (γ : outParam Type*) where
  hVee : α → β → γ


-- @@ L37-37 verbatim
infixr:68 " ⋎ " => HVee.hVee

-- @@ L38-38 verbatim
macro_rules | `($x ⋎ $y) => `(binop% HVee.hVee $x $y)


-- @@ L40-44 verbatim
attribute [match_pattern]
  HTilde.hTilde
  HArrow.hArrow
  HWedge.hWedge
  HVee.hVee


-- @@ L46-46 verbatim
/-! ## Homogeneous notation classes -/


-- @@ L48-49 verbatim
class Tilde (α : Type*) where
  tilde : α → α


-- @@ L51-52 verbatim
class Arrow (α : Type*) where
  arrow : α → α → α


-- @@ L54-55 verbatim
class Wedge (α : Type*) where
  wedge : α → α → α


-- @@ L57-58 verbatim
class Vee (α : Type*) where
  vee : α → α → α


-- @@ L60-64 verbatim
attribute [match_pattern]
  Tilde.tilde
  Arrow.arrow
  Wedge.wedge
  Vee.vee


-- @@ L66-67 verbatim
@[default_instance]
instance Tilde.instHTilde [Tilde α] : HTilde α α := ⟨Tilde.tilde⟩


-- @@ L69-70 verbatim
@[default_instance]
instance Arrow.instHArrow [Arrow α] : HArrow α α α := ⟨Arrow.arrow⟩


-- @@ L72-73 verbatim
@[default_instance]
instance Wedge.instHWedge [Wedge α] : HWedge α α α := ⟨Wedge.wedge⟩


-- @@ L75-76 verbatim
@[default_instance]
instance Vee.instHVee [Vee α] : HVee α α α := ⟨Vee.vee⟩


-- @@ L78-79 verbatim
class Box (α : Type*) where
  box : α → α


-- @@ L81-81 verbatim
prefix:76 "□" => Box.box


-- @@ L83-84 verbatim
class Dia (α : Type*) where
  dia : α → α


-- @@ L86-86 verbatim
prefix:76 "◇" => Dia.dia


-- @@ L88-89 verbatim
class Rhd (α : Type*) where
  rhd : α → α → α


-- @@ L91-91 verbatim
infixl:70 " ▷ " => Rhd.rhd


-- @@ L93-96 verbatim
attribute [match_pattern]
  Box.box
  Dia.dia
  Rhd.rhd


-- @@ L98-99 verbatim
class Exp (α : Type*) where
  exp : α → α


-- @@ L101-102 verbatim
class Superexp (α : Type*) where
  superexp : α → α


-- @@ L104-105 verbatim
class Smash (α : Type*) where
  smash : α → α → α


-- @@ L107-107 verbatim
infix:80 " ⨳ " => Smash.smash


-- @@ L109-110 verbatim
class Length (α : Type*) where
  length : α → α


-- @@ L112-112 verbatim
notation "‖" x "‖" => Length.length x


-- @@ L114-116 verbatim
/-- Coding objects into syntactic objects (e.g. natural numbers, first-order terms) -/
class GödelQuote (α β : Sort*) where
  quote : α → β


-- @@ L118-118 verbatim
notation:max "⌜" x "⌝" => GödelQuote.quote x


-- @@ L120-121 verbatim
class SigmaSymbol (α : Type*) where
  sigma : α


-- @@ L123-124 verbatim
class PiSymbol (α : Type*) where
  pi : α


-- @@ L126-127 verbatim
class DeltaSymbol (α : Type*) where
  delta : α


-- @@ L129-129 verbatim
notation "𝚺" => SigmaSymbol.sigma


-- @@ L131-131 verbatim
notation "𝚷" => PiSymbol.pi


-- @@ L133-133 verbatim
notation "𝚫" => DeltaSymbol.delta


-- @@ L135-135 verbatim
attribute [match_pattern] SigmaSymbol.sigma PiSymbol.pi DeltaSymbol.delta


-- @@ L137-137 verbatim
end FFL


-- @@ L139-139 verbatim
end
