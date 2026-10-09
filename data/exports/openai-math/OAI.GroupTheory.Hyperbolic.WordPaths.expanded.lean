import OAI.GroupTheory.Hyperbolic.Presentation


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace Release075

-- @@ L6-8 verbatim
/-! A combinatorial fundamental groupoid of the **un-collapsed** triangle complex.
The quotient imposes only its triangular faces. Tree edges are used for basing,
not mistaken for triangular two-cells in a van Kampen diagram. -/

-- @@ L9-9 verbatim
namespace BlockPresentation

-- @@ L10-10 verbatim
open CategoryTheory


-- @@ L12-12 verbatim
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)


-- @@ L14-15 verbatim
inductive Vertex (d : BlockPresentation I B r) : Type
  | o | v | w


-- @@ L17-20 verbatim
inductive Arrow : d.Vertex → d.Vertex → Type
  | x (e : XEdge (I := I) (r := r)) : Arrow .v .w
  | l (e : d.LEdge) : Arrow .o .v
  | rr (e : d.REdge) : Arrow .o .w


-- @@ L22-22 verbatim
instance vertexQuiver : Quiver d.Vertex := ⟨d.Arrow⟩


-- @@ L24-24 verbatim
abbrev FreePaths := Quiver.FreeGroupoid d.Vertex


-- @@ L26-26 verbatim
def freeVertex (a : d.Vertex) : d.FreePaths := (Quiver.FreeGroupoid.of d.Vertex).obj a


-- @@ L28-29 verbatim
def freeX (e : XEdge (I := I) (r := r)) : d.freeVertex .v ⟶ d.freeVertex .w :=
  (Quiver.FreeGroupoid.of d.Vertex).map (.x e)

-- @@ L30-31 verbatim
def freeL (e : d.LEdge) : d.freeVertex .o ⟶ d.freeVertex .v :=
  (Quiver.FreeGroupoid.of d.Vertex).map (.l e)

-- @@ L32-33 verbatim
def freeR (e : d.REdge) : d.freeVertex .o ⟶ d.freeVertex .w :=
  (Quiver.FreeGroupoid.of d.Vertex).map (.rr e)


-- @@ L35-40 verbatim
inductive FaceRelation : HomRel d.FreePaths
  | triangle (b : B) (i : (d.block b).labels) (u v : Fin r) :
      FaceRelation
        (d.freeL ⟨b,u,((d.block b).coordinates i).1 + (v.val : ZMod (d.block b).s)⟩ ≫
          d.freeX (i.val,u,v))
        (d.freeR ⟨b,v,((d.block b).coordinates i).2 + (u.val : ZMod (d.block b).t)⟩)


-- @@ L42-42 verbatim
abbrev FundamentalGroupoid := CategoryTheory.Quotient d.FaceRelation


-- @@ L44-45 verbatim
def vertex (a : d.Vertex) : d.FundamentalGroupoid :=
  (CategoryTheory.Quotient.functor d.FaceRelation).obj (d.freeVertex a)


-- @@ L47-48 verbatim
def pathX (e : XEdge (I := I) (r := r)) : d.vertex .v ⟶ d.vertex .w :=
  (CategoryTheory.Quotient.functor d.FaceRelation).map (d.freeX e)

-- @@ L49-50 verbatim
def pathL (e : d.LEdge) : d.vertex .o ⟶ d.vertex .v :=
  (CategoryTheory.Quotient.functor d.FaceRelation).map (d.freeL e)

-- @@ L51-52 verbatim
def pathR (e : d.REdge) : d.vertex .o ⟶ d.vertex .w :=
  (CategoryTheory.Quotient.functor d.FaceRelation).map (d.freeR e)


-- @@ L54-59 verbatim
theorem path_triangle (b : B) (i : (d.block b).labels) (u v : Fin r) :
    d.pathL ⟨b,u,((d.block b).coordinates i).1 + (v.val : ZMod (d.block b).s)⟩ ≫
        d.pathX (i.val,u,v) =
      d.pathR ⟨b,v,((d.block b).coordinates i).2 + (u.val : ZMod (d.block b).t)⟩ := by
  have h := CategoryTheory.Quotient.sound d.FaceRelation (FaceRelation.triangle (d := d) b i u v)
  simpa only [Functor.map_comp,pathX,pathL,pathR,vertex] using h


-- @@ L61-62 verbatim
/-- Path-order multiplication is the opposite of Mathlib's End multiplication. -/
abbrev FundamentalGroup := (End (d.vertex .o))ᵐᵒᵖ


-- @@ L64-64 verbatim
def treePathV : d.vertex .o ⟶ d.vertex .v := d.pathL ⟨d.baseBlock,d.baseIndex,0⟩

-- @@ L65-65 verbatim
def treePathW : d.vertex .o ⟶ d.vertex .w := d.pathR ⟨d.baseBlock,d.baseIndex,0⟩


-- @@ L67-70 verbatim
def basedEdge : d.Edge → d.FundamentalGroup
  | .inl e => MulOpposite.op (d.treePathV ≫ d.pathX e ≫ Groupoid.inv d.treePathW)
  | .inr (.inl e) => MulOpposite.op (d.pathL e ≫ Groupoid.inv d.treePathV)
  | .inr (.inr e) => MulOpposite.op (d.pathR e ≫ Groupoid.inv d.treePathW)


-- @@ L72-81 verbatim
theorem based_triangle (b : B) (i : (d.block b).labels) (u v : Fin r) :
    (FreeGroup.lift d.basedEdge) (d.triangleWord b i u v) = 1 := by
  simp only [triangleWord,map_mul,map_inv,FreeGroup.lift_apply_of]
  apply (mul_inv_eq_one (G := d.FundamentalGroup)).mpr
  apply MulOpposite.unop_injective
  change (d.pathL _ ≫ Groupoid.inv d.treePathV) ≫
      (d.treePathV ≫ d.pathX _ ≫ Groupoid.inv d.treePathW) =
    d.pathR _ ≫ Groupoid.inv d.treePathW
  simp only [Category.assoc,Groupoid.inv_eq_inv,IsIso.inv_hom_id_assoc]
  rw [← Category.assoc,d.path_triangle]


-- @@ L83-86 verbatim
theorem based_treeL : d.basedEdge d.treeL = 1 := by
  apply MulOpposite.unop_injective
  change d.treePathV ≫ Groupoid.inv d.treePathV = 𝟙 _
  simp


-- @@ L88-91 verbatim
theorem based_treeR : d.basedEdge d.treeR = 1 := by
  apply MulOpposite.unop_injective
  change d.treePathW ≫ Groupoid.inv d.treePathW = 𝟙 _
  simp


-- @@ L93-98 verbatim
def toFundamentalGroup : d.GroupType →* d.FundamentalGroup :=
  PresentedGroup.toGroup (f := d.basedEdge) (fun w hw => by
    rcases hw with ⟨b,i,u,v,rfl⟩ | rfl | rfl
    · exact d.based_triangle b i u v
    · simpa only [FreeGroup.lift_apply_of] using d.based_treeL
    · simpa only [FreeGroup.lift_apply_of] using d.based_treeR)


-- @@ L100-101 verbatim
@[simp] theorem toFundamentalGroup_edge (e : d.Edge) :
    d.toFundamentalGroup (d.edge e) = d.basedEdge e := PresentedGroup.toGroup.of _


-- @@ L103-109 verbatim
/-- Evaluation in the displayed group presentation, before quotienting faces. -/
def edgeEvaluation : d.Vertex ⥤q SingleObj d.GroupTypeᵐᵒᵖ where
  obj _ := SingleObj.star _
  map f := match f with
    | .x e => MulOpposite.op (d.edge (.inl e))
    | .l e => MulOpposite.op (d.edge (.inr (.inl e)))
    | .rr e => MulOpposite.op (d.edge (.inr (.inr e)))


-- @@ L111-112 verbatim
def freeEvaluation : d.FreePaths ⥤ SingleObj d.GroupTypeᵐᵒᵖ :=
  Quiver.FreeGroupoid.lift d.edgeEvaluation


-- @@ L114-117 verbatim
@[simp] theorem freeEvaluation_generator {a c : d.Vertex} (e : a ⟶ c) :
    d.freeEvaluation.map ((Quiver.FreeGroupoid.of d.Vertex).map e) =
      d.edgeEvaluation.map e := by
  exact Prefunctor.congr_hom (Quiver.FreeGroupoid.lift_spec d.edgeEvaluation) e


-- @@ L119-127 verbatim
def evaluation : d.FundamentalGroupoid ⥤ SingleObj d.GroupTypeᵐᵒᵖ :=
  CategoryTheory.Quotient.lift d.FaceRelation d.freeEvaluation (by
    intro a c f g h
    cases h with
    | triangle b i u v =>
      simp only [freeL,freeX,freeR]
      apply MulOpposite.unop_injective
      change d.l b u _ * d.x i u v = d.rr b v _
      exact (eq_inv_mul_iff_mul_eq).mp (d.triangle_relation b i u v))


-- @@ L129-132 verbatim
@[simp] theorem evaluation_pathX (e : XEdge (I := I) (r := r)) :
    d.evaluation.map (d.pathX e) = MulOpposite.op (d.edge (.inl e)) := by
  change d.freeEvaluation.map ((Quiver.FreeGroupoid.of d.Vertex).map (.x e)) = _
  exact d.freeEvaluation_generator (.x e)


-- @@ L134-137 verbatim
@[simp] theorem evaluation_pathL (e : d.LEdge) :
    d.evaluation.map (d.pathL e) = MulOpposite.op (d.edge (.inr (.inl e))) := by
  change d.freeEvaluation.map ((Quiver.FreeGroupoid.of d.Vertex).map (.l e)) = _
  exact d.freeEvaluation_generator (.l e)


-- @@ L139-142 verbatim
@[simp] theorem evaluation_pathR (e : d.REdge) :
    d.evaluation.map (d.pathR e) = MulOpposite.op (d.edge (.inr (.inr e))) := by
  change d.freeEvaluation.map ((Quiver.FreeGroupoid.of d.Vertex).map (.rr e)) = _
  exact d.freeEvaluation_generator (.rr e)


-- @@ L144-153 verbatim
def fromFundamentalGroup : d.FundamentalGroup →* d.GroupType where
  toFun g := MulOpposite.unop (d.evaluation.map (MulOpposite.unop g))
  map_one' := by
    change MulOpposite.unop (d.evaluation.map (𝟙 _)) = 1
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_mul' g h := by
    change MulOpposite.unop (d.evaluation.map (MulOpposite.unop g ≫ MulOpposite.unop h)) = _
    rw [Functor.map_comp]
    rfl


-- @@ L155-172 verbatim
@[simp] theorem fromFundamentalGroup_basedEdge (e : d.Edge) :
    d.fromFundamentalGroup (d.basedEdge e) = d.edge e := by
  rcases e with e | e | e
  all_goals
    simp only [fromFundamentalGroup,basedEdge,MonoidHom.coe_mk,OneHom.coe_mk,
      MulOpposite.unop_op,Functor.map_comp,Groupoid.inv_eq_inv,Functor.map_inv]
  all_goals
    simp only [treePathV,treePathW,evaluation_pathX,evaluation_pathL,evaluation_pathR,
      SingleObj.comp_as_mul,SingleObj.inv_as_inv]
  · change d.edge d.treeL * (d.edge (.inl e) * (d.edge d.treeR)⁻¹) = _
    rw [d.treeL_eq_one,d.treeR_eq_one]
    simp
  · change d.edge (.inr (.inl e)) * (d.edge d.treeL)⁻¹ = _
    rw [d.treeL_eq_one]
    simp
  · change d.edge (.inr (.inr e)) * (d.edge d.treeR)⁻¹ = _
    rw [d.treeR_eq_one]
    simp


-- @@ L174-179 verbatim
theorem from_to_fundamental : d.fromFundamentalGroup.comp d.toFundamentalGroup =
    MonoidHom.id d.GroupType := by
  apply PresentedGroup.ext
  intro e
  change d.fromFundamentalGroup (d.toFundamentalGroup (d.edge e)) = d.edge e
  rw [d.toFundamentalGroup_edge,d.fromFundamentalGroup_basedEdge]


-- @@ L181-186 verbatim
theorem toFundamentalGroup_injective : Function.Injective d.toFundamentalGroup := by
  intro a b h
  have h' := congrArg d.fromFundamentalGroup h
  have hi (g : d.GroupType) : d.fromFundamentalGroup (d.toFundamentalGroup g) = g :=
    DFunLike.congr_fun d.from_to_fundamental g
  simpa only [hi] using h'


-- @@ L188-190 verbatim
/-! A finite, purely combinatorial nullhomotopy follows from equality in the actual
fundamental groupoid. This is the starting point for the planar reduction,
not an assumed existence of a reduced diagram. -/

-- @@ L191-191 verbatim
abbrev RawPaths := CategoryTheory.Paths (Quiver.Symmetrify d.Vertex)


-- @@ L193-193 verbatim
def rawVertex (a : d.Vertex) : d.RawPaths := (CategoryTheory.Paths.of _).obj a


-- @@ L195-196 verbatim
def rawX (e : XEdge (I := I) (r := r)) : d.rawVertex .v ⟶ d.rawVertex .w :=
  @Quiver.Hom.toPosPath d.Vertex inferInstance .v .w (.x e)

-- @@ L197-198 verbatim
def rawL (e : d.LEdge) : d.rawVertex .o ⟶ d.rawVertex .v :=
  @Quiver.Hom.toPosPath d.Vertex inferInstance .o .v (.l e)

-- @@ L199-200 verbatim
def rawR (e : d.REdge) : d.rawVertex .o ⟶ d.rawVertex .w :=
  @Quiver.Hom.toPosPath d.Vertex inferInstance .o .w (.rr e)


-- @@ L202-209 verbatim
inductive RawMove : HomRel d.RawPaths
  | backtrack {a c : d.RawPaths} {p q : a ⟶ c} :
      Quiver.FreeGroupoid.redStep p q → RawMove p q
  | triangle (b : B) (i : (d.block b).labels) (u v : Fin r) :
      RawMove
        (d.rawL ⟨b,u,((d.block b).coordinates i).1 + (v.val : ZMod (d.block b).s)⟩ ≫
          d.rawX (i.val,u,v))
        (d.rawR ⟨b,v,((d.block b).coordinates i).2 + (u.val : ZMod (d.block b).t)⟩)


-- @@ L211-212 verbatim
def RawHomotopic {a c : d.RawPaths} (p q : a ⟶ c) : Prop :=
  Relation.EqvGen (@HomRel.CompClosure _ _ d.RawMove a c) p q


-- @@ L214-214 verbatim
abbrev RawQuotient := CategoryTheory.Quotient d.RawMove


-- @@ L216-220 verbatim
def freeToRawQuotient : d.FreePaths ⥤ d.RawQuotient :=
  CategoryTheory.Quotient.lift Quiver.FreeGroupoid.redStep
    (CategoryTheory.Quotient.functor d.RawMove) (by
      intro a c p q h
      exact CategoryTheory.Quotient.sound d.RawMove (RawMove.backtrack h))


-- @@ L222-229 verbatim
def fundamentalToRawQuotient : d.FundamentalGroupoid ⥤ d.RawQuotient :=
  CategoryTheory.Quotient.lift d.FaceRelation d.freeToRawQuotient (by
    intro a c p q h
    cases h with
    | triangle b i u v =>
      change (CategoryTheory.Quotient.functor d.RawMove).map
          (d.rawL _ ≫ d.rawX _) = (CategoryTheory.Quotient.functor d.RawMove).map (d.rawR _)
      exact CategoryTheory.Quotient.sound d.RawMove (RawMove.triangle b i u v))


-- @@ L231-233 verbatim
def rawToFundamental : d.RawPaths ⥤ d.FundamentalGroupoid :=
  CategoryTheory.Quotient.functor Quiver.FreeGroupoid.redStep ⋙
    CategoryTheory.Quotient.functor d.FaceRelation


-- @@ L235-242 verbatim
theorem rawMove_sound {a c : d.RawPaths} {p q : a ⟶ c} (h : d.RawMove p q) :
    d.rawToFundamental.map p = d.rawToFundamental.map q := by
  cases h with
  | backtrack h =>
    exact congrArg ((CategoryTheory.Quotient.functor d.FaceRelation).map)
      (CategoryTheory.Quotient.sound Quiver.FreeGroupoid.redStep h)
  | triangle b i u v =>
    exact CategoryTheory.Quotient.sound d.FaceRelation (FaceRelation.triangle b i u v)


-- @@ L244-245 verbatim
def rawQuotientToFundamental : d.RawQuotient ⥤ d.FundamentalGroupoid :=
  CategoryTheory.Quotient.lift d.RawMove d.rawToFundamental (fun _ _ _ _ h => d.rawMove_sound h)


-- @@ L247-260 verbatim
/-- Equality in the two-stage groupoid quotient is **exactly** a finite chain of
triangle moves and backtrack moves in arbitrary typed path contexts. -/
theorem raw_equality_iff {a c : d.RawPaths} (p q : a ⟶ c) :
    d.rawToFundamental.map p = d.rawToFundamental.map q ↔ d.RawHomotopic p q := by
  constructor
  · intro h
    have hh := congrArg (d.fundamentalToRawQuotient.map) h
    change (CategoryTheory.Quotient.functor d.RawMove).map p =
      (CategoryTheory.Quotient.functor d.RawMove).map q at hh
    exact Quot.eq.mp hh
  · intro h
    have hh : (CategoryTheory.Quotient.functor d.RawMove).map p =
        (CategoryTheory.Quotient.functor d.RawMove).map q := Quot.eq.mpr h
    exact congrArg (d.rawQuotientToFundamental.map) hh


-- @@ L262-264 verbatim
def rawRectangle (i : I) (u u' v v' : Fin r) : d.rawVertex .v ⟶ d.rawVertex .v :=
  d.rawX (i,u,v) ≫ Quiver.Path.reverse (d.rawX (i,u',v)) ≫
    d.rawX (i,u',v') ≫ Quiver.Path.reverse (d.rawX (i,u,v'))


-- @@ L266-267 verbatim
@[simp] theorem rawToFundamental_X (e : XEdge (I := I) (r := r)) :
    d.rawToFundamental.map (d.rawX e) = d.pathX e := rfl


-- @@ L269-271 verbatim
@[simp] theorem rawToFundamental_reverse {a c : d.RawPaths} (p : a ⟶ c) :
    d.rawToFundamental.map (Quiver.Path.reverse p) =
      Groupoid.inv (d.rawToFundamental.map p) := rfl


-- @@ L273-283 verbatim
private theorem based_rectangle_formula {C : Type*} [Groupoid C] {a b c : C}
    (A : a ⟶ b) (B : a ⟶ c) (f g h k : b ⟶ c) :
    (MulOpposite.op (End.of (A ≫ f ≫ Groupoid.inv B)) : (End a)ᵐᵒᵖ) *
        (MulOpposite.op (End.of (A ≫ g ≫ Groupoid.inv B)))⁻¹ *
        MulOpposite.op (End.of (A ≫ h ≫ Groupoid.inv B)) *
        (MulOpposite.op (End.of (A ≫ k ≫ Groupoid.inv B)))⁻¹ =
      MulOpposite.op (End.of (A ≫ (f ≫ Groupoid.inv g ≫ h ≫ Groupoid.inv k) ≫ Groupoid.inv A)) := by
  apply MulOpposite.unop_injective
  change (((A ≫ f ≫ Groupoid.inv B) ≫ Groupoid.inv (A ≫ g ≫ Groupoid.inv B)) ≫
    (A ≫ h ≫ Groupoid.inv B)) ≫ Groupoid.inv (A ≫ k ≫ Groupoid.inv B) = _
  simp [Groupoid.inv_eq_inv,Category.assoc]


-- @@ L285-304 verbatim
/-- If a rectangular word vanished in the actual presentation, the unbased
four-edge rectangle would have a finite triangle/backtrack nullhomotopy. -/
theorem rawRectangle_nullhomotopic_of_eq_one (i : I) (u u' v v' : Fin r)
    (h : d.x i u v * (d.x i u' v)⁻¹ * d.x i u' v' * (d.x i u v')⁻¹ = 1) :
    d.RawHomotopic (d.rawRectangle i u u' v v') (𝟙 _) := by
  have hh := congrArg d.toFundamentalGroup h
  simp only [map_mul,map_inv,map_one,x,toFundamentalGroup_edge,basedEdge] at hh
  rw [based_rectangle_formula] at hh
  have hu := congrArg MulOpposite.unop hh
  change d.treePathV ≫
      (d.pathX (i,u,v) ≫ Groupoid.inv (d.pathX (i,u',v)) ≫
        d.pathX (i,u',v') ≫ Groupoid.inv (d.pathX (i,u,v'))) ≫
      Groupoid.inv d.treePathV = 𝟙 _ at hu
  apply (d.raw_equality_iff _ _).mp
  simp only [rawRectangle,Functor.map_comp,rawToFundamental_X,rawToFundamental_reverse,
    CategoryTheory.Functor.map_id]
  change d.pathX (i,u,v) ≫ Groupoid.inv (d.pathX (i,u',v)) ≫
    d.pathX (i,u',v') ≫ Groupoid.inv (d.pathX (i,u,v')) = 𝟙 (d.vertex .v)
  have hc := congrArg (fun f => Groupoid.inv d.treePathV ≫ f ≫ d.treePathV) hu
  simpa [Groupoid.inv_eq_inv,Category.assoc] using hc


-- @@ L306-306 verbatim
end BlockPresentation

-- @@ L307-307 verbatim
end Release075


-- @@ L309-309 verbatim
end OAI
