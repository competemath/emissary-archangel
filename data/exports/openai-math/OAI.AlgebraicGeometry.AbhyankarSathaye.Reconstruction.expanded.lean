import OAI.AlgebraicGeometry.AbhyankarSathaye.LiftingIdentities


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-10 verbatim
/-!
# Mutually inverse polynomial formulas

The parameter `T = α * U + β * (V + U * W)` and the formulas `inverseU`,
`inverseV`, and `inverseW` reconstruct each other over arbitrary commutative rings.
-/


-- @@ L12-12 verbatim
namespace AbhyankarSathaye

-- @@ L13-13 verbatim
section

-- @@ L14-14 verbatim
variable {B : Type*} [CommRing B]


-- @@ L16-16 verbatim
def inverseU (h x β T : B) : B := h*T-β*x

-- @@ L17-17 verbatim
def inverseG (x y α T : B) : B := y*T+α*x

-- @@ L18-19 verbatim
def inverseW (h y s α β U G : B) : B :=
  α*(1+β*y)*(y+U^2)+β^2*(s-h*G^2+2*U*y*G)

-- @@ L20-20 verbatim
def inverseV (U G W : B) : B := G-U*W

-- @@ L21-21 verbatim
def parameter (α β U V W : B) : B := α*U+β*(V+U*W)


-- @@ L23-39 verbatim
theorem inverse_relations (h x y s α β T : B)
    (hc : x^2+y^3 = h*s) (hb : α*h+β*y = 1) :
    let U := inverseU h x β T
    let G := inverseG x y α T
    let W := inverseW h y s α β U G
    U^3+h*inverseV U G W = x ∧ -U^2+h*W = y ∧ S h U (inverseV U G W) W = s := by
  dsimp only
  have hl := linear_parameter_relation h x y α β T hb
  have hcompat := compatibility h x y s (inverseU h x β T) (inverseG x y α T) hc hl
  have hb2 := squared_bezout h y α β hb
  have hw := solve_h h (y^2) (y+(inverseU h x β T)^2)
    (s-h*(inverseG x y α T)^2+2*(inverseU h x β T)*y*(inverseG x y α T))
    (α*(1+β*y)) (β^2) hcompat hb2
  have hs := solve_c h (y^2) (y+(inverseU h x β T)^2)
    (s-h*(inverseG x y α T)^2+2*(inverseU h x β T)*y*(inverseG x y α T))
    (α*(1+β*y)) (β^2) hcompat hb2
  exact linear_to_original h x y s _ _ _ hl hw hs


-- @@ L41-50 verbatim
theorem inverse_parameter (h x y s α β T : B) (hb : α*h+β*y = 1) :
    let U := inverseU h x β T
    let G := inverseG x y α T
    let W := inverseW h y s α β U G
    parameter α β U (inverseV U G W) W = T := by
  dsimp only [parameter, inverseV]
  have he := linear_parameter_inverse h x y α β T hb
  dsimp [inverseU, inverseG]
  convert he using 1
  ring


-- @@ L52-73 verbatim
theorem original_reconstruction (h x y s α β U V W : B)
    (hb : α*h+β*y = 1) (hx : U^3+h*V = x)
    (hy : -U^2+h*W = y) (hs : S h U V W = s) :
    let T := parameter α β U V W
    let U' := inverseU h x β T
    let G' := inverseG x y α T
    let W' := inverseW h y s α β U' G'
    U' = U ∧ inverseV U' G' W' = V ∧ W' = W := by
  dsimp only
  obtain ⟨hl, hw, hs'⟩ := original_to_linear h x y s U V W hx hy hs
  have hu : inverseU h x β (parameter α β U V W) = U :=
    recover_U h x y α β U (V+U*W) hb hl
  have hg : inverseG x y α (parameter α β U V W) = V+U*W :=
    recover_G h x y α β U (V+U*W) hb hl
  rw [hu, hg]
  have hww : inverseW h y s α β U (V+U*W) = W :=
    (solve_unique h (y^2) (y+U^2) (s-h*(V+U*W)^2+2*U*y*(V+U*W))
      (α*(1+β*y)) (β^2) W (squared_bezout h y α β hb) hw hs').symm
  rw [hww]
  refine ⟨rfl, ?_, rfl⟩
  unfold inverseV
  ring


-- @@ L75-75 verbatim
end


-- @@ L77-77 verbatim
section Maps

-- @@ L78-78 verbatim
variable {B D H : Type*} [CommRing B] [CommRing D]

-- @@ L79-79 verbatim
variable [FunLike H B D] [RingHomClass H B D]


-- @@ L81-82 verbatim
@[simp] theorem map_inverseU (f : H) (h x β T : B) :
    f (inverseU h x β T) = inverseU (f h) (f x) (f β) (f T) := by simp [inverseU]

-- @@ L83-84 verbatim
@[simp] theorem map_inverseG (f : H) (x y α T : B) :
    f (inverseG x y α T) = inverseG (f x) (f y) (f α) (f T) := by simp [inverseG]

-- @@ L85-87 verbatim
@[simp] theorem map_inverseW (f : H) (h y s α β U G : B) :
    f (inverseW h y s α β U G) =
      inverseW (f h) (f y) (f s) (f α) (f β) (f U) (f G) := by simp [inverseW, map_ofNat]

-- @@ L88-89 verbatim
@[simp] theorem map_inverseV (f : H) (U G W : B) :
    f (inverseV U G W) = inverseV (f U) (f G) (f W) := by simp [inverseV]

-- @@ L90-92 verbatim
@[simp] theorem map_parameter (f : H) (α β U V W : B) :
    f (parameter α β U V W) = parameter (f α) (f β) (f U) (f V) (f W) := by
  simp [parameter]


-- @@ L94-94 verbatim
end Maps

-- @@ L95-95 verbatim
end AbhyankarSathaye


-- @@ L97-97 verbatim
end OAI
