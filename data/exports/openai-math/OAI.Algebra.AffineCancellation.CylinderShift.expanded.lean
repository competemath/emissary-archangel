import OAI.Algebra.AffineCancellation.Model


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
/-! Polynomial stabilization without division by the distinguished coordinate. -/

-- @@ L8-8 verbatim
namespace ComplexCancellation.Cylinder


-- @@ L10-10 verbatim
variable {R : Type*} [CommRing R]


-- @@ L12-17 verbatim
@[ext] structure Point (R : Type*) where
  p : R
  s : R
  u : R
  f : R
  j : R


-- @@ L19-19 verbatim
namespace Point


-- @@ L21-21 verbatim
def x (q : Point R) : R := q.s ^ 2 + q.u ^ 3 + q.p ^ 2 * q.f

-- @@ L22-23 verbatim
def equation (q : Point R) : R :=
  q.x ^ 2 * q.f - (1 + 2 * q.s * q.x) * q.j - q.p ^ 2 * q.j ^ 2 - q.p * q.u


-- @@ L25-25 verbatim
def cubicDiff (p u w : R) : R := -3 * u ^ 2 * w + 3 * u * p ^ 2 * w ^ 2 - p ^ 4 * w ^ 3


-- @@ L27-30 verbatim
lemma cubicDiff_spec (p u w : R) :
    (u - p ^ 2 * w) ^ 3 = u ^ 3 + p ^ 2 * cubicDiff p u w := by
  unfold cubicDiff
  ring


-- @@ L32-35 verbatim
lemma cubicDiff_add (p u w z : R) :
    cubicDiff p u w + cubicDiff p (u - p ^ 2 * w) z = cubicDiff p u (w + z) := by
  unfold cubicDiff
  ring


-- @@ L37-42 verbatim
/-- A finite exponential shift fixing `p`, `x`, `y`, `z` and translating `u` by `-p²w`. -/
def shift (q : Point R) (w : R) : Point R :=
  let k := cubicDiff q.p q.u w
  ⟨q.p, q.s + q.p ^ 2 * q.x * k, q.u - q.p ^ 2 * w,
    q.f - (2 * q.s * q.x + 1) * k - q.p ^ 2 * q.x ^ 2 * k ^ 2,
    q.j - q.x ^ 2 * k⟩


-- @@ L44-44 verbatim
@[simp] lemma shift_p (q : Point R) (w : R) : (q.shift w).p = q.p := rfl

-- @@ L45-45 verbatim
@[simp] lemma shift_u (q : Point R) (w : R) : (q.shift w).u = q.u - q.p ^ 2 * w := rfl


-- @@ L47-55 verbatim
@[simp] lemma shift_x (q : Point R) (w : R) : (q.shift w).x = q.x := by
  change (q.s + q.p ^ 2 * q.x * cubicDiff q.p q.u w) ^ 2 +
    (q.u - q.p ^ 2 * w) ^ 3 + q.p ^ 2 *
    (q.f - (2 * q.s * q.x + 1) * cubicDiff q.p q.u w -
      q.p ^ 2 * q.x ^ 2 * cubicDiff q.p q.u w ^ 2) = q.x
  rw [cubicDiff_spec]
  calc
    _ = q.s ^ 2 + q.u ^ 3 + q.p ^ 2 * q.f := by ring
    _ = q.x := rfl


-- @@ L57-59 verbatim
@[simp] lemma shift_zero (q : Point R) : q.shift 0 = q := by
  cases q
  simp [shift, cubicDiff]


-- @@ L61-89 verbatim
lemma shift_add (q : Point R) (w z : R) : (q.shift w).shift z = q.shift (w + z) := by
  have hk := cubicDiff_add q.p q.u w z
  have hx := shift_x q w
  apply Point.ext
  · rfl
  · change (q.s + q.p ^ 2 * q.x * cubicDiff q.p q.u w) +
      q.p ^ 2 * (q.shift w).x * cubicDiff q.p (q.u - q.p ^ 2 * w) z = _
    rw [hx]
    change _ = q.s + q.p ^ 2 * q.x * cubicDiff q.p q.u (w + z)
    rw [← hk]
    ring
  · change q.u - q.p ^ 2 * w - q.p ^ 2 * z = q.u - q.p ^ 2 * (w + z)
    ring
  · change q.f - (2 * q.s * q.x + 1) * cubicDiff q.p q.u w -
      q.p ^ 2 * q.x ^ 2 * cubicDiff q.p q.u w ^ 2 -
      (2 * (q.s + q.p ^ 2 * q.x * cubicDiff q.p q.u w) * (q.shift w).x + 1) *
        cubicDiff q.p (q.u - q.p ^ 2 * w) z -
      q.p ^ 2 * (q.shift w).x ^ 2 * cubicDiff q.p (q.u - q.p ^ 2 * w) z ^ 2 = _
    rw [hx]
    change _ = q.f - (2 * q.s * q.x + 1) * cubicDiff q.p q.u (w + z) -
      q.p ^ 2 * q.x ^ 2 * cubicDiff q.p q.u (w + z) ^ 2
    rw [← hk]
    ring
  · change q.j - q.x ^ 2 * cubicDiff q.p q.u w -
      (q.shift w).x ^ 2 * cubicDiff q.p (q.u - q.p ^ 2 * w) z = _
    rw [hx]
    change _ = q.j - q.x ^ 2 * cubicDiff q.p q.u (w + z)
    rw [← hk]
    ring


-- @@ L91-101 verbatim
lemma shift_equation (q : Point R) (w : R) :
    (q.shift w).equation = q.equation + q.p ^ 3 * w := by
  unfold equation
  rw [shift_x]
  change q.x ^ 2 * (q.f - (2 * q.s * q.x + 1) * cubicDiff q.p q.u w -
      q.p ^ 2 * q.x ^ 2 * cubicDiff q.p q.u w ^ 2) -
    (1 + 2 * (q.s + q.p ^ 2 * q.x * cubicDiff q.p q.u w) * q.x) *
      (q.j - q.x ^ 2 * cubicDiff q.p q.u w) -
    q.p ^ 2 * (q.j - q.x ^ 2 * cubicDiff q.p q.u w) ^ 2 -
    q.p * (q.u - q.p ^ 2 * w) = _
  ring


-- @@ L103-104 verbatim
@[simp] lemma shift_neg_shift (q : Point R) (w : R) : (q.shift w).shift (-w) = q := by
  rw [shift_add, add_neg_cancel, shift_zero]


-- @@ L106-106 verbatim
end Point

-- @@ L107-107 verbatim
end ComplexCancellation.Cylinder


-- @@ L109-109 verbatim
namespace ComplexCancellation.Cylinder

-- @@ L110-110 verbatim
variable {R : Type*} [CommRing R]


-- @@ L112-116 verbatim
@[ext] structure Frame (R : Type*) where
  p : R
  s : R
  u : R
  m : R


-- @@ L118-118 verbatim
namespace Frame


-- @@ L120-120 verbatim
def x₀ (t : Frame R) : R := t.s ^ 2 + t.u ^ 3

-- @@ L121-121 verbatim
def f₁ (t : Frame R) : R := 4 * t.s ^ 2

-- @@ L122-122 verbatim
def f₀ (t : Frame R) : R := (1 + 2 * t.s * t.x₀) * t.m

-- @@ L123-123 verbatim
def j₁ (t : Frame R) : R := 2 * t.s * t.x₀ - 1

-- @@ L124-124 verbatim
def j₀ (t : Frame R) : R := t.x₀ ^ 2 * t.m

-- @@ L125-125 verbatim
def f (t : Frame R) (l : R) : R := t.f₁ * l + t.f₀

-- @@ L126-126 verbatim
def j (t : Frame R) (l : R) : R := t.j₁ * l + t.j₀

-- @@ L127-127 verbatim
def point (t : Frame R) (l : R) : Point R := ⟨t.p, t.s, t.u, t.f l, t.j l⟩

-- @@ L128-129 verbatim
def Q (t : Frame R) (l : R) : R :=
  2 * t.x₀ * t.f l ^ 2 - 2 * t.s * t.f l * t.j l - t.j l ^ 2

-- @@ L130-130 verbatim
def c (t : Frame R) : R := t.Q 0

-- @@ L131-132 verbatim
def q₁ (t : Frame R) : R :=
  4 * t.x₀ * t.f₁ * t.f₀ - 2 * t.s * (t.f₁ * t.j₀ + t.f₀ * t.j₁) - 2 * t.j₁ * t.j₀

-- @@ L133-134 verbatim
def q₂ (t : Frame R) : R :=
  2 * t.x₀ * t.f₁ ^ 2 - 2 * t.s * t.f₁ * t.j₁ - t.j₁ ^ 2

-- @@ L135-135 verbatim
def Q₁ (t : Frame R) (l : R) : R := t.q₁ + t.q₂ * l


-- @@ L137-139 verbatim
lemma Q_expand (t : Frame R) (l : R) : t.Q l = t.c + l * t.Q₁ l := by
  simp only [Q, c, Q₁, q₁, q₂, f, j]
  ring


-- @@ L141-153 verbatim
lemma equation_point (t : Frame R) (l : R) :
    (t.point l).equation = l - t.p * t.u + t.p ^ 2 * t.Q l + t.p ^ 4 * t.f l ^ 3 := by
  have hl : t.x₀ ^ 2 * t.f l - (1 + 2 * t.s * t.x₀) * t.j l = l := by
    unfold f j f₁ f₀ j₁ j₀
    ring
  change (t.s ^ 2 + t.u ^ 3 + t.p ^ 2 * t.f l) ^ 2 * t.f l -
    (1 + 2 * t.s * (t.s ^ 2 + t.u ^ 3 + t.p ^ 2 * t.f l)) * t.j l -
    t.p ^ 2 * t.j l ^ 2 - t.p * t.u = _
  change (t.x₀ + t.p ^ 2 * t.f l) ^ 2 * t.f l -
    (1 + 2 * t.s * (t.x₀ + t.p ^ 2 * t.f l)) * t.j l -
    t.p ^ 2 * t.j l ^ 2 - t.p * t.u = _
  unfold Q
  linear_combination hl


-- @@ L155-155 verbatim
def root (t : Frame R) : R := t.p * t.u - t.p ^ 2 * t.c

-- @@ L156-157 verbatim
def h (t : Frame R) (l w : R) : R :=
  t.u - t.p * t.Q l - t.p ^ 3 * t.f l ^ 3 - t.p ^ 2 * w

-- @@ L158-158 verbatim
def e (t : Frame R) (l w : R) : R := -w - t.p * t.f l ^ 3 - t.Q₁ l * t.h l w


-- @@ L160-160 verbatim
def L (t : Frame R) (z : R) : R := t.root + t.p ^ 3 * z

-- @@ L161-162 verbatim
def W (t : Frame R) (z : R) : R :=
  -z - (t.u - t.p * t.c + t.p ^ 2 * z) * t.Q₁ (t.L z) - t.p * t.f (t.L z) ^ 3


-- @@ L164-170 verbatim
lemma e_certificate (t : Frame R) (l w : R) :
    t.p ^ 3 * t.e l w - (l - t.root) =
    (t.p ^ 2 * t.Q₁ l - 1) * ((t.point l).equation + t.p ^ 3 * w) := by
  rw [equation_point]
  unfold e h root
  rw [Q_expand]
  ring


-- @@ L172-176 verbatim
lemma coordinate_equation (t : Frame R) (z : R) :
    (t.point (t.L z)).equation + t.p ^ 3 * t.W z = 0 := by
  rw [equation_point, Q_expand]
  unfold W L root
  ring


-- @@ L178-183 verbatim
lemma h_coordinates (t : Frame R) (z : R) :
    t.h (t.L z) (t.W z) = t.u - t.p * t.c + t.p ^ 2 * z := by
  unfold h W
  rw [Q_expand]
  unfold L root
  ring


-- @@ L185-189 verbatim
lemma e_coordinates (t : Frame R) (z : R) : t.e (t.L z) (t.W z) = z := by
  unfold e
  rw [h_coordinates]
  unfold W
  ring


-- @@ L191-191 verbatim
end Frame


-- @@ L193-193 verbatim
namespace Point


-- @@ L195-196 verbatim
def frame (q : Point R) : Frame R :=
  ⟨q.p, q.s, q.u, (1 - 2 * q.s * (q.s ^ 2 + q.u ^ 3)) * q.f + 4 * q.s ^ 2 * q.j⟩

-- @@ L197-198 verbatim
def linear (q : Point R) : R :=
  (q.s ^ 2 + q.u ^ 3) ^ 2 * q.f - (1 + 2 * q.s * (q.s ^ 2 + q.u ^ 3)) * q.j


-- @@ L200-212 verbatim
lemma point_frame (q : Point R) : q.frame.point q.linear = q := by
  apply Point.ext
  · rfl
  · rfl
  · rfl
  · change 4 * q.s ^ 2 * q.linear +
      (1 + 2 * q.s * (q.s ^ 2 + q.u ^ 3)) * q.frame.m = q.f
    unfold linear frame
    ring
  · change (2 * q.s * (q.s ^ 2 + q.u ^ 3) - 1) * q.linear +
      (q.s ^ 2 + q.u ^ 3) ^ 2 * q.frame.m = q.j
    unfold linear frame
    ring


-- @@ L214-214 verbatim
end Point

-- @@ L215-215 verbatim
namespace Frame


-- @@ L217-224 verbatim
@[simp] lemma frame_point (t : Frame R) (l : R) : (t.point l).frame = t := by
  apply Frame.ext
  · rfl
  · rfl
  · rfl
  · change (1 - 2 * t.s * t.x₀) * t.f l + 4 * t.s ^ 2 * t.j l = t.m
    unfold f j f₁ f₀ j₁ j₀
    ring


-- @@ L226-229 verbatim
@[simp] lemma linear_point (t : Frame R) (l : R) : (t.point l).linear = l := by
  change t.x₀ ^ 2 * t.f l - (1 + 2 * t.s * t.x₀) * t.j l = l
  unfold f j f₁ f₀ j₁ j₀
  ring


-- @@ L231-231 verbatim
end Frame

-- @@ L232-232 verbatim
end ComplexCancellation.Cylinder


-- @@ L234-234 verbatim
end


-- @@ L236-236 verbatim
end OAI
