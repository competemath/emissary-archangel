/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldWeight
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderRecursiveAdmissibility
public import LeanPool.NavierStokesAndEuler.Euler.PacketTimeProfiles


-- @@ L13-14 verbatim
/-! Time-endpoint equality transports the actual path norm and its profile without changing any
bound. -/


-- @@ L16-16 verbatim
@[expose] public section



-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
namespace EulerPacketCylinderField


-- @@ L23-23 verbatim
open Set EulerPacketProfileRecursion EulerPacketTimeProfile


-- @@ L25-27 verbatim
/-- Time profile change, given by `h ▸ g`. -/
def timeProfileChange {T T' : ℝ} (g : C(Icc (0 : ℝ) T, ℝ)) (h : T = T') :
    C(Icc (0 : ℝ) T',ℝ) := h ▸ g


-- @@ L29-32 verbatim
theorem timeProfileChange_pos {T T' : ℝ} (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t)
    (h : T = T') (t : Icc (0 : ℝ) T') : 0 < timeProfileChange g h t := by
  subst T'
  exact hg t


-- @@ L34-37 verbatim
@[simp] theorem timeProfileChange_roundtrip {T T' : ℝ} (g : C(Icc (0 : ℝ) T, ℝ)) (h : T = T') :
    timeProfileChange (timeProfileChange g h) h.symm = g := by
  subst T'
  rfl


-- @@ L39-39 verbatim
namespace Field


-- @@ L41-42 verbatim
variable {P T T' : ℝ} [Fact (0 < P)] {raw : VectorField} {G : Field P T raw}
  {q d : ℕ} {R A : ℝ}


-- @@ L44-47 verbatim
theorem WordBound.changeTime (hG : G.WordBound q R A d) (h : T = T') :
    (G.changeTime h).WordBound q R A d := by
  subst T'
  exact hG


-- @@ L49-55 verbatim
theorem WordBound.normalized_profile_eq {hT : 0 ≤ T}
    {g : C(Icc (0 : ℝ) T, ℝ)} {hg : ∀ t, 0 < g t}
    (hG : (G.normalized hT g hg).WordBound q R A d)
    (g' : C(Icc (0 : ℝ) T, ℝ)) (hg' : ∀ t, 0 < g' t) (he : g = g') :
    (G.normalized hT g' hg').WordBound q R A d := by
  subst g'
  exact hG


-- @@ L57-66 verbatim
theorem WordBound.normalized_changeTime (hT : 0 ≤ T)
    (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t)
    (hG : (G.normalized hT g hg).WordBound q R A d)
    (h : T = T') (hT' : 0 ≤ T')
    (g' : C(Icc (0 : ℝ) T', ℝ)) (hg' : ∀ t, 0 < g' t) (he : timeProfileChange g h = g') :
    ((G.changeTime h).normalized hT' g' hg').WordBound q R A d := by
  subst T'
  change g = g' at he
  subst g'
  exact hG


-- @@ L68-68 verbatim
end Field

-- @@ L69-69 verbatim
end EulerPacketCylinderField


-- @@ L71-71 verbatim
namespace EulerPacketTimeProfile.Scales


-- @@ L73-73 verbatim
open Set EulerPacketCylinderField


-- @@ L75-77 verbatim
/-- Change time, given by `h ▸ S`. -/
def changeTime {T T' : ℝ} (S : Scales (Icc (0 : ℝ) T)) (h : T = T') :
    Scales (Icc (0 : ℝ) T') := h ▸ S


-- @@ L79-82 verbatim
@[simp] theorem high_changeTime {T T' : ℝ} (S : Scales (Icc (0 : ℝ) T)) (h : T = T') (p : ℕ) :
    (S.changeTime h).high p = timeProfileChange (S.high p) h := by
  subst T'
  rfl


-- @@ L84-87 verbatim
@[simp] theorem mean_changeTime {T T' : ℝ} (S : Scales (Icc (0 : ℝ) T)) (h : T = T') (p : ℕ) :
    (S.changeTime h).mean p = timeProfileChange (S.mean p) h := by
  subst T'
  rfl


-- @@ L89-92 verbatim
@[simp] theorem changeTime_roundtrip {T T' : ℝ} (S : Scales (Icc (0 : ℝ) T)) (h : T = T') :
    (S.changeTime h).changeTime h.symm = S := by
  subst T'
  rfl


-- @@ L94-94 verbatim
end EulerPacketTimeProfile.Scales
