import OAI.InformationTheory.BooleanNoise.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section


-- @@ L8-8 verbatim
open scoped BigOperators


-- @@ L10-10 verbatim
namespace LeanBlast.CourtadeKumar


-- @@ L12-12 verbatim
@[simp] theorem xlogx_zero : xlogx 0 = 0 := by simp [xlogx]


-- @@ L14-15 verbatim
@[simp] theorem binaryEntropy_zero : binaryEntropy 0 = 0 := by
  simp [binaryEntropy, xlogx]


-- @@ L17-18 verbatim
@[simp] theorem binaryEntropy_one : binaryEntropy 1 = 0 := by
  simp [binaryEntropy, xlogx]


-- @@ L20-20 verbatim
end LeanBlast.CourtadeKumar


-- @@ L22-22 verbatim
end


-- @@ L24-24 verbatim
end OAI
