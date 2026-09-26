/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.Algebra.Group.Indicator


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
namespace Set


-- @@ L24-24 verbatim
variable {α R : Type*} [One R] [Zero R] (A : Set α)


-- @@ L26-27 verbatim
/-- A polymorphic indicator function `𝟙_A` which is `1` on `A` and `0` outside. -/
noncomputable def indicatorOne : α → R := indicator A (fun _ ↦ 1)


-- @@ L29-29 verbatim
scoped notation "𝟙_" A:max => indicatorOne A


-- @@ L31-31 verbatim
end Set
